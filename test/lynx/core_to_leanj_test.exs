defmodule Lynx.CoreToLeanjTest do
  use ExUnit.Case, async: true

  test "cutoffs retain the signature without traversing the original body" do
    body = :cerl.c_primop(:cerl.c_atom(:unsupported_body), [])
    defs = definitions([definition(:entry, body)])
    {:function, core} = defs[{:entry, 1}]
    defs = Map.put(defs, {:entry, 1}, {:cutoff, core})

    assert {:ok,
            %{
              {:entry, 1} => %{
                purity: :partial,
                local_calls: [],
                translation: %{
                  "kind" => "def",
                  "name" => "entry",
                  "params" => [_],
                  "body" => %{"kind" => "cutoff"}
                }
              }
            }, []} = translate(defs)
  end

  test "writable binary allocation starts with an empty binary" do
    body = :cerl.c_primop(:cerl.c_atom(:bs_init_writable), [:cerl.c_int(256)])

    assert {:ok,
            %{
              {:entry, 1} => %{
                purity: :pure,
                translation: %{
                  "body" => %{
                    "kind" => "return",
                    "values" => [
                      %{"kind" => "bitstring", "bytes" => [], "last_bits" => 0}
                    ]
                  }
                }
              }
            }, []} = translate(definitions([definition(:entry, body)]))
  end

  test "external function literals share a capture-free remote-call wrapper" do
    capture = :cerl.abstract(&:erlang."=<"/2)
    body = :cerl.c_tuple([capture, capture])

    assert {:ok,
            %{
              {:entry, 1} => %{
                translation: %{
                  "body" => %{
                    "values" => [
                      %{
                        "elements" => [
                          %{"kind" => "function", "id" => id, "arity" => 2, "captures" => []},
                          %{"kind" => "function", "id" => id, "arity" => 2, "captures" => []}
                        ]
                      }
                    ]
                  }
                }
              },
              {:"$lynx_fun_0", 2} => %{
                purity: :pure,
                translation: %{
                  "params" => [%{"name" => 0}, %{"name" => 1}],
                  "body" => %{
                    "kind" => "remote_call",
                    "module" => "Erlang.erlang",
                    "name" => "=<",
                    "args" => [%{"name" => 0}, %{"name" => 1}]
                  }
                }
              }
            }, [{:erlang, :"=<", 2, []}]} = translate(definitions([definition(:entry, body)]))
  end

  test "passes captures explicitly through direct local recursion" do
    loop = :cerl.c_fname(:loop, 1)
    input = :cerl.c_var(:input)
    captured = :cerl.c_var(0)
    tail = :cerl.c_var(:tail)

    body =
      :cerl.c_case(input, [
        :cerl.c_clause([:cerl.c_nil()], captured),
        :cerl.c_clause(
          [:cerl.c_cons(:cerl.c_var(:head), tail)],
          :cerl.c_apply(loop, [tail])
        )
      ])

    local =
      :cerl.c_letrec(
        [{loop, :cerl.c_fun([input], body)}],
        :cerl.c_apply(loop, [:cerl.c_nil()])
      )

    assert {:ok,
            %{
              {:entry, 1} => %{
                purity: :pure,
                local_calls: [{:lynx_local_1, 2}],
                translation: %{
                  "body" => %{
                    "kind" => "local_call",
                    "name" => "lynx_local_1",
                    "args" => [%{"kind" => "nil"}, %{"name" => 0}]
                  }
                }
              },
              {:lynx_local_1, 2} => %{
                purity: :pure,
                local_calls: [],
                translation: %{
                  "params" => [%{"name" => "input"}, %{"name" => 0}],
                  "body" => %{
                    "cases" => [
                      _,
                      %{
                        "body" => %{
                          "kind" => "local_call",
                          "name" => "lynx_local_1",
                          "args" => [%{"name" => "tail"}, %{"name" => 0}]
                        }
                      }
                    ]
                  }
                }
              }
            }, []} = translate(definitions([definition(:entry, local)]))
  end

  test "escaping local functions preserve captures, generated arguments, and self identity" do
    loop = :cerl.c_fname(:loop, 1)
    input = :cerl.c_var(:input)
    captured = :cerl.c_var(0)
    call = :cerl.c_call(:cerl.c_atom(:external), :cerl.c_atom(:entry), [captured])

    body =
      :cerl.c_letrec(
        [{loop, :cerl.c_fun([input], :cerl.c_tuple([captured, input, loop]))}],
        :cerl.c_case(call, [:cerl.c_clause([:cerl.c_var(:ignored)], loop)])
      )

    assert {:ok,
            %{
              {:entry, 1} => %{
                translation: %{
                  "body" => %{
                    "body" => %{
                      "cases" => [
                        %{
                          "body" => %{
                            "values" => [
                              %{
                                "kind" => "function",
                                "id" => id,
                                "arity" => 1,
                                "captures" => [%{"name" => 0}]
                              }
                            ]
                          }
                        }
                      ]
                    }
                  }
                }
              },
              {:lynx_local_1, 2} => %{
                translation: %{
                  "body" => %{
                    "values" => [
                      %{
                        "kind" => "tuple",
                        "elements" => [
                          %{"name" => 0},
                          %{"name" => "input"},
                          %{"kind" => "function", "id" => self_id, "captures" => [%{"name" => 0}]}
                        ]
                      }
                    ]
                  }
                }
              },
              {:"$lynx_fun_0", 2} => %{
                translation: %{
                  "params" => [%{"name" => 0}, %{"name" => %{"generated" => 1}}],
                  "body" => %{
                    "kind" => "local_call",
                    "name" => "lynx_local_1",
                    "args" => [%{"name" => %{"generated" => 1}}, %{"name" => 0}]
                  }
                }
              }
            }, [{:external, :entry, 1, []}]} = translate(definitions([definition(:entry, body)]))

    assert id == self_id
  end

  test "resolves native segment endianness on the translating platform" do
    # Keep platform-dependent expectations here rather than in fixture snapshots.
    endian = Atom.to_string(:erlang.system_info(:endian))

    for {type, width} <- [{:integer, 13}, {:float, 64}],
        signed <- [:signed, :unsigned] do
      segment =
        :cerl.c_bitstr(
          :cerl.c_var(0),
          :cerl.c_int(width),
          :cerl.c_int(1),
          :cerl.c_atom(type),
          :cerl.abstract([signed, :native])
        )

      type = Atom.to_string(type)

      assert {:ok,
              %{
                {:entry, 1} => %{
                  translation: %{
                    "body" => %{
                      "kind" => "bitstring_constructor",
                      "segments" => [%{"type" => ^type, "endian" => ^endian}]
                    }
                  }
                }
              }, []} = translate(definitions([definition(:entry, :cerl.c_binary([segment]))]))

      body =
        :cerl.c_case(:cerl.c_var(0), [
          :cerl.c_clause([:cerl.c_binary([segment])], :cerl.c_atom(true))
        ])

      assert {:ok,
              %{
                {:entry, 1} => %{
                  translation: %{
                    "body" => %{
                      "cases" => [
                        %{
                          "patterns" => [
                            %{
                              "kind" => "bitstring_pattern",
                              "segments" => [%{"type" => ^type, "endian" => ^endian}]
                            }
                          ]
                        }
                      ]
                    }
                  }
                }
              }, []} = translate(definitions([definition(:entry, body)]))
    end
  end

  test "translates UTF construction with no size or unit and resolves native endianness" do
    for type <- [:utf8, :utf16, :utf32], endian <- [:big, :little, :native] do
      segment =
        :cerl.c_bitstr(
          :cerl.c_var(0),
          :cerl.c_atom(:undefined),
          :cerl.c_atom(:undefined),
          :cerl.c_atom(type),
          :cerl.abstract([:unsigned, endian])
        )

      type = Atom.to_string(type)

      endian =
        Atom.to_string(if endian == :native, do: :erlang.system_info(:endian), else: endian)

      assert {:ok,
              %{
                {:entry, 1} => %{
                  purity: :pure,
                  translation: %{
                    "body" => %{
                      "kind" => "bitstring_constructor",
                      "segments" => [translated]
                    }
                  }
                }
              }, []} = translate(definitions([definition(:entry, :cerl.c_binary([segment]))]))

      assert %{"type" => ^type, "endian" => ^endian, "value" => %{"kind" => "var"}, "span" => _} =
               translated

      assert map_size(translated) == 4
    end
  end

  test "resolves native UTF pattern endianness on the translating platform" do
    endian = Atom.to_string(:erlang.system_info(:endian))

    for type <- [:utf8, :utf16, :utf32] do
      segment =
        :cerl.c_bitstr(
          :cerl.c_var(1),
          :cerl.c_atom(:undefined),
          :cerl.c_atom(:undefined),
          :cerl.c_atom(type),
          :cerl.abstract([:unsigned, :native])
        )

      body =
        :cerl.c_case(:cerl.c_var(0), [
          :cerl.c_clause([:cerl.c_binary([segment])], :cerl.c_atom(true))
        ])

      type = Atom.to_string(type)

      assert {:ok,
              %{
                {:entry, 1} => %{
                  translation: %{
                    "body" => %{
                      "cases" => [
                        %{
                          "patterns" => [
                            %{
                              "kind" => "bitstring_pattern",
                              "segments" => [%{"type" => ^type, "endian" => ^endian}]
                            }
                          ]
                        }
                      ]
                    }
                  }
                }
              }, []} = translate(definitions([definition(:entry, body)]))
    end
  end

  test "folds native integer literals using the translating platform" do
    for {value, signed} <- [{0x123, :unsigned}, {-2, :signed}] do
      bytes = :binary.bin_to_list(<<value::native-size(12), 0::4>>)

      segment =
        :cerl.c_bitstr(
          :cerl.c_int(value),
          :cerl.c_int(12),
          :cerl.c_int(1),
          :cerl.c_atom(:integer),
          :cerl.abstract([:native, signed])
        )

      body =
        :cerl.c_case(:cerl.c_var(0), [
          :cerl.c_clause([:cerl.c_binary([segment])], :cerl.c_atom(true))
        ])

      assert {:ok,
              %{
                {:entry, 1} => %{
                  translation: %{
                    "body" => %{
                      "cases" => [
                        %{
                          "patterns" => [
                            %{"kind" => "bitstring", "bytes" => ^bytes, "last_bits" => 4}
                          ]
                        }
                      ]
                    }
                  }
                }
              }, []} = translate(definitions([definition(:entry, body)]))
    end
  end

  test "keeps unrepresentable integer patterns and large literals as segment matches" do
    # The compiler removes impossible source clauses; exercise their Core forms directly.
    for {value, size, signed} <- [
          {256, 8, :unsigned},
          {-1, 8, :unsigned},
          {128, 8, :signed},
          {-129, 8, :signed},
          {1, 0, :unsigned},
          {0, 8192, :unsigned}
        ] do
      segment =
        :cerl.c_bitstr(
          :cerl.c_int(value),
          :cerl.c_int(size),
          :cerl.c_int(1),
          :cerl.c_atom(:integer),
          :cerl.abstract([signed, :big])
        )

      body =
        :cerl.c_case(:cerl.c_var(0), [
          :cerl.c_clause([:cerl.c_binary([segment])], :cerl.c_atom(true))
        ])

      assert {:ok,
              %{
                {:entry, 1} => %{
                  translation: %{
                    "body" => %{
                      "cases" => [
                        %{
                          "patterns" => [
                            %{
                              "kind" => "bitstring_pattern",
                              "segments" => [
                                %{
                                  "value" => %{"kind" => "integer", "value" => ^value},
                                  "size" => %{"kind" => "integer", "value" => ^size}
                                }
                              ]
                            }
                          ]
                        }
                      ]
                    }
                  }
                }
              }, []} = translate(definitions([definition(:entry, body)]))
    end
  end

  test "allocates distinct generated message binders for timeout-only receives" do
    receive_after = fn action ->
      loop = :cerl.c_fname(:receive_loop, 0)
      expired = :cerl.c_var(:expired)

      wait =
        :cerl.c_let(
          [expired],
          :cerl.c_primop(:cerl.c_atom(:recv_wait_timeout), [:cerl.c_int(0)]),
          :cerl.c_case(expired, [
            :cerl.c_clause([:cerl.c_atom(true)], action),
            :cerl.c_clause([:cerl.c_atom(false)], :cerl.c_apply(loop, []))
          ])
        )

      :cerl.c_letrec([{loop, :cerl.c_fun([], wait)}], :cerl.c_apply(loop, []))
    end

    body =
      :cerl.c_seq(
        receive_after.(:cerl.c_atom(:ok)),
        receive_after.(:cerl.c_atom(:done))
      )

    assert {:ok, functions, []} = translate(definitions([definition(:entry, body)]))
    assert functions[{:entry, 1}].purity == :concurrent

    assert %{
             "body" => %{
               "kind" => "bind",
               "computation" => %{
                 "kind" => "receive",
                 "message" => %{"name" => %{"generated" => 0}},
                 "cases" => []
               },
               "body" => %{
                 "kind" => "receive",
                 "message" => %{"name" => %{"generated" => 1}},
                 "cases" => []
               }
             }
           } = functions[{:entry, 1}].translation
  end

  test "translates Core values into separate match expressions and patterns" do
    body =
      :cerl.c_case(:cerl.c_values([:cerl.c_var(0), :cerl.c_nil()]), [
        :cerl.c_clause([:cerl.c_tuple([:cerl.c_var(:X)]), :cerl.c_nil()], :cerl.c_var(:X))
      ])

    assert {:ok, functions, []} = translate(definitions([definition(:entry, body)]))

    assert %{
             "body" => %{
               "kind" => "match",
               "expressions" => [
                 %{"kind" => "var", "name" => 0},
                 %{"kind" => "nil"}
               ],
               "cases" => [
                 %{
                   "patterns" => [
                     %{"kind" => "tuple", "elements" => [%{"kind" => "var", "name" => "X"}]},
                     %{"kind" => "nil"}
                   ]
                 }
               ]
             }
           } = functions[{:entry, 1}].translation
  end

  test "names parameters after the variables every clause binds them to" do
    body =
      :cerl.c_case(:cerl.c_values([:cerl.c_var(0), :cerl.c_nil()]), [
        :cerl.c_clause([:cerl.c_var(:Acc), :cerl.c_nil()], :cerl.c_var(:Acc)),
        :cerl.c_clause([:cerl.c_var(2), :cerl.c_var(:Other)], :cerl.c_var(2))
      ])

    assert {:ok, functions, []} = translate(definitions([definition(:entry, body)]))

    assert %{
             "params" => [%{"name" => "Acc"}],
             "body" => %{
               "kind" => "match",
               "expressions" => [%{"kind" => "nil"}],
               "cases" => [
                 %{
                   "patterns" => [%{"kind" => "nil"}],
                   "body" => %{"values" => [%{"name" => "Acc"}]}
                 },
                 %{
                   "patterns" => [%{"kind" => "var", "name" => "Other"}],
                   "body" => %{"values" => [%{"name" => "Acc"}]}
                 }
               ]
             }
           } = functions[{:entry, 1}].translation
  end

  test "translates map construction" do
    key = :cerl.c_var(0)

    body =
      :cerl.c_map([
        :cerl.c_map_pair(key, :cerl.c_int(1)),
        :cerl.c_map_pair(key, :cerl.c_var(0))
      ])

    assert {:ok, functions, []} = translate(definitions([definition(:entry, body)]))
    assert functions[{:entry, 1}].purity == :pure

    assert %{
             "kind" => "return",
             "values" => [%{"kind" => "map", "entries" => [first, last]}]
           } = functions[{:entry, 1}].translation["body"]

    assert last["key"] == first["key"]
    assert last["value"] == %{"kind" => "var", "name" => 0, "span" => []}
    assert first["value"] == %{"kind" => "integer", "value" => 1, "span" => []}
  end

  test "lowers mixed map updates to calls and fresh binds with dependencies" do
    base = :cerl.c_var(0)
    key = :cerl.c_atom(:a)
    assoc = :cerl.ann_c_map_pair([10], :cerl.c_atom(:assoc), key, :cerl.c_int(1))
    exact = :cerl.ann_c_map_pair([11], :cerl.c_atom(:exact), key, :cerl.c_int(2))
    update = :cerl.c_map(base, [assoc, exact, assoc])
    # A surrounding match also allocates a generated variable.
    body = :cerl.c_case(update, [:cerl.c_clause([:cerl.c_var(:result)], :cerl.c_var(:result))])

    assert {:ok, functions, calls} = translate(definitions([definition(:entry, body)]))
    assert functions[{:entry, 1}].purity == :pure
    assert calls == [{:maps, :put, 3, [10]}, {:maps, :update, 3, [11]}, {:maps, :put, 3, [10]}]
    outer = functions[{:entry, 1}].translation["body"]
    first = outer["computation"]
    second = first["body"]
    assert first["kind"] == "bind"
    assert first["computation"]["module"] == "Erlang.maps"
    assert first["computation"]["name"] == "put"

    assert first["computation"]["args"] |> List.last() == %{
             "kind" => "var",
             "name" => 0,
             "span" => []
           }

    assert second["computation"]["name"] == "update"
    assert List.last(second["computation"]["args"]) == hd(first["vars"])
    assert second["body"]["name"] == "put"
    assert List.last(second["body"]["args"]) == hd(second["vars"])

    assert Enum.map(first["vars"] ++ second["vars"] ++ outer["vars"], & &1["name"]) ==
             [%{"generated" => 0}, %{"generated" => 1}, %{"generated" => 2}]

    assert {:ok, impure, _} =
             translate(definitions([definition(:entry, update)]), %{}, %{
               {:maps, :update, 3} => :sequential
             })

    assert impure[{:entry, 1}].purity == :sequential
  end

  test "lowers exact updates even with an empty literal base" do
    pair = :cerl.c_map_pair_exact(:cerl.c_atom(:a), :cerl.c_int(1))
    body = :cerl.c_map(:cerl.abstract(%{}), [pair])

    assert {:ok, functions, [{:maps, :update, 3, []}]} =
             translate(definitions([definition(:entry, body)]))

    call = functions[{:entry, 1}].translation["body"]
    assert call["kind"] == "remote_call"
    assert call["name"] == "update"
    assert List.last(call["args"]) == %{"kind" => "map", "entries" => [], "span" => []}
  end

  test "map pattern keys remain values while nested values remain patterns" do
    literal_key = :cerl.abstract(%{a: 1})

    nested =
      :cerl.c_map_pattern([
        :cerl.c_map_pair_exact(:cerl.c_atom(:b), :cerl.c_var(:value))
      ])

    pat = :cerl.c_map_pattern([:cerl.c_map_pair_exact(literal_key, nested)])

    body =
      :cerl.c_case(:cerl.c_var(0), [
        :cerl.c_clause([pat], :cerl.c_var(:value)),
        :cerl.c_clause([:cerl.c_var(:other)], :cerl.c_atom(:fallback))
      ])

    assert {:ok, functions, []} =
             translate(definitions([definition(:entry, body)]))

    assert %{
             "kind" => "match",
             "cases" => [
               %{
                 "patterns" => [
                   %{
                     "kind" => "map",
                     "entries" => [
                       %{
                         "key" => %{
                           "kind" => "map",
                           "entries" => [
                             %{
                               "key" => %{"kind" => "atom", "value" => "a"},
                               "value" => %{"kind" => "integer", "value" => 1}
                             }
                           ]
                         },
                         "value" => %{
                           "kind" => "map",
                           "entries" => [
                             %{
                               "key" => %{"kind" => "atom", "value" => "b"},
                               "value" => %{"kind" => "var", "name" => "value"}
                             }
                           ]
                         }
                       }
                     ]
                   }
                 ]
               },
               _fallback
             ]
           } = functions[{:entry, 1}].translation["body"]
  end

  test "preserves compiler fallthrough labels and their jump sites" do
    label = :cerl.c_fname(:label, 0)
    fallback = :cerl.c_call(:cerl.c_atom(:other), :cerl.c_atom(:fallback), [])

    guarded =
      :cerl.c_case(:cerl.c_var(0), [
        :cerl.c_clause([:cerl.c_atom(true)], :cerl.c_atom(:matched)),
        :cerl.c_clause([:cerl.c_atom(false)], :cerl.c_apply(label, [])),
        :cerl.c_clause([:cerl.c_var(:other)], :cerl.c_apply(label, []))
      ])

    body = :cerl.ann_c_letrec([:letrec_goto], [{label, :cerl.c_fun([], fallback)}], guarded)

    assert {:ok, functions, [{:other, :fallback, 0, []}]} =
             translate(definitions([definition(:entry, body)]))

    assert %{
             "kind" => "label",
             "label" => "label",
             "continuation" => %{
               "kind" => "remote_call",
               "module" => "Erlang.other",
               "name" => "fallback",
               "args" => []
             },
             "body" => %{
               "kind" => "match",
               "cases" => [
                 %{
                   "body" => %{
                     "kind" => "return",
                     "values" => [%{"kind" => "atom", "value" => "matched"}]
                   }
                 },
                 %{"body" => %{"kind" => "jump", "label" => "label"}},
                 %{"body" => %{"kind" => "jump", "label" => "label"}}
               ]
             }
           } = functions[{:entry, 1}].translation["body"]
  end

  test "preserves nested compiler labels with immediate jumps" do
    outer = :cerl.c_fname(:outer, 0)
    inner = :cerl.c_fname(:inner, 0)

    nested =
      :cerl.ann_c_letrec(
        [:letrec_goto],
        [{inner, :cerl.c_fun([], :cerl.c_apply(outer, []))}],
        :cerl.c_apply(inner, [])
      )

    body =
      :cerl.ann_c_letrec(
        [:letrec_goto],
        [{outer, :cerl.c_fun([], :cerl.c_atom(:fallback))}],
        nested
      )

    assert {:ok, functions, []} = translate(definitions([definition(:entry, body)]))

    assert %{
             local_calls: [],
             translation: %{
               "body" => %{
                 "kind" => "label",
                 "label" => "outer",
                 "continuation" => %{
                   "kind" => "return",
                   "values" => [%{"kind" => "atom", "value" => "fallback"}]
                 },
                 "body" => %{
                   "kind" => "label",
                   "label" => "inner",
                   "continuation" => %{"kind" => "jump", "label" => "outer"},
                   "body" => %{"kind" => "jump", "label" => "inner"}
                 }
               }
             }
           } = functions[{:entry, 1}]
  end

  test "translates zero and multiple Core try values" do
    x = :cerl.c_var(:x)
    a = :cerl.c_var(:a)
    b = :cerl.c_var(:b)
    evars = Enum.map([:class, :reason, :trace], &:cerl.c_var/1)
    empty = :cerl.c_var({:empty, 0})
    pair = :cerl.c_var({:pair, 1})
    bound = :cerl.c_var({:bound, 1})
    empty_bound = :cerl.c_var({:empty_bound, 0})
    matched = :cerl.c_var({:matched, 1})
    returned = :cerl.c_values([x, :cerl.c_atom(:second)])

    protected =
      :cerl.c_try(
        returned,
        [a, b],
        :cerl.c_values([b, a]),
        evars,
        :cerl.c_values([:cerl.c_atom(:caught), :cerl.c_atom(:caught)])
      )

    core =
      :cerl.c_module(:cerl.c_atom(:core_try), [empty, pair, bound, empty_bound, matched], [], [
        {empty,
         :cerl.c_fun(
           [],
           :cerl.c_try(
             :cerl.c_values([]),
             [],
             :cerl.c_atom(:empty),
             Enum.take(evars, 2),
             :cerl.c_atom(:caught)
           )
         )},
        {pair,
         :cerl.c_fun(
           [x],
           :cerl.c_try(returned, [a, b], :cerl.c_tuple([b, a]), evars, :cerl.c_atom(:caught))
         )},
        {bound, :cerl.c_fun([x], :cerl.c_let([a, b], protected, :cerl.c_tuple([a, b])))},
        {empty_bound, :cerl.c_fun([], :cerl.c_let([], :cerl.c_values([]), :cerl.c_atom(:empty)))},
        {matched,
         :cerl.c_fun(
           [x],
           :cerl.c_case(protected, [
             :cerl.c_clause([a, b], :cerl.c_tuple([a, b]))
           ])
         )}
      ])

    roots = [{:empty, 0}, {:pair, 1}, {:bound, 1}, {:empty_bound, 0}, {:matched, 1}]
    callback = fn _, _, _, _, _, _ -> flunk("unexpected remote call") end

    assert {:ok, functions, %{}, %{}, %{}, []} =
             core_translate(:core_try, :lynx_core_to_leanj.to_definitions(core), roots, callback)

    by_name =
      Map.new(functions, fn {{name, _}, function} ->
        {Atom.to_string(name), function.translation}
      end)

    assert %{
             "kind" => "try",
             "vars" => [],
             "computation" => %{"kind" => "return", "values" => []},
             "exception_vars" => [_, _]
           } = by_name["empty"]["body"]

    assert %{
             "kind" => "try",
             "vars" => [_, _],
             "computation" => %{"kind" => "return", "values" => [_, _]},
             "exception_vars" => [_, _, _]
           } = by_name["pair"]["body"]

    assert %{
             "kind" => "bind",
             "vars" => [],
             "computation" => %{"kind" => "return", "values" => []}
           } = by_name["empty_bound"]["body"]

    assert %{
             "kind" => "bind",
             "vars" => [_, _],
             "computation" => %{
               "kind" => "try",
               "computation" => %{"kind" => "return", "values" => [_, _]}
             }
           } = by_name["bound"]["body"]

    assert %{
             "kind" => "bind",
             "vars" => [left, right],
             "body" => %{"kind" => "match", "expressions" => [left, right]}
           } = by_name["matched"]["body"]
  end

  test "recursively translates reachable callees and keeps each function's calls separate" do
    body =
      :cerl.c_let(
        [:cerl.c_var(:Y)],
        call(:odd),
        :cerl.c_case(:cerl.c_var(:Y), [
          :cerl.c_clause([:cerl.c_nil()], call(:helper)),
          :cerl.c_clause([:cerl.c_var(:Other)], call(:even))
        ])
      )

    definitions =
      definitions([
        definition(:entry, body),
        definition(:odd, call(:even)),
        definition(:even, call(:odd)),
        definition(:helper, call(:helper)),
        definition(:unused, unsupported_call())
      ])

    assert {:ok, functions, []} = translate(definitions)

    assert Enum.sort(Map.keys(functions)) == [{:entry, 1}, {:even, 1}, {:helper, 1}, {:odd, 1}]
    assert Enum.sort(functions[{:entry, 1}].local_calls) == [{:even, 1}, {:helper, 1}, {:odd, 1}]

    assert %{
             {:odd, 1} => %{local_calls: [{:even, 1}]},
             {:even, 1} => %{local_calls: [{:odd, 1}]},
             {:helper, 1} => %{local_calls: []}
           } = functions

    for {{name, 1}, %{translation: translation}} <- functions do
      expected = Atom.to_string(name)
      assert %{"kind" => "def", "name" => ^expected} = translation
    end
  end

  test "lowers a case input computation to a bind followed by a match" do
    input = :cerl.c_call(:cerl.c_atom(:other), :cerl.c_atom(:entry), [:cerl.c_var(0)])

    body =
      :cerl.c_case(input, [
        :cerl.c_clause([:cerl.c_atom(true)], :cerl.c_var(0)),
        :cerl.c_clause([:cerl.c_var(:Other)], :cerl.c_atom(false))
      ])

    defs = definitions([definition(:entry, body)])

    assert {:ok, functions, [{:other, :entry, 1, []}]} =
             translate(defs, %{}, %{{:other, :entry, 1} => :sequential})

    assert %{purity: :sequential, local_calls: [], translation: translation} =
             functions[{:entry, 1}]

    assert %{
             "body" => %{
               "kind" => "bind",
               "vars" => [%{"kind" => "var", "name" => name}],
               "computation" => %{"kind" => "remote_call", "name" => "entry"},
               "body" => %{
                 "kind" => "match",
                 "expressions" => [%{"kind" => "var", "name" => name}],
                 "cases" => [_, _]
               }
             }
           } = translation

    assert name == %{"generated" => 0}
  end

  test "threads the remote callback context through local functions and reuses translations" do
    remote = fn module ->
      :cerl.c_call(:cerl.c_atom(module), :cerl.c_atom(:entry), [:cerl.c_var(0)])
    end

    definitions =
      definitions([
        definition(:entry, :cerl.c_let([:cerl.c_var(:Y)], call(:first), call(:second))),
        definition(:first, remote.(:one)),
        definition(:second, remote.(:two))
      ])

    assert {:ok, functions, calls} = translate(definitions)

    assert calls == [{:two, :entry, 1, []}, {:one, :entry, 1, []}]
    assert Enum.sort(functions[{:entry, 1}].local_calls) == [{:first, 1}, {:second, 1}]

    assert %{
             {:first, 1} => %{local_calls: []},
             {:second, 1} => %{local_calls: []}
           } = functions

    assert {:ok, ^functions, []} = translate(definitions, functions)
  end

  test "translates qualified calls to the current module as local calls" do
    qualified = :cerl.c_call(:cerl.c_atom(:example), :cerl.c_atom(:helper), [:cerl.c_var(0)])
    definitions = definitions([definition(:entry, qualified), definition(:helper, qualified)])

    assert {:ok, functions, []} = translate(definitions)

    assert Enum.sort(Map.keys(functions)) == [{:entry, 1}, {:helper, 1}]

    assert %{
             {:entry, 1} => %{local_calls: [{:helper, 1}]},
             {:helper, 1} => %{local_calls: []}
           } = functions

    for name <- [:entry, :helper] do
      assert %{"body" => %{"kind" => "local_call", "name" => "helper"}} =
               functions[{name, 1}].translation
    end
  end

  test "passes raw file and position annotations to remote calls" do
    body =
      :cerl.ann_c_call(
        [{:file, ~c"foo"}, {7, 3}],
        :cerl.c_atom(:other),
        :cerl.c_atom(:entry),
        [:cerl.c_var(0)]
      )

    assert {:ok, _, [{:other, :entry, 1, [{:file, ~c"foo"}, {7, 3}]}]} =
             translate(definitions([definition(:entry, body)]))
  end

  test "qualifies remote modules and preserves raw function names" do
    for {module, expected} <- [
          {:other, "Erlang.other"},
          {Foo.Bar, "Elixir.Foo.Bar"}
        ] do
      body = :cerl.c_call(:cerl.c_atom(module), :cerl.c_atom(:entry), [:cerl.c_var(0)])

      assert {:ok, functions, [{^module, :entry, 1, []}]} =
               translate(definitions([definition(:entry, body)]))

      assert %{"body" => %{"kind" => "remote_call", "module" => ^expected, "name" => "entry"}} =
               functions[{:entry, 1}].translation
    end
  end

  test "accumulates remote impurity without leaking it between functions" do
    remote = fn module ->
      :cerl.c_call(:cerl.c_atom(module), :cerl.c_atom(:entry), [:cerl.c_var(0)])
    end

    defs =
      definitions([
        definition(:entry, :cerl.c_let([:cerl.c_var(:Y)], remote.(:impure), call(:helper))),
        definition(:helper, remote.(:pure))
      ])

    assert {:ok, functions, calls} = translate(defs, %{}, %{{:impure, :entry, 1} => :sequential})

    assert %{
             {:entry, 1} => %{purity: :sequential},
             {:helper, 1} => %{purity: :pure}
           } = functions

    assert calls == [{:pure, :entry, 1, []}, {:impure, :entry, 1, []}]
  end

  test "extracts paired law attributes and calls their ordinary predicate helpers" do
    core =
      :cerl.c_module(
        :cerl.c_atom(:example),
        [],
        [
          {:cerl.c_atom(:law),
           :cerl.ann_abstract([10], [
             %{name: {:entry, [:x]}, requires: :requirement, ensures: :expected}
           ])},
          {:cerl.c_atom(:proof), :cerl.ann_abstract([11], ["rfl"])}
        ],
        [definition(:requirement, :cerl.c_atom(true)), definition(:expected, :cerl.c_atom(true))]
      )

    definitions = :lynx_core_to_leanj.to_definitions(core)
    assert {:law, _} = definitions[{:entry, 1}]
    assert {:function, _} = definitions[{:requirement, 1}]
    assert {laws, functions} = translate_law(definitions)
    assert Enum.sort(Map.keys(functions)) == [{:expected, 1}, {:requirement, 1}]

    assert %{
             "kind" => "theorem",
             "name" => "entry",
             "span" => [10],
             "params" => ["x"],
             "requires" => "requirement",
             "ensures" => "expected",
             "proof" => %{"source" => "rfl", "indentation" => 0, "span" => [12]}
           } == laws[{:entry, 1}]
  end

  test "uses the law's explicit span instead of the Core attribute's annotations" do
    for {span, expected} <- [{40, [40]}, {{40, 9}, [40, 9]}] do
      definitions =
        law_core(%{name: {:entry, [:x]}, ensures: :expected, span: span})
        |> :lynx_core_to_leanj.to_definitions()

      assert {laws, _functions} = translate_law(definitions)
      assert %{"span" => ^expected, "proof" => %{"span" => [12]}} = laws[{:entry, 1}]
    end
  end

  describe "to_definition" do
    test "extracts ordinary functions and ignores unrelated attributes" do
      defs = [definition(:entry, :cerl.c_atom(true))]
      [{_, fun}] = defs
      core = core([attribute(:other, [:value], [2])], defs)
      assert %{{:entry, 1} => {:function, ^fun}} = :lynx_core_to_leanj.to_definitions(core)
    end

    test "extracts a law with optional requires and a binary proof" do
      core = law_core(%{name: {:entry, [:x]}, ensures: :expected}, ["exact hé"])

      assert %{
               {:entry, 1} => {:law, law},
               {:expected, 1} => {:function, _}
             } = :lynx_core_to_leanj.to_definitions(core)

      assert law == %{
               name: {:entry, [:x]},
               ensures: :expected,
               anno: [10],
               proof: %{"source" => "exact hé", "indentation" => 0, "span" => [12]}
             }
    end

    test "extracts multiple paired laws with binary proofs" do
      law = %{name: {:entry, [:x]}, requires: :requirement, ensures: :expected}
      core = law_core(law, ["rfl"])

      attrs =
        :cerl.module_attrs(core) ++
          [
            attribute(:law, [%{name: {:second, [:b, :a]}, ensures: :expected}], [14]),
            attribute(:proof, ["rfl"], [{15, 8}])
          ]

      core = core(attrs, :cerl.module_defs(core))

      assert %{
               {:entry, 1} =>
                 {:law,
                  %{
                    requires: :requirement,
                    proof: %{"source" => "rfl", "indentation" => 0, "span" => [12]}
                  }},
               {:second, 2} => {:law, %{name: {:second, [:b, :a]}, proof: %{"span" => [16]}}}
             } = :lynx_core_to_leanj.to_definitions(core)
    end

    test "reports missing or misplaced proofs at the offending attribute" do
      law = attribute(:law, [%{name: {:entry, [:x]}, ensures: :expected}], [10])
      proof = attribute(:proof, ["rfl"], [11])
      other = attribute(:other, [:value], [12])

      for attrs <- [[law], [law, other, proof]] do
        assert {:error, [10], "proof must immediately follow law"} ==
                 :lynx_core_to_leanj.to_definitions(core(attrs))
      end

      assert {:error, [11], "proof without preceding law"} ==
               :lynx_core_to_leanj.to_definitions(core([proof]))
    end

    test "reports malformed law descriptors with their original annotations" do
      anno = [{:file, ~c"law.erl"}, {10, 2}]
      reason = "law must contain name {atom, parameters} and ensures function name"

      for law <- [
            %{},
            %{name: {:entry, [:x]}},
            %{name: {:entry, -1}, ensures: :expected},
            %{name: {:entry, 1}, ensures: :expected},
            %{name: {"entry", [:x]}, ensures: :expected},
            %{name: {:entry, [:x]}, ensures: "expected"}
          ] do
        core = core([attribute(:law, [law], anno), attribute(:proof, ["rfl"], [11])])
        assert {:error, ^anno, ^reason} = :lynx_core_to_leanj.to_definitions(core)
      end
    end

    test "requires unique atom parameter names" do
      for {params, reason} <- [
            {["x"], "law parameters must be atoms"},
            {[:x, :x], "law parameters must be unique"}
          ] do
        assert {:error, [10], ^reason} =
                 :lynx_core_to_leanj.to_definitions(
                   law_core(%{name: {:entry, params}, ensures: :expected})
                 )
      end
    end

    test "validates requires names" do
      law = %{name: {:entry, [:x]}, ensures: :expected, requires: "requirement"}

      assert {:error, [10], "law requires must be a function name"} =
               :lynx_core_to_leanj.to_definitions(law_core(law))
    end

    test "reports invalid law spans at the Core attribute" do
      law = %{name: {:entry, [:x]}, ensures: :expected, span: {40, 0}}

      assert {:error, [10], "law span must be a line or {line, column}"} =
               :lynx_core_to_leanj.to_definitions(law_core(law))
    end

    test "extracts embedded proof metadata with tuple and integer spans" do
      for {span, expected} <- [{{12, 9}, [12, 9]}, {12, [12]}] do
        law = %{
          name: {:entry, [:x]},
          ensures: :expected,
          proof: %{source: "rfl", indentation: 4, span: span}
        }

        core = core([attribute(:law, [law], [10])])

        assert %{
                 {:entry, 1} =>
                   {:law, %{proof: %{"source" => "rfl", "indentation" => 4, "span" => ^expected}}}
               } =
                 :lynx_core_to_leanj.to_definitions(core)
      end
    end

    test "reports invalid embedded proof metadata at the law attribute" do
      for {extra, reason} <- [
            {%{source: ~c"rfl"},
             "embedded proof requires a binary, nonnegative indentation and span"},
            {%{indentation: -1},
             "embedded proof requires a binary, nonnegative indentation and span"},
            {%{span: {12, 0}}, "embedded proof span must be a line or {line, column}"}
          ] do
        law = %{
          name: {:entry, [:x]},
          ensures: :expected,
          proof: Map.merge(%{source: "rfl", indentation: 0, span: 12}, extra)
        }

        assert {:error, [10], ^reason} =
                 :lynx_core_to_leanj.to_definitions(core([attribute(:law, [law], [10])]))
      end
    end

    test "rejects embedded proof metadata at the law root" do
      law = %{name: {:entry, [:x]}, ensures: :expected, proof: "rfl", indentation: 0, span: 12}

      assert {:error, [10], "embedded proof requires a binary, nonnegative indentation and span"} =
               :lynx_core_to_leanj.to_definitions(core([attribute(:law, [law], [10])]))
    end

    test "requires binary proofs and reports errors at the proof attribute" do
      for proof <- [~c"rfl", [:not_text], [42]] do
        assert {:error, [11], "proof must be a binary"} ==
                 :lynx_core_to_leanj.to_definitions(
                   law_core(%{name: {:entry, [:x]}, ensures: :expected}, proof)
                 )
      end
    end

    test "a law replaces an ordinary function with the same name and arity" do
      original = law_core(%{name: {:entry, [:x]}, ensures: :expected})

      core =
        core(
          :cerl.module_attrs(original),
          [definition(:entry, :cerl.c_atom(true)) | :cerl.module_defs(original)]
        )

      assert %{{:entry, 1} => {:law, %{ensures: :expected}}} =
               :lynx_core_to_leanj.to_definitions(core)
    end
  end

  test "returns annotated binary reasons for unsupported Core during translation" do
    anno = [{:file, ~c"example.erl"}, {7, 3}]
    body = :cerl.ann_c_primop(anno, :cerl.c_atom(:unsupported), [])
    assert {:error, ^anno, reason} = translate(definitions([definition(:entry, body)]))
    assert reason =~ "unsupported Core expression:"
    assert reason =~ "unsupported"
  end

  test "rejects dynamic function references and calls" do
    module = :cerl.c_var(:M)
    name = :cerl.c_atom(:f)

    for {body, message} <- [
          {:cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:make_fun), [
             module,
             name,
             :cerl.c_int(1)
           ]), "dynamic function references"},
          {:cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:apply), [module, name, :cerl.c_nil()]),
           "dynamic calls, such as apply(M, F, Args)"},
          {:cerl.c_call(module, name, []), "dynamic calls, such as mod.fun(x)"}
        ] do
      assert {:error, _, reason} = translate(definitions([definition(:entry, body)]))
      assert reason =~ message
    end
  end

  test "translates laws without a requires helper" do
    definitions =
      :lynx_core_to_leanj.to_definitions(law_core(%{name: {:entry, [:x]}, ensures: :expected}))

    assert {%{{:entry, 1} => law}, functions} = translate_law(definitions)
    assert Map.keys(functions) == [{:expected, 1}]

    assert law == %{
             "kind" => "theorem",
             "name" => "entry",
             "params" => ["x"],
             "span" => [10],
             "ensures" => "expected",
             "proof" => %{"source" => "rfl", "indentation" => 0, "span" => [12]}
           }
  end

  defp core(attrs, defs \\ []), do: :cerl.c_module(:cerl.c_atom(:example), [], attrs, defs)
  defp attribute(name, value, anno), do: {:cerl.c_atom(name), :cerl.ann_abstract(anno, value)}

  defp law_core(law, proof \\ ["rfl"]) do
    core(
      [attribute(:law, [law], [10]), attribute(:proof, proof, [11])],
      [definition(:requirement, :cerl.c_atom(true)), definition(:expected, :cerl.c_atom(true))]
    )
  end

  defp translate(definitions, translated \\ %{}, purity \\ %{}) do
    callback = fn calls, module, function, arity, span_anno, funs ->
      if module == :example do
        :local
      else
        purity = Map.get(purity, {module, function, arity}, :pure)
        {purity, funs, [{module, function, arity, span_anno} | calls]}
      end
    end

    case core_translate(:example, definitions, [{:entry, 1}], callback, translated) do
      {:ok, functions, _literals, _laws, _funs, calls} -> {:ok, functions, calls}
      {:error, _, _} = error -> error
    end
  end

  # Translates roots starting from an empty literal pool and function registry.
  defp core_translate(module, definitions, roots, callback, translated \\ %{}) do
    :lynx_core_to_leanj.translate(
      module,
      definitions,
      roots,
      translated,
      %{},
      %{},
      [],
      {[], callback}
    )
  end

  defp translate_law(definitions) do
    callback = fn _, _, _, _, _, _ -> :local end

    assert {:ok, functions, %{}, laws, %{}, []} =
             core_translate(:example, definitions, [{:entry, 1}], callback)

    {laws, functions}
  end

  defp definitions(defs) do
    defs
    |> then(&:cerl.c_module(:cerl.c_atom(:example), [], &1))
    |> :lynx_core_to_leanj.to_definitions()
  end

  defp definition(name, body), do: {:cerl.c_fname(name, 1), :cerl.c_fun([:cerl.c_var(0)], body)}
  defp call(name), do: :cerl.c_apply(:cerl.c_fname(name, 1), [:cerl.c_var(0)])

  defp unsupported_call,
    do: :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:abs), [:cerl.c_int(-1)])
end
