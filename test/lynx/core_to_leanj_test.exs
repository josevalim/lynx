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
                purity: :pure,
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

  test "calls nested in arguments are bound in order before the call" do
    abs = :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:abs), [:cerl.c_var(0)])
    neg = :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:-), [:cerl.c_var(0)])
    body = :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:+), [abs, neg])

    assert {:ok,
            %{
              {:entry, 1} => %{
                translation: %{
                  "body" => %{
                    "kind" => "bind",
                    "vars" => [%{"kind" => "var", "name" => %{"generated" => 0}} = first],
                    "computation" => %{"kind" => "remote_call", "name" => "abs"},
                    "body" => %{
                      "kind" => "bind",
                      "vars" => [%{"kind" => "var", "name" => %{"generated" => 1}} = second],
                      "computation" => %{"kind" => "remote_call", "name" => "-"},
                      "body" => %{
                        "kind" => "remote_call",
                        "name" => "+",
                        "args" => [first, second]
                      }
                    }
                  }
                }
              }
            }, _} = translate(definitions([definition(:entry, body)]))
  end

  test "binaries nested in arguments are constructed before the call" do
    segment =
      :cerl.c_bitstr(
        :cerl.c_var(0),
        :cerl.c_int(8),
        :cerl.c_int(1),
        :cerl.c_atom(:integer),
        :cerl.abstract([:unsigned, :big])
      )

    body =
      :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:byte_size), [
        :cerl.c_binary([segment])
      ])

    assert {:ok,
            %{
              {:entry, 1} => %{
                translation: %{
                  "body" => %{
                    "kind" => "bind",
                    "vars" => [%{"kind" => "var"} = var],
                    "computation" => %{"kind" => "bitstring_constructor"},
                    "body" => %{"kind" => "remote_call", "name" => "byte_size", "args" => [var]}
                  }
                }
              }
            }, _} = translate(definitions([definition(:entry, body)]))
  end

  test "calls nested in constructors are bound before the constructor" do
    abs = :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:abs), [:cerl.c_var(0)])
    body = :cerl.c_cons(abs, :cerl.c_nil())

    assert {:ok,
            %{
              {:entry, 1} => %{
                translation: %{
                  "body" => %{
                    "kind" => "bind",
                    "vars" => [%{"kind" => "var"} = var],
                    "computation" => %{"kind" => "remote_call", "name" => "abs"},
                    "body" => %{
                      "kind" => "return",
                      "values" => [%{"kind" => "cons", "head" => var}]
                    }
                  }
                }
              }
            }, _} = translate(definitions([definition(:entry, body)]))
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
                          %{
                            "kind" => "function",
                            "module" => "erlang",
                            "name" => "=<",
                            "arity" => 2,
                            "captures" => []
                          },
                          %{
                            "kind" => "function",
                            "module" => "erlang",
                            "name" => "=<",
                            "arity" => 2,
                            "captures" => []
                          }
                        ]
                      }
                    ]
                  }
                }
              },
              {:"erlang:=<", 2} => %{
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

  test "spawning a literal function with arguments spawns an anonymous closure over them" do
    args = :cerl.c_cons(:cerl.c_var(0), :cerl.c_cons(:cerl.c_atom(:ok), :cerl.c_nil()))

    body =
      :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:spawn_link), [
        :cerl.c_atom(:other),
        :cerl.c_atom(:run),
        args
      ])

    assert {:ok,
            %{
              {:entry, 1} => %{
                translation: %{
                  "body" => %{
                    "kind" => "remote_call",
                    "module" => "Erlang.erlang",
                    "name" => "spawn_link",
                    "args" => [
                      %{
                        "kind" => "function",
                        "module" => "example",
                        "name" => "-entry/1-anonymous-0-",
                        "arity" => 0,
                        "captures" => [%{"name" => 0}]
                      }
                    ]
                  }
                }
              },
              {:"-entry/1-anonymous-0-", 1} => %{
                translation: %{
                  "params" => [%{"name" => 0}],
                  "body" => %{
                    "kind" => "remote_call",
                    "module" => "Erlang.other",
                    "name" => "run",
                    "args" => [%{"name" => 0}, %{"kind" => "atom", "value" => "ok"}]
                  }
                }
              }
            }, _} = translate(definitions([definition(:entry, body)]))
  end

  test "spawning with arguments that are not a list of values is rejected" do
    body =
      :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:spawn), [
        :cerl.c_atom(:other),
        :cerl.c_atom(:run),
        :cerl.c_var(0)
      ])

    assert {:error, _, message} = translate(definitions([definition(:entry, body)]))
    assert message =~ "spawning with arguments"
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
        [
          {loop,
           :cerl.ann_c_fun(
             [{:id, {0, 0, :"-entry/1-fun-0-"}}],
             [input],
             :cerl.c_tuple([captured, input, loop])
           )}
        ],
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
                                "module" => "example",
                                "name" => "-entry/1-fun-0-",
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
                          %{
                            "kind" => "function",
                            "name" => "-entry/1-fun-0-",
                            "captures" => [%{"name" => 0}]
                          }
                        ]
                      }
                    ]
                  }
                }
              },
              {:"-entry/1-fun-0-", 2} => %{
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

  test "translates float segment sizes computed at runtime" do
    segment =
      :cerl.c_bitstr(
        :cerl.c_int(1),
        :cerl.c_var(0),
        :cerl.c_int(2),
        :cerl.c_atom(:float),
        :cerl.abstract([:unsigned, :big])
      )

    assert {:ok,
            %{
              {:entry, 1} => %{
                translation: %{
                  "body" => %{
                    "kind" => "bitstring_constructor",
                    "segments" => [
                      %{
                        "type" => "float",
                        "value" => %{"kind" => "integer", "value" => 1},
                        "size" => %{"kind" => "var", "name" => 0},
                        "unit" => 2
                      }
                    ]
                  }
                }
              }
            }, []} = translate(definitions([definition(:entry, :cerl.c_binary([segment]))]))
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

  test "translates receive clauses whose unused bodies the compiler dropped" do
    loop = :cerl.c_fname(:receive_loop, 0)
    available = :cerl.c_var(:available)
    message = :cerl.c_var(:message)
    expired = :cerl.c_var(:expired)
    remove = :cerl.c_primop(:cerl.c_atom(:remove_message), [])
    next = :cerl.c_seq(:cerl.c_primop(:cerl.c_atom(:recv_next), []), :cerl.c_apply(loop, []))

    scan =
      :cerl.c_case(message, [
        :cerl.c_clause([:cerl.c_tuple([:cerl.c_atom(:stop)])], remove),
        :cerl.c_clause([:cerl.c_var(:other)], next)
      ])

    wait =
      :cerl.c_let(
        [expired],
        :cerl.c_primop(:cerl.c_atom(:recv_wait_timeout), [:cerl.c_atom(:infinity)]),
        :cerl.c_case(expired, [
          :cerl.c_clause([:cerl.c_atom(true)], :cerl.c_atom(:ok)),
          :cerl.c_clause([:cerl.c_atom(false)], :cerl.c_apply(loop, []))
        ])
      )

    peek =
      :cerl.c_let(
        [available, message],
        :cerl.c_primop(:cerl.c_atom(:recv_peek_message), []),
        :cerl.c_case(available, [
          :cerl.c_clause([:cerl.c_atom(true)], scan),
          :cerl.c_clause([:cerl.c_atom(false)], wait)
        ])
      )

    receive = :cerl.c_letrec([{loop, :cerl.c_fun([], peek)}], :cerl.c_apply(loop, []))
    body = :cerl.c_seq(receive, :cerl.c_atom(:done))

    assert {:ok, functions, []} = translate(definitions([definition(:entry, body)]))

    assert %{
             "body" => %{
               "kind" => "bind",
               "computation" => %{
                 "kind" => "receive",
                 "cases" => [
                   %{
                     "pattern" => %{"kind" => "tuple"},
                     "body" => %{"kind" => "return", "values" => [%{"kind" => "atom"}]}
                   }
                 ]
               },
               "body" => %{"kind" => "return", "values" => [%{"value" => "done"}]}
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

  test "Elixir's strict and/or raise badbool" do
    body =
      :cerl.c_case(call(:left), [
        :cerl.c_clause([:cerl.c_atom(false)], :cerl.c_atom(false)),
        :cerl.c_clause([:cerl.c_atom(true)], call(:right)),
        :cerl.c_clause(
          [:cerl.c_var(:X)],
          :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:error), [
            :cerl.c_tuple([:cerl.c_atom(:badbool), :cerl.c_atom(:and), :cerl.c_var(:X)])
          ])
        )
      ])

    defs =
      definitions([
        definition(:entry, body),
        definition(:left, :cerl.c_atom(true)),
        definition(:right, :cerl.c_atom(true))
      ])

    assert {:ok, %{{:entry, 1} => %{translation: %{"body" => translated}}}, _} = translate(defs)

    assert %{
             "kind" => "andalso",
             "badbool" => true,
             "left" => %{"kind" => "local_call"},
             "right" => %{"kind" => "local_call"}
           } = translated
  end

  test "Elixir's and/or nest to the left, collapsing only Boolean left operands" do
    erlang = fn name, args -> :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(name), args) end
    var = :cerl.c_var(:Left)

    # (is_integer(x) and Right) and x < 5, with a compiler-checked inner case
    outer = fn inner_right ->
      left =
        :cerl.c_case(erlang.(:is_integer, [:cerl.c_var(0)]), [
          :cerl.ann_c_clause([:compiler_generated], [:cerl.c_atom(false)], :cerl.c_atom(false)),
          :cerl.c_clause([:cerl.c_atom(true)], inner_right)
        ])

      case_on_left =
        :cerl.c_case(var, [
          :cerl.c_clause([:cerl.c_atom(false)], :cerl.c_atom(false)),
          :cerl.c_clause([:cerl.c_atom(true)], erlang.(:<, [:cerl.c_var(0), :cerl.c_int(5)])),
          :cerl.c_clause(
            [:cerl.c_var(:Other)],
            :cerl.c_primop(:cerl.c_atom(:match_fail), [
              :cerl.c_tuple([:cerl.c_atom(:case_clause), :cerl.c_var(:Other)])
            ])
          )
        ])

      result = :cerl.c_var(:Result)

      {:cerl.c_let([var], left, case_on_left),
       :cerl.c_let([var], left, :cerl.c_let([result], case_on_left, result))}
    end

    translate_body = fn body ->
      defs = definitions([definition(:entry, body), definition(:check, :cerl.c_atom(true))])
      {:ok, %{{:entry, 1} => %{translation: %{"body" => translated}}}, _} = translate(defs)
      translated
    end

    # A Boolean inner chain cannot reach case_clause, so it becomes the left operand.
    zero = :cerl.c_var(:Zero)

    {direct, bound} =
      outer.(:cerl.c_let([zero], :cerl.c_int(0), erlang.(:>=, [:cerl.c_var(0), zero])))

    assert %{
             "kind" => "andalso",
             "left" => %{
               "kind" => "andalso",
               "left" => %{"kind" => "remote_call", "name" => "is_integer"},
               "right" => %{
                 "kind" => "bind",
                 "body" => %{"kind" => "remote_call", "name" => ">="}
               }
             },
             "right" => %{"kind" => "remote_call", "name" => "<"}
           } = translated = translate_body.(direct)

    refute Map.has_key?(translated, "badbool")
    assert %{"kind" => "bind", "computation" => ^translated} = translate_body.(bound)

    # Otherwise the inner chain may return any value and the case stays.
    {direct, _} = outer.(call(:check))
    assert %{"kind" => "bind", "body" => %{"kind" => "match"}} = translate_body.(direct)
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

  test "records calls to function values apart from purity" do
    fun_call = :cerl.c_apply(:cerl.c_var(0), [:cerl.c_int(1)])

    remote = fn module ->
      :cerl.c_call(:cerl.c_atom(module), :cerl.c_atom(:entry), [:cerl.c_var(0)])
    end

    purities = %{{:impure, :entry, 1} => :sequential, {:applies, :entry, 1} => {:pure, true}}

    for {body, purity} <- [
          {fun_call, :pure},
          {:cerl.c_let([:cerl.c_var(:Y)], remote.(:impure), fun_call), :sequential}
        ] do
      assert {:ok, %{{:entry, 1} => %{purity: ^purity, dispatches: true}}, _} =
               translate(definitions([definition(:entry, body)]), %{}, purities)
    end

    # Calls to remote callees that call function values record it.
    assert {:ok, functions, _} =
             translate(definitions([definition(:entry, remote.(:applies))]), %{}, purities)

    assert %{
             purity: :pure,
             dispatches: true,
             translation: %{
               "body" => %{"kind" => "remote_call", "purity" => "pure", "dispatches" => true}
             }
           } = functions[{:entry, 1}]

    assert {:ok, functions, _} =
             translate(definitions([definition(:entry, remote.(:impure))]), %{}, purities)

    assert %{dispatches: false, translation: %{"body" => body}} = functions[{:entry, 1}]
    refute Map.has_key?(body, "dispatches")
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

  describe "protocols" do
    test "protocol functions call the implementation impl_for!/1 selects" do
      assert %{{:size, 1} => %{translation: %{"params" => [param], "body" => body}}} =
               translate_protocol(Lynx.Support.Size, [{:size, 1}])

      assert %{
               "kind" => "bind",
               "vars" => [impl],
               "computation" => %{
                 "kind" => "local_call",
                 "name" => "impl_for!",
                 "args" => [^param]
               },
               "body" => %{
                 "kind" => "match",
                 "expressions" => [impl],
                 "cases" => [
                   integer,
                   list,
                   point,
                   map,
                   %{
                     "patterns" => [other],
                     "body" => %{
                       "kind" => "raise",
                       "reason" => %{
                         "kind" => "tuple",
                         "elements" => [%{"kind" => "atom", "value" => "case_clause"}, other]
                       }
                     }
                   }
                 ]
               }
             } = body

      for {clause, impl} <- [
            {integer, "Elixir.Lynx.Support.Size.Integer"},
            {list, "Elixir.Lynx.Support.Size.List"},
            {point, "Elixir.Lynx.Support.Size.Lynx.Support.Point"},
            {map, "Elixir.Lynx.Support.Size.Map"}
          ] do
        assert %{
                 "patterns" => [%{"kind" => "atom", "value" => ^impl}],
                 "body" => %{
                   "kind" => "remote_call",
                   "module" => ^impl,
                   "name" => "size",
                   "args" => [^param]
                 }
               } = clause
      end
    end

    test "impl_for/1 matches built-in constructors and structs among maps" do
      assert %{{:impl_for, 1} => %{translation: %{"params" => [param], "body" => body}}} =
               translate_protocol(Lynx.Support.Size, [{:impl_for, 1}])

      assert %{
               "kind" => "match",
               "expressions" => [^param],
               "cases" => [
                 %{"patterns" => [%{"kind" => "nil"}], "body" => empty},
                 %{"patterns" => [%{"kind" => "cons"}], "body" => list},
                 %{
                   "guard" => %{"kind" => "remote_call", "name" => "is_map", "args" => [^param]},
                   "body" => %{
                     "kind" => "match",
                     "expressions" => [^param],
                     "cases" => [
                       %{
                         "patterns" => [
                           %{
                             "kind" => "map",
                             "entries" => [
                               %{
                                 "key" => %{"kind" => "atom", "value" => "__struct__"},
                                 "value" => %{
                                   "kind" => "atom",
                                   "value" => "Elixir.Lynx.Support.Point"
                                 }
                               }
                             ]
                           }
                         ],
                         "body" => point
                       },
                       %{
                         "patterns" => [
                           %{
                             "kind" => "map",
                             "entries" => [
                               %{
                                 "key" => %{"kind" => "atom", "value" => "__struct__"},
                                 "value" => struct
                               }
                             ]
                           }
                         ],
                         "guard" => %{
                           "kind" => "remote_call",
                           "name" => "is_atom",
                           "args" => [struct]
                         },
                         "body" => other_struct
                       },
                       %{"patterns" => [%{"kind" => "var"}], "body" => map}
                     ]
                   }
                 },
                 %{
                   "guard" => %{
                     "kind" => "remote_call",
                     "name" => "is_integer",
                     "args" => [^param]
                   },
                   "body" => integer
                 },
                 %{"patterns" => [%{"kind" => "var"}], "body" => other}
               ]
             } = body

      for {body, impl} <- [
            {empty, "Elixir.Lynx.Support.Size.List"},
            {list, "Elixir.Lynx.Support.Size.List"},
            {point, "Elixir.Lynx.Support.Size.Lynx.Support.Point"},
            {other_struct, "nil"},
            {map, "Elixir.Lynx.Support.Size.Map"},
            {integer, "Elixir.Lynx.Support.Size.Integer"},
            {other, "nil"}
          ] do
        assert %{"kind" => "return", "values" => [%{"kind" => "atom", "value" => ^impl}]} = body
      end
    end

    test "impl_for!/1 raises Protocol.UndefinedError without an implementation" do
      assert %{{:impl_for!, 1} => %{translation: %{"params" => [param], "body" => body}}} =
               translate_protocol(Lynx.Support.Size, [{:impl_for!, 1}])

      assert %{
               "kind" => "bind",
               "vars" => [impl],
               "computation" => %{
                 "kind" => "local_call",
                 "name" => "impl_for",
                 "args" => [^param]
               },
               "body" => %{
                 "kind" => "match",
                 "expressions" => [impl],
                 "cases" => [
                   %{
                     "patterns" => [%{"kind" => "atom", "value" => "nil"}],
                     "body" => %{"kind" => "raise", "class" => "error", "reason" => error}
                   },
                   %{"patterns" => [found], "body" => %{"kind" => "return", "values" => [found]}}
                 ]
               }
             } = body

      assert %{
               "kind" => "map",
               "entries" => [
                 %{
                   "key" => %{"kind" => "atom", "value" => "__struct__"},
                   "value" => %{"kind" => "atom", "value" => "Elixir.Protocol.UndefinedError"}
                 },
                 %{
                   "key" => %{"kind" => "atom", "value" => "__exception__"},
                   "value" => %{"kind" => "atom", "value" => "true"}
                 },
                 %{
                   "key" => %{"kind" => "atom", "value" => "protocol"},
                   "value" => %{"kind" => "atom", "value" => "Elixir.Lynx.Support.Size"}
                 },
                 %{"key" => %{"kind" => "atom", "value" => "value"}, "value" => ^param},
                 %{
                   "key" => %{"kind" => "atom", "value" => "description"},
                   "value" => %{"kind" => "bitstring", "bytes" => [], "last_bits" => 0}
                 }
               ]
             } = error
    end

    test "falls back to the implementation for Any" do
      assert %{
               {:impl_for!, 1} => %{
                 translation: %{
                   "params" => [param],
                   "body" => %{"kind" => "local_call", "name" => "impl_for", "args" => [param]}
                 }
               },
               {:impl_for, 1} => %{
                 translation: %{"body" => %{"kind" => "match", "cases" => cases}}
               }
             } = translate_protocol(Lynx.Support.Describe, [{:impl_for!, 1}])

      assert [
               %{"guard" => %{"name" => "is_atom"}},
               %{
                 "guard" => %{"name" => "is_map"},
                 "body" => %{"cases" => [_tagged, %{"body" => other_struct}, %{"body" => map}]}
               },
               %{"patterns" => [%{"kind" => "var"}], "body" => other}
             ] = cases

      for body <- [other_struct, map, other] do
        assert %{
                 "kind" => "return",
                 "values" => [%{"kind" => "atom", "value" => "Elixir.Lynx.Support.Describe.Any"}]
               } = body
      end
    end

    test "keeps other protocol definitions" do
      definitions = protocol_definitions(:code.which(Lynx.Support.Size))

      assert %{{:__protocol__, 1} => {:function, _}, {:behaviour_info, 1} => {:function, _}} =
               definitions
    end

    test "rejects protocols that are not consolidated" do
      beam = Path.join(:code.lib_dir(:lynx), "ebin/Elixir.Lynx.Support.Size.beam")

      assert {:error, _anno,
              "cannot translate protocol Elixir.Lynx.Support.Size because it is not consolidated"} =
               protocol_definitions(String.to_charlist(beam))
    end

    test "implementations calling their protocol dispatch through local copies" do
      depth = beam_core(:code.which(Lynx.Support.Depth.List))

      assert :lynx_core_to_leanj.called_protocol(depth) ==
               {Lynx.Support.Depth, [{:depth, 1}]}

      assert :lynx_core_to_leanj.called_protocol(beam_core(:code.which(Lynx.Support.Size.List))) ==
               nil

      definitions = :lynx_core_to_leanj.to_definitions(depth)
      dispatch = {Lynx.Support.Depth, protocol_definitions(:code.which(Lynx.Support.Depth)), []}

      callback = fn calls, module, function, arity, _, funs ->
        if module == Lynx.Support.Depth.List,
          do: :local,
          else: {{:pure, false}, funs, [{module, function, arity} | calls]}
      end

      assert {:ok, functions, _, _, _, calls} =
               core_translate(
                 Lynx.Support.Depth.List,
                 definitions,
                 [{:depth, 1}],
                 callback,
                 %{},
                 [],
                 dispatch
               )

      assert Enum.sort(Map.keys(functions)) == [
               {:"Lynx.Support.Depth.depth", 1},
               {:"Lynx.Support.Depth.impl_for", 1},
               {:"Lynx.Support.Depth.impl_for!", 1},
               {:depth, 1}
             ]

      assert Enum.uniq(for {module, _, _} <- calls, do: module) -- [:erlang] ==
               [Lynx.Support.Depth.Integer]

      assert %{
               "body" => %{
                 "kind" => "bind",
                 "computation" => %{
                   "kind" => "local_call",
                   "name" => "Lynx.Support.Depth.impl_for!"
                 },
                 "body" => %{
                   "kind" => "match",
                   "cases" => [
                     %{
                       "patterns" => [%{"value" => "Elixir.Lynx.Support.Depth.Integer"}],
                       "body" => %{
                         "kind" => "remote_call",
                         "module" => "Elixir.Lynx.Support.Depth.Integer",
                         "name" => "depth"
                       }
                     },
                     %{
                       "patterns" => [%{"value" => "Elixir.Lynx.Support.Depth.List"}],
                       "body" => %{"kind" => "local_call", "name" => "depth"}
                     },
                     %{"body" => %{"kind" => "raise"}}
                   ]
                 }
               }
             } = functions[{:"Lynx.Support.Depth.depth", 1}].translation
    end

    test "implementations call cut off functions of their protocol" do
      depth = beam_core(:code.which(Lynx.Support.Depth.List))
      definitions = :lynx_core_to_leanj.to_definitions(depth)

      dispatch =
        {Lynx.Support.Depth, protocol_definitions(:code.which(Lynx.Support.Depth)),
         [{:impl_for!, 1}]}

      callback = fn calls, module, function, arity, _, funs ->
        if module == Lynx.Support.Depth.List,
          do: :local,
          else: {{:pure, false}, funs, [{module, function, arity} | calls]}
      end

      assert {:ok, functions, _, _, _, calls} =
               core_translate(
                 Lynx.Support.Depth.List,
                 definitions,
                 [{:depth, 1}],
                 callback,
                 %{},
                 [],
                 dispatch
               )

      # Only the cut off impl_for!/1 calls impl_for/1, so it is not reached.
      assert Enum.sort(Map.keys(functions)) == [{:"Lynx.Support.Depth.depth", 1}, {:depth, 1}]
      assert {Lynx.Support.Depth, :impl_for!, 1} in calls
    end
  end

  test "returns annotated binary reasons for unsupported Core during translation" do
    anno = [{:file, ~c"example.erl"}, {7, 3}]
    body = :cerl.ann_c_primop(anno, :cerl.c_atom(:unsupported), [])
    assert {:error, ^anno, reason} = translate(definitions([definition(:entry, body)]))
    assert reason =~ "unsupported Core expression:"
    assert reason =~ "unsupported"
  end

  test "dynamic targets join the function table" do
    body =
      :cerl.c_call(:cerl.c_atom(:erlang), :cerl.c_atom(:apply), [
        :cerl.c_var(:M),
        :cerl.c_atom(:f),
        :cerl.c_nil()
      ])

    callback = fn _, _, _, _, _, funs -> {{:pure, true}, funs, []} end

    assert {:ok, _, _, _, funs, _} =
             core_translate(
               :example,
               definitions([definition(:entry, body)]),
               [{:entry, 1}],
               callback,
               %{},
               [{:other, :target, 2}]
             )

    assert %{
             {:other, :target, 2} => %{
               module: :example,
               name: {:"other:target", 2},
               captures: []
             }
           } = funs
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
        callee =
          case Map.get(purity, {module, function, arity}, :pure) do
            {_purity, _dispatches} = callee -> callee
            purity -> {purity, false}
          end

        {callee, funs, [{module, function, arity, span_anno} | calls]}
      end
    end

    case core_translate(:example, definitions, [{:entry, 1}], callback, translated) do
      {:ok, functions, _literals, _laws, _funs, calls} -> {:ok, functions, calls}
      {:error, _, _} = error -> error
    end
  end

  # Translates roots starting from an empty literal pool and function registry.
  defp core_translate(
         module,
         definitions,
         roots,
         callback,
         translated \\ %{},
         dynamic \\ [],
         dispatch \\ :none
       ) do
    :lynx_core_to_leanj.translate(
      module,
      definitions,
      roots,
      translated,
      %{},
      %{},
      [],
      dynamic,
      {[], callback},
      dispatch
    )
  end

  defp translate_law(definitions) do
    callback = fn _, _, _, _, _, _ -> :local end

    assert {:ok, functions, %{}, laws, %{}, []} =
             core_translate(:example, definitions, [{:entry, 1}], callback)

    {laws, functions}
  end

  defp beam_core(beam) do
    {:ok, {module, [debug_info: {:debug_info_v1, backend, data}]}} =
      :beam_lib.chunks(beam, [:debug_info])

    {:ok, core} = backend.debug_info(:core_v1, module, data, [])
    core
  end

  defp protocol_definitions(beam), do: :lynx_core_to_leanj.to_definitions(beam_core(beam))

  # Translates protocol functions, treating calls to other modules as pure.
  defp translate_protocol(protocol, roots) do
    definitions = protocol_definitions(:code.which(protocol))
    callback = fn calls, _, _, _, _, funs -> {{:pure, false}, funs, calls} end

    assert {:ok, functions, _, _, _, _} =
             core_translate(protocol, definitions, roots, callback)

    functions
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
