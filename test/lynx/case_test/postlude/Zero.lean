module
public import Double
@[expose] public section

namespace Elixir.Lynx.CaseTest.Postludes

theorem double_zero : «double/1» (.integer 0) = .ok (.integer 0) := by
  simpa using double_integer 0

end Elixir.Lynx.CaseTest.Postludes
