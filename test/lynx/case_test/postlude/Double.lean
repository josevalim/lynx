module
public import Elixir.Lynx.CaseTest.Postludes
@[expose] public section

namespace Elixir.Lynx.CaseTest.Postludes

theorem double_integer (n : Int) : «double/1» (.integer n) = .ok (.integer (n + n)) := by
  simp [«double/1»]

end Elixir.Lynx.CaseTest.Postludes
