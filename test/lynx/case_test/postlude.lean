namespace Elixir.Lynx.CaseTest.Postludes

theorem double_integer (n : Int) : «double/1» (.integer n) = .ok (.integer (n + n)) := by
  simp [«double/1»]
