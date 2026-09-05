import Lynx

def main : IO Unit :=
  IO.println s!"{repr (Lynx.Examples.TermSum.sumTerm
    (Lynx.Examples.TermSum.encodeIntList [1, 2, 3]))}"
