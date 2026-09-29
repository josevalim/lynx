module Foxy.Float

open FStar.Mul
// Finite IEEE-754 binary64 fields. No host floats or external axioms.
let fraction_limit : int = 4503599627370496
let significand_limit : int = 9007199254740992

type t = { negative: bool; exponent: e:nat{e <= 2046}; fraction: f:nat{f < fraction_limit} }

let rec pow2 (n:nat) : Tot pos (decreases n) =
  match n with | 0 -> 1 | _ -> 2 * pow2 (n - 1)

// Every binary64 value is an integer multiple of 2^-1074.
let magnitude (x:t) : Tot nat =
  match x.exponent with
  | 0 -> x.fraction
  | _ -> (fraction_limit + x.fraction) * pow2 (x.exponent - 1)

let units (x:t) : Tot int =
  let n = magnitude x in if x.negative then -n else n

let zero (negative:bool) : t = { negative; exponent=0; fraction=0 }

let make (negative:bool) (exponent:int) (fraction:int) : Tot (option t) =
  if exponent >= 0 && exponent <= 2046 && fraction >= 0 && fraction < fraction_limit
  then Some {negative; exponent; fraction} else None

// Shift needed to retain at most 53 significant bits.
let rec shift (n:nat) : Tot nat (decreases n) =
  if n < significand_limit then 0 else 1 + shift (n / 2)

let round_units (negative:bool) (n:nat) : Tot (option t) =
  if n < fraction_limit then make negative 0 n else
  let s = shift n in
  let divisor = pow2 s in
  let q = n / divisor in
  let r = n % divisor in
  let rounded = if 2*r > divisor || (2*r = divisor && q % 2 = 1) then q+1 else q in
  if rounded = significand_limit then make negative (s+2) 0
  else make negative (s+1) (rounded-fraction_limit)

let of_int (n:int) : Tot (option t) =
  round_units (n < 0) ((if n < 0 then -n else n) * pow2 1074)

let add (a:t) (b:t) : Tot (option t) =
  let n = units a + units b in
  let negative = if n = 0 then a.negative && b.negative else n < 0 in
  round_units negative (if n < 0 then -n else n)

let of_bits (bits:nat) : Tot (option t) =
  if bits >= 18446744073709551616 then None else
  let negative = bits >= 9223372036854775808 in
  let magnitude = bits % 9223372036854775808 in
  make negative (magnitude / fraction_limit) (magnitude % fraction_limit)

let to_bits (x:t) : Tot int =
  (if x.negative then 9223372036854775808 else 0) + x.exponent * fraction_limit + x.fraction

let bits_roundtrip (x:t) : Lemma (of_bits (to_bits x) == Some x) = ()
