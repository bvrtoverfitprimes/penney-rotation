import Std.Data.HashMap

namespace Rotation.Cert

def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap fun p =>
      (List.range (p.length + 1)).map fun i => p.take i ++ x :: p.drop i

def standardize (xs : List Nat) : List Nat :=
  xs.map fun x => (xs.filter (· < x)).length

def rot (a : List Nat) : List Nat := a.getLast! :: a.dropLast

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def overlap (u v : List Nat) (d : Nat) : Nat := Id.run do
  let k := u.length
  let shared := ((u.drop d).zip (v.take (k - d))).mergeSort (fun p q => p.1 ≤ q.1)
  let mut oldU : Int := -1
  let mut oldV : Int := -1
  let mut ways := 1
  for (x, y) in shared ++ [(k, k)] do
    if (y : Int) ≤ oldV then return 0
    let left := ((x : Int) - oldU - 1).toNat
    let right := ((y : Int) - oldV - 1).toNat
    ways := ways * binom (left + right) left
    oldU := x
    oldV := y
  return ways

def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else lexLt xs ys

def reps (k : Nat) : List (List Nat) :=
  (perms (List.range k)).filter fun a => lexLt a (a.map fun x => k - 1 - x)

def Hk (k : Nat) : Rat := (8 * ((k : Rat) - 1)) / ((fact k : Rat) - 2 * ((k : Rat) - 1))

def pairBound (a : List Nat) : Rat := Id.run do
  let k := a.length
  let b := rot a
  let init : Int := (overlap a a 1 : Int) + overlap b a 1 - overlap a b 1 - overlap b b 1
  let mut lower : Rat := (init : Rat) / ((k : Rat) + 1)
  for d in [2:k] do
    lower := lower - (((overlap a b d + overlap b b d) * fact k : Nat) : Rat) / (fact (k + d) : Rat)
  return lower - Hk k

def minOf (xs : List Rat) : Rat := xs.foldl min (xs.headD 0)

abbrev Key := List Nat × Nat × Nat

def coefficients (a : List Nat) (maxN : Nat) : Array Int × Array (Array Nat) := Id.run do
  let k := a.length
  let b := rot a
  let len := maxN - k + 1
  let mut states : Std.HashMap Key Nat := {}
  for p in [a, b] do
    let key : Key := (p.tail, 0, 1)
    states := states.insert key (states.getD key 0 + 1)
  let mut coeffs : Array Int := Array.replicate len 0
  let mut arrivals : Array (Array Nat) := Array.replicate len (Array.replicate k 0)
  let mask := 2 ^ k - 1
  for n in [k:maxN] do
    let start := n + 1 - k
    let mut nxt : Std.HashMap Key Nat := {}
    for ((tail, age, bits), count) in states.toList do
      let gap := age + 1
      if gap < k then
        for rank in [0:n+1] do
          let window := tail.map (fun x => if x ≥ rank then x + 1 else x) ++ [rank]
          let pat := standardize window
          let isA := pat == a
          let isB := pat == b
          if isA || isB then
            let newBit := (bits >>> (k - 1)) &&& 1
            let signed : Int := ((bits &&& 1 : Nat) : Int) - (newBit : Int)
            let sgn : Int := if isA then 1 else -1
            coeffs := coeffs.modify start (· + (count : Int) * signed * sgn)
            arrivals := arrivals.modify start (fun row => row.modify gap (· + count))
            let key : Key := (window.tail, 0, ((bits <<< 1) ||| newBit) &&& mask)
            nxt := nxt.insert key (nxt.getD key 0 + count)
          else
            let newBit := bits &&& 1
            if gap < k - 1 then
              let key : Key := (window.tail, gap, ((bits <<< 1) ||| newBit) &&& mask)
              nxt := nxt.insert key (nxt.getD key 0 + count)
    states := nxt
  return (coeffs, arrivals)

def certificate (a : List Nat) (h : Nat) : Rat := Id.run do
  let k := a.length
  let R := h + 2 * k - 2
  let N := k + R - 1
  let (cs, arr) := coefficients a N
  let mut prefixP : Rat := 0
  for i in [h:h+k-1] do
    for g in [i-h+1:k] do
      prefixP := prefixP + ((arr[i]!)[g]! : Rat) / (fact (k + i) : Rat)
  let mut partialS : Rat := 0
  for d in [0:cs.size] do
    partialS := partialS + (cs[d]! : Rat) / (fact (k + d) : Rat)
  let bound : Rat := (4 * ((k : Rat) - 1)) / ((fact k : Rat) - 2 * ((k : Rat) - 1)) * prefixP
  return (partialS - bound) * (fact k : Rat)

def check67 : Bool :=
  (reps 6).length == 360 && (reps 7).length == 2520 &&
  minOf ((reps 6).map pairBound) == (5539 : Rat) / 89460 &&
  minOf ((reps 7).map pairBound) == (4332253 : Rat) / 51768288 &&
  (reps 6).all (fun a => 0 < pairBound a) && (reps 7).all (fun a => 0 < pairBound a)

def check345 : Bool :=
  (reps 3).length == 3 && (reps 4).length == 12 && (reps 5).length == 60 &&
  minOf ((reps 3).map (certificate · 13)) == (10651931797 : Rat) / 200559744000 &&
  minOf ((reps 4).map (certificate · 4)) == (8812049 : Rat) / 129729600 &&
  minOf ((reps 5).map (certificate · 1)) == (98321 : Rat) / 1235520 &&
  (reps 3).all (fun a => 0 < certificate a 13) &&
  (reps 4).all (fun a => 0 < certificate a 4) &&
  (reps 5).all (fun a => 0 < certificate a 1)

def clusterWeight (k : Nat) (occ : List Bool) : Int := Id.run do
  let n := occ.length
  let mut w : Array Int := Array.replicate n 0
  for t in [0:n] do
    if occ[t]! then
      if t == 0 then
        w := w.set! 0 (-1)
      else
        let mut s : Int := 0
        for j in [t + 1 - k:t] do
          s := s + w[j]!
        w := w.set! t (-s)
  return w[n - 1]!

def directCoeff (a : List Nat) (n : Nat) : Int :=
  let k := a.length
  let b := rot a
  (perms (List.range n)).foldl (fun acc p =>
    let occ := (List.range (n - k + 1)).map fun i =>
      let pat := standardize ((p.drop i).take k)
      pat == a || pat == b
    let last := standardize (p.drop (n - k))
    let sgn : Int := if last == a then 1 else if last == b then -1 else 0
    acc + sgn * clusterWeight k occ) 0

def overlapTally (k d : Nat) : Std.HashMap (List Nat × List Nat) Nat :=
  (perms (List.range (k + d))).foldl (fun m p =>
    let key := (standardize (p.take k), standardize ((p.drop d).take k))
    m.insert key (m.getD key 0 + 1)) {}

def checkOverlap (k : Nat) : Bool :=
  let pats := perms (List.range k)
  (List.range (k - 1)).all fun d0 =>
    let d := d0 + 1
    let tally := overlapTally k d
    pats.all fun u => pats.all fun v => overlap u v d == tally.getD (u, v) 0

def checkRecurrence (k maxN : Nat) : Bool :=
  (perms (List.range k)).all fun a =>
    let (cs, _) := coefficients a maxN
    (List.range (maxN - k + 1)).all fun i => cs[i]! == directCoeff a (k + i)

def firstCounts (a : List Nat) (n : Nat) : Nat × Nat × Nat :=
  let k := a.length
  let b := rot a
  (perms (List.range n)).foldl (fun (acc : Nat × Nat × Nat) p =>
    let first := (List.range (n + 1 - k)).find? fun i =>
      let pat := standardize ((p.drop i).take k)
      pat == a || pat == b
    match first with
    | none => (acc.1 + 1, acc.2.1, acc.2.2)
    | some i =>
      if i + k == n then
        if standardize ((p.drop i).take k) == a then (acc.1, acc.2.1 + 1, acc.2.2)
        else (acc.1, acc.2.1, acc.2.2 + 1)
      else acc) (0, 0, 0)

def checkFactorization (a : List Nat) (maxN : Nat) : Bool :=
  let k := a.length
  let (cs, _) := coefficients a maxN
  let counts := (List.range (maxN + 1)).map (firstCounts a)
  let alpha := counts.map (·.1)
  (List.range (maxN + 1)).all fun n =>
    let c := counts[n]!
    let lhs : Int := (c.2.2 : Int) - (c.2.1 : Int)
    let rhs : Int := ((List.range (n + 1)).filter (k ≤ ·)).foldl (fun s j =>
      s + (binom n j : Int) * (alpha[n - j]! : Int) * cs[j - k]!) 0
    lhs == rhs

end Rotation.Cert
