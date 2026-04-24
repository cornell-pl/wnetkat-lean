module

public import WeightedNetKAT.WeightedSemiring.Instances
public import Lake.Util.Log

@[expose] public section

namespace WeightedNetKAT

namespace Perf

structure Marker where
  name : Option String
  ns : ℕ

def mark (name : Option String := none) : IO Marker := do
  let m : Marker := ⟨name, ← IO.monoNanosNow⟩
  return m

structure Duration where
  ns : ℕ

instance : ToString Duration where
  toString d :=
    let nano := 1
    let micr := nano * 1000
    let mili := micr * 1000
    let full := mili * 1000

    let d := d.ns

    if d < micr then
      s!"{d}ns"
    else if d < mili then
      s!"{d / micr}µs"
    else if d < full then
      s!"{d / mili}ms"
    else
      s!"{Float.ofNat d / Float.ofNat full}s"

def Marker.since (m : Marker) : IO Duration := do
  let d : Duration := ⟨(← IO.monoNanosNow) - m.ns⟩
  let s := if let some name := m.name then
    s!"    ← ⏱️  {name} {d}"
  else
    s!"    ← ⏱️  {d}"
  println! "{Lake.Ansi.chalk "90" s}"

  return d

def time {α : Type} (name : String) (f : Unit → α) : IO α := do
  let m ← mark name
  let v ← IO.lazyPure f
  let _ ← m.since
  return v
def timeIO {α : Type} (name : String) (f : Unit → IO α) : IO α := do
  let m ← mark name
  let v ← f ()
  let _ ← m.since
  return v

end Perf
