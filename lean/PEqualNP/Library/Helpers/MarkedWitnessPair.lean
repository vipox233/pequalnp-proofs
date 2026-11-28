import Mathlib
import PEqualNP.Defs.NotBracket
import PEqualNP.Defs.MetaComplexity
import PEqualNP.Defs.NestedCoverCircuit

namespace PEqualNP.MarkedWitnessPair
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

private def both (i j : Nat) : Gate := ⟨.and,[i,j]⟩
private def neg (i : Nat) : Gate := ⟨.not,[i]⟩

def separate {n : Nat} (a b c : Fin n) : Circuit :=
  ⟨[both a b, neg (n+2), both b c, neg (n+4)], n+3⟩

def shared {n : Nat} (a b c : Fin n) : Circuit :=
  ⟨[both a b, both (n+2) c, neg (n+3), both (n+4) c, both (n+4) a], n+5⟩

private theorem raw {n : Nat} (x : Fin n → Bool) (tail : List Bool) (i : Fin n) :
    (List.ofFn x ++ tail).getD i.val false = x i := by
  rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,i.isLt]

private theorem rawOption {n : Nat} (x : Fin n → Bool) (tail : List Bool) (i : Fin n) :
    ((List.ofFn x ++ tail)[i.val]?).getD false = x i := by
  simpa only [List.getD_eq_getElem?_getD] using raw x tail i

private theorem extra {n : Nat} (x : Fin n → Bool) (tail : List Bool) (j : Nat) :
    (List.ofFn x ++ tail).getD (n+j) false = tail.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem separate_legal {n} (a b c : Fin n) :
    FanInTwo (separate a b c) ∧ ReadsBack (n+2) (separate a b c) ∧
    (separate a b c).size = 4 ∧ NotBracket.notCount (separate a b c) = 2 := by
  refine ⟨?_,?_,rfl,rfl⟩
  · simp [FanInTwo,separate,both,neg]
  · intro j bound i hi
    change j<4 at bound
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    interval_cases j <;> simp [gateAt,separate,both,neg] at hi <;> omega

theorem shared_legal {n} (a b c : Fin n) :
    FanInTwo (shared a b c) ∧ ReadsBack (n+2) (shared a b c) ∧
    (shared a b c).size = 5 ∧ NotBracket.notCount (shared a b c) = 1 := by
  refine ⟨?_,?_,rfl,rfl⟩
  · simp [FanInTwo,shared,both,neg]
  · intro j bound i hi
    change j<5 at bound
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    interval_cases j <;> simp [gateAt,shared,both,neg] at hi <;> omega

theorem separate_eval {n} (a b c : Fin n) (x : Fin n → Bool)
    (ab : x a = true ∨ x b = true) (bc : x b = true ∨ x c = true) :
    let w := (separate a b c).wires (List.ofFn x ++ [false,true])
    w.getD (n+3) false = xor (x a) (x b) ∧ w.getD (n+5) false = xor (x b) (x c) := by
  simp [separate,Circuit.wires,both,neg,GateOp.eval,List.append_assoc,raw,rawOption,extra]
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp_all

theorem shared_eval {n} (a b c : Fin n) (x : Fin n → Bool)
    (ab : x a = true ∨ x b = true) (bc : x b = true ∨ x c = true)
    (ac : x a = true ∨ x c = true) :
    let w := (shared a b c).wires (List.ofFn x ++ [false,true])
    w.getD (n+5) false = xor (x a) (x b) ∧ w.getD (n+6) false = xor (x b) (x c) := by
  simp [shared,Circuit.wires,both,neg,GateOp.eval,List.append_assoc,raw,rawOption,extra]
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp_all

/-- The constructive direction for two marked edge outputs on vertex covers. -/
theorem upper {n : Nat} (G : Finset (Fin n × Fin n)) (a b c : Fin n)
    (ab : (a,b) ∈ G ∨ (b,a) ∈ G) (bc : (b,c) ∈ G ∨ (c,b) ∈ G) (s r : Nat)
    (budget : (4 ≤ s ∧ 2 ≤ r) ∨ (((a,c) ∈ G ∨ (c,a) ∈ G) ∧ 5 ≤ s ∧ 1 ≤ r)) :
    ∃ (C : Circuit) (p q : Fin (n+2+C.size)), FanInTwo C ∧ ReadsBack (n+2) C ∧
      C.output = p.val ∧ C.size ≤ s ∧ NotBracket.notCount C ≤ r ∧
      ∀ x : Fin n → Bool, (∀ e ∈ G, x e.1=true ∨ x e.2=true) →
        let w := C.wires (List.ofFn x ++ [false,true])
        w.getD p.val false = xor (x a) (x b) ∧ w.getD q.val false = xor (x b) (x c) := by
  have edge {u v : Fin n} (adj : (u,v) ∈ G ∨ (v,u) ∈ G) (x : Fin n → Bool)
      (cover : ∀ e ∈ G, x e.1=true ∨ x e.2=true) : x u=true ∨ x v=true := by
    rcases adj with h|h
    · exact cover _ h
    · exact (cover _ h).symm
  rcases budget with ⟨sz,nv⟩|⟨ac,sz,nv⟩
  · obtain ⟨fan,back,hs,hr⟩ := separate_legal a b c
    refine ⟨separate a b c,⟨n+3,by rw [hs]; omega⟩,⟨n+5,by rw [hs]; omega⟩,
      fan,back,rfl,hs.trans_le sz,hr.trans_le nv,?_⟩
    exact fun x cover => separate_eval a b c x (edge ab x cover) (edge bc x cover)
  · obtain ⟨fan,back,hs,hr⟩ := shared_legal a b c
    refine ⟨shared a b c,⟨n+5,by rw [hs]; omega⟩,⟨n+6,by rw [hs]; omega⟩,
      fan,back,rfl,hs.trans_le sz,hr.trans_le nv,?_⟩
    exact fun x cover => shared_eval a b c x (edge ab x cover) (edge bc x cover) (edge ac x cover)

end PEqualNP.MarkedWitnessPair
