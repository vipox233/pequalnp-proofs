import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Library.Helpers.MarkedInversionFloor

namespace PEqualNP.MarkedTriangleDecision
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def cover (x : Fin 3 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

def Fits (s r : Nat) : Prop :=
  ∃ (C : Circuit) (p q : Fin (5+C.size)),
    FanInTwo C ∧ ReadsBack 5 C ∧ C.output < 5+C.size ∧
    C.size ≤ s ∧ NotBracket.notCount C ≤ r ∧
    ∀ x : Fin 3 → Bool,
      let w := List.ofFn x ++ [false,true]
      C.eval w = cover x ∧ (cover x = true →
        (C.wires w).getD p.val false = xor (x 0) (x 1) ∧
        (C.wires w).getD q.val false = xor (x 1) (x 2))

private def conj (i j : Nat) : Gate := ⟨.and,[i,j]⟩
private def disj (i j : Nat) : Gate := ⟨.or,[i,j]⟩
private def neg (i : Nat) : Gate := ⟨.not,[i]⟩

def seven : Circuit :=
  ⟨[conj 0 1, conj 0 2, conj 1 2, disj 5 6, disj 8 7, neg 5, neg 7],9⟩

def eight : Circuit :=
  ⟨[conj 0 1, conj 5 2, neg 6, conj 7 2, conj 7 0, disj 0 1, conj 10 2, disj 5 11],12⟩

private theorem three (x : Fin 3 → Bool) : List.ofFn x = [x 0,x 1,x 2] := rfl

theorem seven_fits : Fits 7 2 := by
  refine ⟨seven,⟨10,by decide⟩,⟨11,by decide⟩,?_,?_,by decide,by decide,by decide,?_⟩
  · simp [seven,FanInTwo,conj,disj,neg]
  · intro j hj i hi
    change j<7 at hj
    interval_cases j <;> simp [gateAt,seven,conj,disj,neg] at hi <;> omega
  · intro x
    rw [three]
    cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;>
      simp [cover,h₀,h₁,h₂] <;> decide

theorem eight_fits : Fits 8 1 := by
  refine ⟨eight,⟨8,by decide⟩,⟨9,by decide⟩,?_,?_,by decide,by decide,by decide,?_⟩
  · simp [eight,FanInTwo,conj,disj,neg]
  · intro j hj i hi
    change j<8 at hj
    interval_cases j <;> simp [gateAt,eight,conj,disj,neg] at hi <;> omega
  · intro x
    rw [three]
    cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;>
      simp [cover,h₀,h₁,h₂] <;> decide

theorem mono {s r t u : Nat} (h : Fits s r) (sz : s≤t) (iv : r≤u) : Fits t u := by
  obtain ⟨C,p,q,fan,back,valid,size,count,works⟩ := h
  exact ⟨C,p,q,fan,back,valid,size.trans sz,count.trans iv,works⟩

theorem positive {s r : Nat} (h : Fits s r) : 1 ≤ r := by
  obtain ⟨C,p,q,fan,_,_,_,count,works⟩ := h
  let G : Finset (Fin 3 × Fin 3) := {(0,1),(1,2),(0,2)}
  let H : Finset (Fin 3 × Fin 3) := {(0,1)}
  let S : Finset (Fin 3) := {0}
  have floor := MarkedInversionFloor.lower G H (by decide) S (by decide) (by decide) C fan
    (fun _ => p) (by
      intro x val e
      have edge₁ := val (0,1) (by decide)
      have edge₂ := val (1,2) (by decide)
      have edge₃ := val (0,2) (by decide)
      have hc : cover x = true := by
        cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;> simp_all [cover]
      have he : e.val = (0,1) := Finset.mem_singleton.mp e.property
      simpa [he] using ((works x).2 hc).1)
  by_contra! bad
  have z : NotBracket.notCount C = 0 := by omega
  simpa [S,z] using floor

/-- Two fixed physical obstructions suffice for the whole unbounded resource statement. -/
theorem classify (six : ¬ Fits 6 6) (one : ¬ Fits 7 1) (s r : Nat) :
    Fits s r ↔ (7 ≤ s ∧ 2 ≤ r) ∨ (8 ≤ s ∧ 1 ≤ r) := by
  constructor
  · intro h
    have nz := positive h
    have total : 7 ≤ s := by
      by_contra! bad
      apply six
      obtain ⟨C,p,q,fan,back,valid,size,_,works⟩ := h
      have bound : NotBracket.notCount C ≤ C.size := List.length_filter_le ..
      exact ⟨C,p,q,fan,back,valid,by omega,by omega,works⟩
    by_cases rr : 2 ≤ r
    · exact Or.inl ⟨total,rr⟩
    · refine Or.inr ⟨?_,nz⟩
      by_contra! bad
      exact one (mono h (by omega) (by omega))
  · rintro (⟨a,b⟩|⟨a,b⟩)
    · exact mono seven_fits a b
    · exact mono eight_fits a b

end PEqualNP.MarkedTriangleDecision
