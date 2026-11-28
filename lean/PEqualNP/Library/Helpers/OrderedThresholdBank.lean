import PEqualNP.Library.Helpers.FiniteGateBank
import PEqualNP.Library.Helpers.MarkedInversionFloor

namespace PEqualNP.OrderedThresholdBank

open FiniteGateBank

variable {X : Type} {n : Nat}

def high (r : X → Nat) (i : Nat) (x : X) := decide (i ≤ r x)
def low (r : X → Nat) (i : Nat) (x : X) := decide (r x < i)

/-- Complement an already available sorted bank. The old wires remain usable.
Only the number of thresholds enters the binary-gate budget. -/
theorem decode (raw : X → List Bool) (width : ∀ x, (raw x).length=n) (b k : Nat)
    (room : k < 2^b) (r : X → Nat) (bound : ∀ x, r x≤k) (p : Net n)
    (zero : p.has raw (fun _ => false)) (known : ∀ i : Nat, 0 < i → i ≤ k → p.has raw (high r i)) :
    ∃ q, Grow raw p q (4*k+b) b ∧ ∀ i : Nat, 0 < i → i ≤ k → q.has raw (low r i) := by
  induction b generalizing k r p with
  | zero =>
    have : k=0 := by simpa using room
    subst k
    exact ⟨p,by simpa using start raw p,by omega⟩
  | succ b ih =>
    let a := k/2
    let m := a+1
    let rem (x : X) := if r x < m then r x else r x-m
    have small : k < 2*m := by dsimp [m,a]; omega
    have rem_le (x) : rem x≤a := by
      have := bound x
      dsimp [rem,m,a] at *
      split <;> omega
    have limited : a < 2^b := by dsimp [a]; rw [pow_succ] at room; omega
    have avail (i) (pos : 0 < i) : p.has raw (high r i) := by
      by_cases le : i≤k
      · exact known i pos le
      · convert zero using 2 with x
        simp [high,show ¬i≤r x by have := bound x; omega]
    obtain ⟨p₁,g₁,hneg⟩ := invert width p (high r m) (avail m (by dsimp [m]; omega))
    let ids := List.range a
    obtain ⟨p₂,g₂,hrem⟩ := batch (raw:=raw) p₁ ids (fun j => high rem (j+1)) 2 0 (by
      intro j hj q keep
      have index : j < a := List.mem_range.mp hj
      obtain ⟨u,gu,band⟩ := binary width q _ _ (keep _ hneg) (keep _ (g₁.1 _ (avail (j+1) (by omega)))) true
      obtain ⟨v,gv,bor⟩ := binary width u _ _ band (gu.1 _ (keep _ (g₁.1 _ (avail (m+(j+1)) (by omega))))) false
      refine ⟨v,chain gu gv,?_⟩
      convert bor using 2 with x
      have := bound x
      apply Bool.eq_iff_iff.mpr
      simp only [high,rem,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
        decide_eq_false_iff_not,ite_true,ite_false,Bool.false_eq_true]
      dsimp [m] at *
      split <;> omega)
    have residual (i) (pos : 0 < i) (le : i≤a) : p₂.has raw (high rem i) := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact hrem j (List.mem_range.mpr (by omega))
    obtain ⟨p₃,g₃,remneg⟩ := ih a limited rem rem_le p₂ (g₂.1 _ (g₁.1 _ zero)) residual
    have g123 := chain (chain g₁ g₂) g₃
    have mid := g₃.1 _ (g₂.1 _ hneg)
    obtain ⟨q,g₄,outs⟩ := batch (raw:=raw) p₃ (List.range k) (fun j => low r (j+1)) 1 0 (by
      intro j hj u keep
      have jk : j < k := List.mem_range.mp hj
      by_cases below : j+1 < m
      · have le : j+1≤a := by dsimp [m] at below; omega
        obtain ⟨v,g,h⟩ := binary width u _ _ (keep _ mid) (keep _ (remneg (j+1) (by omega) le)) true
        refine ⟨v,g,?_⟩
        convert h using 2 with x
        apply Bool.eq_iff_iff.mpr
        simp only [low,high,rem,ite_true,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
        split <;> omega
      · by_cases eq : j+1=m
        · refine ⟨u,allowance (start raw u) (by decide : 0≤1),?_⟩
          convert keep _ mid using 2 with x
          apply Bool.eq_iff_iff.mpr
          simp only [high,low,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
          omega
        · have above : m < j+1 := by omega
          have ix : j+1-m≤a := by dsimp [m,a] at *; omega
          obtain ⟨v,g,h⟩ := binary width u _ _ (keep _ mid) (keep _ (remneg (j+1-m) (by omega) ix)) false
          refine ⟨v,g,?_⟩
          convert h using 2 with x
          apply Bool.eq_iff_iff.mpr
          simp only [low,high,rem,Bool.false_eq_true,ite_false,Bool.or_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
          split <;> omega)
    have gr := chain g123 g₄
    simp only [ids,List.length_range,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at gr
    refine ⟨q,?_,?_⟩
    · have gr' := allowance gr (show 1 + a*2 + (4*a+b) + k ≤ 4*k+(b+1) by dsimp [a]; omega)
      simpa [Nat.add_comm 1 b] using gr'
    · intro i pos le
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
      exact outs j (List.mem_range.mpr (by omega))

end PEqualNP.OrderedThresholdBank
