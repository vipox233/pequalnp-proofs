import PEqualNP.Library.Helpers.PivotDependencies

namespace PEqualNP.PivotReports

open PivotDependencies
variable {n m : Nat}

def report (Q : Fin n → Word m) (v : Word n) : Word m :=
  fun j => ∑ i, v i * Q i j

def pull (Q : Fin n → Word m) (S : Finset (Fin m)) :=
  Finset.univ.filter (fun i => parity S (Q i) ≠ 0)

theorem project (Q : Fin n → Word m) (S : Finset (Fin m)) (v : Word n) :
    parity S (report Q v) = parity (pull Q S) v := by
  classical
  unfold parity report
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_coe_sort]
  unfold pull
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  change v i * parity S (Q i) = _
  generalize parity S (Q i) = b
  by_cases hz : b = 0
  · simp [hz]
  · have ho : b = 1 := by fin_cases b <;> first | rfl | exact (hz rfl).elim
    simp [ho]

private theorem inversion (F : Word n → Word m) (v : Word m) :
    (2:ℤ)^m * (Nat.card {x : Word n // F x = v} : ℤ) =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset,
        (∑ x : Word n, sign (parity S (F x))) * sign (parity S v) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [point]
  simp [Nat.card_eq_fintype_card,Fintype.card_subtype,mul_comm]
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem criterion (D : Fin n → Finset (Fin n)) (Q : Fin n → Word m) :
    let uniform := ∀ T, Local D T → ∀ v : Word m,
      2^m * Nat.card {x : Word n // report Q (output T x) = v} = 2^n
    let onto := ∀ T, Local D T → Function.Surjective (fun x => report Q (output T x))
    let noMask := ∀ S : Finset (Fin m), S.Nonempty → ¬Covered D (pull Q S)
    (uniform ↔ noMask) ∧ (onto ↔ noMask) := by
  classical
  dsimp only
  have exactCount (h : ∀ S : Finset (Fin m), S.Nonempty → ¬Covered D (pull Q S))
      (T : Tail n) (loc : Local D T) (v : Word m) :
      2^m * Nat.card {x : Word n // report Q (output T x) = v} = 2^n := by
    have hZ := inversion (fun x => report Q (output T x)) v
    rw [Finset.sum_eq_single (∅ : Finset (Fin m))] at hZ
    · simp [parity,sign] at hZ
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast hZ
    · intro S _ hne
      simp_rw [project]
      rw [characterCount,balanced (h S (Finset.nonempty_iff_ne_empty.mpr hne)) T loc]
      simp
    · simp
  have ontoOfCount (h : ∀ T, Local D T → ∀ v : Word m,
      2^m * Nat.card {x : Word n // report Q (output T x) = v} = 2^n)
      (T : Tail n) (loc : Local D T) (v : Word m) : ∃ x, report Q (output T x) = v := by
    have hn : 0 < Nat.card {x : Word n // report Q (output T x) = v} := by
      by_contra! hz
      have ht := h T loc v
      rw [Nat.eq_zero_of_le_zero hz,mul_zero] at ht
      exact (by positivity : 0 < 2^n).ne ht
    obtain ⟨x,hx⟩ := (Nat.card_pos_iff.mp hn).1
    exact ⟨x,hx⟩
  have noOfOnto (h : ∀ T, Local D T → Function.Surjective (fun x => report Q (output T x)))
      (S : Finset (Fin m)) (hn : S.Nonempty) (covered : Covered D (pull Q S)) : False := by
    obtain ⟨i,hi⟩ := hn
    obtain ⟨T,loc,_,locked⟩ := lock covered (0 : Word n)
    let v : Word m := fun j => if i=j then 1 else 0
    obtain ⟨x,hx⟩ := h T loc v
    have same := project Q S (output T x)
    change report Q (output T x) = v at hx
    rw [hx,locked] at same
    unfold parity at same
    rw [Finset.sum_coe_sort,Finset.sum_coe_sort] at same
    simpa [v,hi] using same
  exact ⟨⟨fun h => noOfOnto (ontoOfCount h),exactCount⟩,⟨noOfOnto,fun h => ontoOfCount (exactCount h)⟩⟩

end PEqualNP.PivotReports
