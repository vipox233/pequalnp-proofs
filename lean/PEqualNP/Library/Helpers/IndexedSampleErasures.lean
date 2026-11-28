import PEqualNP.Defs

namespace PEqualNP.IndexedSampleErasures

variable {I X : Type*} [Fintype I] [DecidableEq I] [DecidableEq X]

def support (row : I → X) := Finset.univ.image row

def fiber (row : I → X) (x : X) := Finset.univ.filter (fun i => row i=x)

def survivors (row : I → X) (lost : Finset I) := (Finset.univ \ lost).image row

private theorem supports (row : I → X) (lost : Finset I) : survivors row lost ⊆ support row := by
  intro x hx
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

private def forced (row : I → X) (keep : Finset X) :=
  Finset.univ.filter (fun i => row i ∉ keep)

private theorem exactSurvivors (row : I → X) (keep : Finset X) (sub : keep ⊆ support row) :
    survivors row (forced row keep) = keep := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simpa [forced] using (Finset.mem_sdiff.mp hi).2
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (sub hx)
    exact Finset.mem_image.mpr ⟨i, by simp [forced,hx], rfl⟩

private theorem forcedSubset (row : I → X) (lost : Finset I) :
    forced row (survivors row lost) ⊆ lost := by
  intro i hi
  by_contra live
  have inside : row i ∈ survivors row lost := Finset.mem_image_of_mem _ (by simp [live])
  exact (Finset.mem_filter.mp hi).2 inside

private theorem bill (row : I → X) (cost : I → Nat) (keep : Finset X) :
    ((support row \ keep).sum (fun x => (fiber row x).sum cost)) =
    (forced row keep).sum cost := by
  let gone := forced row keep
  have hmap : ∀ i ∈ gone, row i ∈ (support row \ keep) := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), (Finset.mem_filter.mp hi).2⟩
  calc
    _ = (support row \ keep).sum (fun x => (gone.filter (fun i => row i=x)).sum cost) := by
      apply Finset.sum_congr rfl
      intro x hx
      have eq : fiber row x = gone.filter (fun i => row i=x) := by
        ext i
        have out := (Finset.mem_sdiff.mp hx).2
        by_cases h : row i=x <;> simp [fiber,gone,forced,h,out]
      rw [eq]
    _ = _ := Finset.sum_fiberwise_of_maps_to hmap cost

/-- The cheapest deletion realizing a prescribed surviving support removes complete fibers. -/
theorem attainable (row : I → X) (cost : I → Nat) (keep : Finset X) (d : Nat) :
    (∃ lost : Finset I, lost.sum cost ≤ d ∧ survivors row lost = keep) ↔
    keep ⊆ support row ∧ (support row \ keep).sum (fun x => (fiber row x).sum cost) ≤ d := by
  rw [bill]
  constructor
  · rintro ⟨lost, budget, rfl⟩
    exact ⟨supports _ _, (Finset.sum_le_sum_of_subset (forcedSubset row lost)).trans budget⟩
  · rintro ⟨sub, budget⟩
    exact ⟨forced row keep, budget, exactSurvivors row keep sub⟩

/-- The survivor predicate may be arbitrary. Each index has its own nonnegative deletion cost. -/
theorem robust (row : I → X) (cost : I → Nat) (d : Nat) (holds : Finset X → Prop) :
    (∀ lost : Finset I, lost.sum cost ≤ d → holds (survivors row lost)) ↔
    ∀ keep ⊆ support row, (support row \ keep).sum (fun x => (fiber row x).sum cost) ≤ d → holds keep := by
  constructor
  · intro all keep sub budget
    obtain ⟨lost, cheap, rfl⟩ := (attainable row cost keep d).mpr ⟨sub,budget⟩
    exact all lost cheap
  · intro all lost budget
    have ok := (attainable row cost (survivors row lost) d).mp ⟨lost,budget,rfl⟩
    exact all _ ok.1 ok.2

/-- This is the indexed-erasure interface to the multiplicity criterion in L-lib-1449. -/
theorem copies (row : I → X) (d : Nat) (holds : Finset X → Prop) :
    (∀ lost : Finset I, lost.card ≤ d → holds (survivors row lost)) ↔
    ∀ removed : X → Nat, (support row).sum removed ≤ d →
      holds ((support row).filter (fun x => removed x < (fiber row x).card)) := by
  classical
  have r := robust row (fun _ => 1) d holds
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at r
  apply r.trans
  constructor
  · intro all removed budget
    let K := (support row).filter (fun x => removed x < (fiber row x).card)
    apply all K (Finset.filter_subset _ _)
    calc
      _ ≤ (support row \ K).sum removed := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨seen, out⟩ := Finset.mem_sdiff.mp hx
        exact Nat.le_of_not_gt (fun h => out (Finset.mem_filter.mpr ⟨seen,h⟩))
      _ ≤ _ := (Finset.sum_le_sum_of_subset Finset.sdiff_subset).trans budget
  · intro all K sub budget
    let removed (x : X) := if x ∈ K then 0 else (fiber row x).card
    have price : (support row).sum removed = (support row \ K).sum (fun x => (fiber row x).card) := by
      rw [Finset.sdiff_eq_filter]
      simp [removed,Finset.sum_filter]
    have remaining : (support row).filter (fun x => removed x < (fiber row x).card) = K := by
      ext x
      by_cases h : x∈K
      · have seen := sub h
        obtain ⟨i,_,hi⟩ := Finset.mem_image.mp seen
        have pos : 0 < (fiber row x).card := Finset.card_pos.mpr ⟨i, by simpa [fiber] using hi⟩
        simp [removed,h,seen,pos]
      · simp [removed,h]
    simpa only [remaining] using all removed (price.trans_le budget)


/-- The maximal failing sets are computed on the whole universe, independently of the bank. -/
theorem obstructionCover [Fintype X] (row : I → X) (cost : I → Nat) (d : Nat)
    (holds : Finset X → Prop) (mono : ∀ A B, A ⊆ B → holds A → holds B) :
    (∀ lost : Finset I, lost.sum cost ≤ d → holds (survivors row lost)) ↔
    ∀ B : Finset X, ¬holds B → (∀ T : Finset X, B ⊂ T → holds T) →
      d < (forced row B).sum cost := by
  classical
  constructor
  · intro ok B bad _
    by_contra! cheap
    apply bad
    refine mono (survivors row (forced row B)) B ?_ (ok _ cheap)
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    simpa [forced] using (Finset.mem_sdiff.mp hi).2
  · intro cuts lost cheap
    by_contra bad
    let live := survivors row lost
    let badSets := (Finset.univ : Finset (Finset X)).filter (fun B => live ⊆ B ∧ ¬holds B)
    have inside : live ∈ badSets := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, bad⟩
    obtain ⟨B, mem, largest⟩ := Finset.exists_max_image badSets Finset.card ⟨live,inside⟩
    obtain ⟨sub, fail⟩ := (Finset.mem_filter.mp mem).2
    have maximal (T : Finset X) (strict : B ⊂ T) : holds T := by
      by_contra no
      have hT : T ∈ badSets := Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub.trans (le_of_lt strict), no⟩
      exact (not_le_of_gt (Finset.card_lt_card strict)) (largest T hT)
    have subLost : forced row B ⊆ lost := by
      refine Finset.Subset.trans ?_ (forcedSubset row lost)
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => (Finset.mem_filter.mp hi).2 (sub h)⟩
    exact (not_le_of_gt (cuts B fail maximal)) ((Finset.sum_le_sum_of_subset subLost).trans cheap)

theorem criterion :
∀ (I X : Type) [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (row : I → X) (price : I → Nat) (d : Nat) (holds : Finset X → Prop),
  let A := Finset.univ.image row
  let F := fun x : X => Finset.univ.filter (fun i : I => row i=x)
  let K := fun Z : Finset I => (Finset.univ \ Z).image row
  (∀ B : Finset X, (∃ Z : Finset I, Z.sum price ≤ d ∧ K Z=B) ↔
    B ⊆ A ∧ (A \ B).sum (fun x => (F x).sum price) ≤ d) ∧
  ((∀ Z : Finset I, Z.card ≤ d → holds (K Z)) ↔ ∀ removed : X → Nat,
    A.sum removed ≤ d → holds (A.filter (fun x => removed x < (F x).card))) ∧
  ((∀ B C : Finset X, B ⊆ C → holds B → holds C) →
    ((∀ Z : Finset I, Z.sum price ≤ d → holds (K Z)) ↔
      ∀ B : Finset X, ¬holds B → (∀ C : Finset X, B ⊂ C → holds C) →
        d < (Finset.univ.filter (fun i : I => row i ∉ B)).sum price))
 := by
  intro I X _ _ _ _ row price d holds
  exact ⟨fun B => attainable row price B d, copies row d holds, obstructionCover row price d holds⟩

end PEqualNP.IndexedSampleErasures
