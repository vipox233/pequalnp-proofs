import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_344_aux

inductive DT (V O : Type) : Type
  | leaf : O → DT V O
  | node : (V → Bool) → DT V O → DT V O → DT V O

namespace DT
variable {V O : Type}

def run : DT V O → V → O
  | leaf o, _ => o
  | node f l r, z => if f z then run l z else run r z

def outs : DT V O → List O
  | leaf o => [o]
  | node _ l r => outs l ++ outs r

def Aff (Q : Set (V → Bool)) : DT V O → Prop
  | leaf _ => True
  | node f l r => f ∈ Q ∧ Aff Q l ∧ Aff Q r

def Shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧ (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def consF {α : Type} (a : α) (l r : List Bool → α) : List Bool → α
  | [] => a
  | true :: p => l p
  | false :: p => r p

def glue (A B : Finset (List Bool)) : Finset (List Bool) :=
  insert [] (A.image (List.cons true) ∪ B.image (List.cons false))

theorem nil_mem_glue (A B : Finset (List Bool)) : [] ∈ glue A B := by
  simp [glue]

theorem true_cons_mem_glue (A B : Finset (List Bool)) (p : List Bool) :
    true :: p ∈ glue A B ↔ p ∈ A := by
  simp [glue]

theorem false_cons_mem_glue (A B : Finset (List Bool)) (p : List Bool) :
    false :: p ∈ glue A B ↔ p ∈ B := by
  simp [glue]

theorem shape_glue {Nl Jl Nr Jr : Finset (List Bool)} (hl : Shape Nl Jl) (hr : Shape Nr Jr) :
    Shape (glue Nl Nr) (glue Jl Jr) := by
  unfold Shape at hl hr ⊢
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hl
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hr
  refine ⟨nil_mem_glue _ _, ?_, ?_, ?_⟩
  · intro p hp
    rcases p with _ | ⟨c, p⟩
    · exact nil_mem_glue _ _
    · cases c
      · simp only [false_cons_mem_glue] at hp ⊢
        exact hr2 hp
      · simp only [true_cons_mem_glue] at hp ⊢
        exact hl2 hp
  · intro p b hp
    rcases p with _ | ⟨c, p⟩
    · exact nil_mem_glue _ _
    · cases c
      · simp only [List.cons_append, false_cons_mem_glue] at hp ⊢
        exact hr3 p b hp
      · simp only [List.cons_append, true_cons_mem_glue] at hp ⊢
        exact hl3 p b hp
  · intro p hp
    rcases p with _ | ⟨c, p⟩
    · simp only [List.nil_append, false_cons_mem_glue, true_cons_mem_glue]
      exact ⟨hr1, hl1⟩
    · cases c
      · simp only [List.cons_append, false_cons_mem_glue] at hp ⊢
        exact hr4 p hp
      · simp only [List.cons_append, true_cons_mem_glue] at hp ⊢
        exact hl4 p hp

theorem glue_sdiff (Nl Jl Nr Jr : Finset (List Bool)) :
    glue Nl Nr \ glue Jl Jr =
      (Nl \ Jl).image (List.cons true) ∪ (Nr \ Jr).image (List.cons false) := by
  ext p
  rcases p with _ | ⟨c, p⟩
  · simp [nil_mem_glue]
  · cases c <;> simp [true_cons_mem_glue, false_cons_mem_glue]

theorem card_glue_sdiff (Nl Jl Nr Jr : Finset (List Bool)) :
    (glue Nl Nr \ glue Jl Jr).card = (Nl \ Jl).card + (Nr \ Jr).card := by
  rw [glue_sdiff, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ List.cons_injective,
    Finset.card_image_of_injective _ List.cons_injective]
  rw [Finset.disjoint_left]
  intro p hp hp'
  simp only [Finset.mem_image] at hp hp'
  obtain ⟨a, _, rfl⟩ := hp
  obtain ⟨b, _, hb⟩ := hp'
  simp at hb

theorem image_glue_sdiff [DecidableEq O] (Nl Jl Nr Jr : Finset (List Bool)) (o : O)
    (outl outr : List Bool → O) :
    (glue Nl Nr \ glue Jl Jr).image (consF o outl outr) =
      (Nl \ Jl).image outl ∪ (Nr \ Jr).image outr := by
  have e1 : consF o outl outr ∘ List.cons true = outl := funext fun p => rfl
  have e2 : consF o outl outr ∘ List.cons false = outr := funext fun p => rfl
  rw [glue_sdiff, Finset.image_union, Finset.image_image, Finset.image_image, e1, e2]

theorem bridge [DecidableEq O] (Q : Set (V → Bool)) (t : DT V O) (ht : t.Aff Q) :
    ∃ (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O),
      Shape N J ∧ (∀ p ∈ J, q p ∈ Q) ∧
      (∀ p ∈ N \ J, ∀ x : V, (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → out p = t.run x) ∧
      (N \ J).card = t.outs.length ∧ (N \ J).image out = t.outs.toFinset := by
  induction t with
  | leaf o =>
    refine ⟨{[]}, ∅, fun _ _ => true, fun _ => o, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Shape]
    · intro p hp
      simp at hp
    · intro p hp x hx
      rfl
    · simp [outs]
    · simp [outs]
  | node f l r ihl ihr =>
    obtain ⟨hf, hl, hr⟩ := ht
    obtain ⟨Nl, Jl, ql, outl, hsl, hql, hrl, hcl, hil⟩ := ihl hl
    obtain ⟨Nr, Jr, qr, outr, hsr, hqr, hrr, hcr, hir⟩ := ihr hr
    refine ⟨glue Nl Nr, glue Jl Jr, consF f ql qr, consF (outl []) outl outr,
      shape_glue hsl hsr, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases p with _ | ⟨c, p⟩
      · exact hf
      · cases c
        · exact hqr p ((false_cons_mem_glue _ _ _).mp hp)
        · exact hql p ((true_cons_mem_glue _ _ _).mp hp)
    · intro p hp x hx
      rcases p with _ | ⟨c, p⟩
      · exfalso
        simp [nil_mem_glue] at hp
      · cases c
        · have hp' : p ∈ Nr \ Jr := by
            simpa [false_cons_mem_glue] using hp
          have h0 : f x = false := hx ⟨0, by simp⟩
          have h1 := hrr p hp' x (fun j => hx ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
          have hrun : (node f l r).run x = r.run x := by simp [run, h0]
          rw [hrun]
          exact h1
        · have hp' : p ∈ Nl \ Jl := by
            simpa [true_cons_mem_glue] using hp
          have h0 : f x = true := hx ⟨0, by simp⟩
          have h1 := hrl p hp' x (fun j => hx ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
          have hrun : (node f l r).run x = l.run x := by simp [run, h0]
          rw [hrun]
          exact h1
    · rw [card_glue_sdiff, hcl, hcr]
      simp [outs]
    · rw [image_glue_sdiff, hil, hir]
      simp [outs]

def readQ : List (V → Bool) → Finset V → (List Bool → DT V O) → DT V O
  | [], _, k => k []
  | f :: fs, D, k =>
    if (D.filter (fun z => f z = true)).Nonempty then
      if (D.filter (fun z => f z = false)).Nonempty then
        node f (readQ fs (D.filter (fun z => f z = true)) (fun bs => k (true :: bs)))
          (readQ fs (D.filter (fun z => f z = false)) (fun bs => k (false :: bs)))
      else readQ fs D (fun bs => k (true :: bs))
    else readQ fs D (fun bs => k (false :: bs))

theorem run_readQ (qs : List (V → Bool)) (D : Finset V) (k : List Bool → DT V O) (z : V)
    (hz : z ∈ D) : (readQ qs D k).run z = (k (qs.map (fun f => f z))).run z := by
  induction qs generalizing D k with
  | nil => simp [readQ]
  | cons f fs ih =>
    simp only [readQ, List.map_cons]
    split_ifs with h1 h2
    · simp only [run]
      cases hf : f z with
      | true =>
        rw [ite_eq_left_of_eq_true _ _ (eq_self true)]
        exact ih _ _ (Finset.mem_filter.mpr ⟨hz, hf⟩)
      | false =>
        rw [ite_eq_right_of_eq_false _ _ (by simp)]
        exact ih _ _ (Finset.mem_filter.mpr ⟨hz, hf⟩)
    · have hf : f z = true := by
        by_contra hne
        exact h2 ⟨z, Finset.mem_filter.mpr ⟨hz, by simpa using hne⟩⟩
      rw [hf]
      exact ih _ _ hz
    · have hf : f z = false := by
        by_contra hne
        exact h1 ⟨z, Finset.mem_filter.mpr ⟨hz, by simpa using hne⟩⟩
      rw [hf]
      exact ih _ _ hz

theorem mem_outs_readQ (qs : List (V → Bool)) (D : Finset V) (k : List Bool → DT V O)
    (hD : D.Nonempty) (o : O) (ho : o ∈ (readQ qs D k).outs) :
    ∃ z ∈ D, o ∈ (k (qs.map (fun f => f z))).outs := by
  induction qs generalizing D k with
  | nil =>
    obtain ⟨z, hz⟩ := hD
    exact ⟨z, hz, by simpa [readQ] using ho⟩
  | cons f fs ih =>
    have et : ∀ z, f z = true →
        (f :: fs).map (fun g => g z) = true :: fs.map (fun g => g z) := by
      intro z h
      simp [h]
    have ef : ∀ z, f z = false →
        (f :: fs).map (fun g => g z) = false :: fs.map (fun g => g z) := by
      intro z h
      simp [h]
    simp only [readQ] at ho
    split_ifs at ho with h1 h2
    · simp only [outs, List.mem_append] at ho
      rcases ho with ho | ho
      · obtain ⟨z, hz, hzo⟩ := ih _ _ h1 ho
        have hz' := Finset.mem_filter.mp hz
        refine ⟨z, hz'.1, ?_⟩
        rw [et z hz'.2]
        exact hzo
      · obtain ⟨z, hz, hzo⟩ := ih _ _ h2 ho
        have hz' := Finset.mem_filter.mp hz
        refine ⟨z, hz'.1, ?_⟩
        rw [ef z hz'.2]
        exact hzo
    · obtain ⟨z, hz, hzo⟩ := ih _ _ hD ho
      have hf : f z = true := by
        by_contra hne
        exact h2 ⟨z, Finset.mem_filter.mpr ⟨hz, by simpa using hne⟩⟩
      refine ⟨z, hz, ?_⟩
      rw [et z hf]
      exact hzo
    · obtain ⟨z, hz, hzo⟩ := ih _ _ hD ho
      have hf : f z = false := by
        by_contra hne
        exact h1 ⟨z, Finset.mem_filter.mpr ⟨hz, by simpa using hne⟩⟩
      refine ⟨z, hz, ?_⟩
      rw [ef z hf]
      exact hzo

theorem nodup_outs_readQ (qs : List (V → Bool)) (D : Finset V) (k : List Bool → DT V O)
    (hD : D.Nonempty)
    (h1 : ∀ z ∈ D, (k (qs.map (fun f => f z))).outs.Nodup)
    (h2 : ∀ z ∈ D, ∀ z' ∈ D, qs.map (fun f => f z) ≠ qs.map (fun f => f z') →
      List.Disjoint (k (qs.map (fun f => f z))).outs (k (qs.map (fun f => f z'))).outs) :
    (readQ qs D k).outs.Nodup := by
  induction qs generalizing D k with
  | nil =>
    obtain ⟨z, hz⟩ := hD
    simpa [readQ] using h1 z hz
  | cons f fs ih =>
    have et : ∀ z, f z = true →
        (f :: fs).map (fun g => g z) = true :: fs.map (fun g => g z) := by
      intro z h
      simp [h]
    have ef : ∀ z, f z = false →
        (f :: fs).map (fun g => g z) = false :: fs.map (fun g => g z) := by
      intro z h
      simp [h]
    simp only [readQ]
    split_ifs with ha hb
    · simp only [outs]
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · apply ih _ _ ha
        · intro z hz
          have hz' := Finset.mem_filter.mp hz
          have h := h1 z hz'.1
          rw [et z hz'.2] at h
          exact h
        · intro z hz z' hz' hne
          have hzm := Finset.mem_filter.mp hz
          have hzm' := Finset.mem_filter.mp hz'
          have h := h2 z hzm.1 z' hzm'.1 (by
            rw [et z hzm.2, et z' hzm'.2]
            exact fun h => hne (List.cons.inj h).2)
          rw [et z hzm.2, et z' hzm'.2] at h
          exact h
      · apply ih _ _ hb
        · intro z hz
          have hz' := Finset.mem_filter.mp hz
          have h := h1 z hz'.1
          rw [ef z hz'.2] at h
          exact h
        · intro z hz z' hz' hne
          have hzm := Finset.mem_filter.mp hz
          have hzm' := Finset.mem_filter.mp hz'
          have h := h2 z hzm.1 z' hzm'.1 (by
            rw [ef z hzm.2, ef z' hzm'.2]
            exact fun h => hne (List.cons.inj h).2)
          rw [ef z hzm.2, ef z' hzm'.2] at h
          exact h
      · intro a haa b hbb hab
        subst hab
        obtain ⟨z, hz, hzo⟩ := mem_outs_readQ _ _ _ ha a haa
        obtain ⟨z', hz', hzo'⟩ := mem_outs_readQ _ _ _ hb a hbb
        have hzm := Finset.mem_filter.mp hz
        have hzm' := Finset.mem_filter.mp hz'
        have h := h2 z hzm.1 z' hzm'.1 (by
          rw [et z hzm.2, ef z' hzm'.2]
          simp)
        rw [et z hzm.2, ef z' hzm'.2] at h
        exact h hzo hzo'
    · have hall : ∀ z ∈ D, f z = true := by
        intro z hz
        by_contra hne
        exact hb ⟨z, Finset.mem_filter.mpr ⟨hz, by simpa using hne⟩⟩
      apply ih _ _ hD
      · intro z hz
        have h := h1 z hz
        rw [et z (hall z hz)] at h
        exact h
      · intro z hz z' hz' hne
        have h := h2 z hz z' hz' (by
          rw [et z (hall z hz), et z' (hall z' hz')]
          exact fun h => hne (List.cons.inj h).2)
        rw [et z (hall z hz), et z' (hall z' hz')] at h
        exact h
    · have hall : ∀ z ∈ D, f z = false := by
        intro z hz
        by_contra hne
        exact ha ⟨z, Finset.mem_filter.mpr ⟨hz, by simpa using hne⟩⟩
      apply ih _ _ hD
      · intro z hz
        have h := h1 z hz
        rw [ef z (hall z hz)] at h
        exact h
      · intro z hz z' hz' hne
        have h := h2 z hz z' hz' (by
          rw [ef z (hall z hz), ef z' (hall z' hz')]
          exact fun h => hne (List.cons.inj h).2)
        rw [ef z (hall z hz), ef z' (hall z' hz')] at h
        exact h

theorem aff_readQ (Q : Set (V → Bool)) (qs : List (V → Bool)) (D : Finset V)
    (k : List Bool → DT V O) (hq : ∀ f ∈ qs, f ∈ Q) (hk : ∀ bs, (k bs).Aff Q) :
    (readQ qs D k).Aff Q := by
  induction qs generalizing D k with
  | nil => simpa [readQ] using hk []
  | cons f fs ih =>
    have hf : f ∈ Q := hq f (by simp)
    have hfs : ∀ g ∈ fs, g ∈ Q := fun g hg => hq g (List.mem_cons_of_mem _ hg)
    simp only [readQ]
    split_ifs
    · simp only [Aff]
      exact ⟨hf, ih _ _ hfs (fun bs => hk _), ih _ _ hfs (fun bs => hk _)⟩
    · exact ih _ _ hfs (fun bs => hk _)
    · exact ih _ _ hfs (fun bs => hk _)

def scan {ι : Type} (fail : ι → V → Bool) (k : ι → DT V O) (d : DT V O) : List ι → DT V O
  | [] => d
  | [i] => k i
  | i :: j :: rest => node (fail i) (k i) (scan fail k d (j :: rest))

theorem run_scan {ι : Type} (fail : ι → V → Bool) (k : ι → DT V O) (d : DT V O) (L : List ι)
    (z : V) (h : ∃ i ∈ L, fail i z = true) :
    ∃ i ∈ L, fail i z = true ∧ (scan fail k d L).run z = (k i).run z := by
  induction L with
  | nil =>
    obtain ⟨i, hi, _⟩ := h
    simp at hi
  | cons i t ih =>
    cases t with
    | nil =>
      obtain ⟨i', hi', hf⟩ := h
      have hii : i' = i := by simpa using hi'
      subst hii
      exact ⟨i', by simp, hf, by simp [scan]⟩
    | cons j rest =>
      by_cases hi : fail i z = true
      · exact ⟨i, by simp, hi, by simp [scan, run, hi]⟩
      · have h' : ∃ i' ∈ j :: rest, fail i' z = true := by
          obtain ⟨i', hi', hf⟩ := h
          rcases List.mem_cons.mp hi' with hii | hmem
          · subst hii
            exact absurd hf hi
          · exact ⟨i', hmem, hf⟩
        obtain ⟨i', hi', hf, hr⟩ := ih h'
        refine ⟨i', List.mem_cons_of_mem _ hi', hf, ?_⟩
        rw [← hr]
        simp [scan, run, hi]

theorem mem_outs_scan {ι : Type} (fail : ι → V → Bool) (k : ι → DT V O) (d : DT V O)
    (L : List ι) (hL : L ≠ []) (o : O) (ho : o ∈ (scan fail k d L).outs) :
    ∃ i ∈ L, o ∈ (k i).outs := by
  induction L with
  | nil => exact absurd rfl hL
  | cons i t ih =>
    cases t with
    | nil => exact ⟨i, by simp, by simpa [scan] using ho⟩
    | cons j rest =>
      simp only [scan, outs, List.mem_append] at ho
      rcases ho with ho | ho
      · exact ⟨i, by simp, ho⟩
      · obtain ⟨i', hi', ho'⟩ := ih (by simp) ho
        exact ⟨i', List.mem_cons_of_mem _ hi', ho'⟩

theorem nodup_outs_scan {ι : Type} (fail : ι → V → Bool) (k : ι → DT V O) (d : DT V O)
    (L : List ι) (hL : L ≠ []) (hn : L.Nodup) (h1 : ∀ i ∈ L, (k i).outs.Nodup)
    (h2 : ∀ i ∈ L, ∀ j ∈ L, i ≠ j → List.Disjoint (k i).outs (k j).outs) :
    (scan fail k d L).outs.Nodup := by
  induction L with
  | nil => exact absurd rfl hL
  | cons i t ih =>
    cases t with
    | nil => simpa [scan] using h1 i (by simp)
    | cons j rest =>
      simp only [scan, outs]
      rw [List.nodup_append]
      refine ⟨h1 i (by simp), ?_, ?_⟩
      · exact ih (by simp) (List.nodup_cons.mp hn).2
          (fun a ha => h1 a (List.mem_cons_of_mem _ ha))
          (fun a ha b hb hab =>
            h2 a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab)
      · intro a ha b hb hab
        subst hab
        obtain ⟨i', hi', ho'⟩ := mem_outs_scan fail k d (j :: rest) (by simp) a hb
        have hne : i ≠ i' := by
          intro hii
          subst hii
          exact (List.nodup_cons.mp hn).1 hi'
        exact h2 i (by simp) i' (List.mem_cons_of_mem _ hi') hne ha ho'

theorem aff_scan {ι : Type} (Q : Set (V → Bool)) (fail : ι → V → Bool) (k : ι → DT V O)
    (d : DT V O) (L : List ι) (hL : L ≠ []) (hf : ∀ i ∈ L, fail i ∈ Q)
    (hk : ∀ i ∈ L, (k i).Aff Q) : (scan fail k d L).Aff Q := by
  induction L with
  | nil => exact absurd rfl hL
  | cons i t ih =>
    cases t with
    | nil => simpa [scan] using hk i (by simp)
    | cons j rest =>
      simp only [scan, Aff]
      exact ⟨hf i (by simp), hk i (by simp),
        ih (by simp) (fun a ha => hf a (List.mem_cons_of_mem _ ha))
          (fun a ha => hk a (List.mem_cons_of_mem _ ha))⟩

end DT


theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem functional_eq_sum {m : ℕ} (φ : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (R : Finset (Fin m)) (v : Fin m → ZMod 2) (hv : ∀ i, i ∉ R → v i = 0) :
    φ v = ∑ i ∈ R.filter (fun i => φ (fun j => if i = j then 1 else 0) = 1), v i := by
  rw [LinearMap.pi_apply_eq_sum_univ φ v, Finset.sum_filter]
  have hsub : ∑ i ∈ R, v i • φ (fun j => if i = j then 1 else 0)
      = ∑ i, v i • φ (fun j => if i = j then 1 else 0) :=
    Finset.sum_subset (Finset.subset_univ R) (fun i _ hi => by rw [hv i hi, zero_smul])
  rw [← hsub]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases zmod2_cases (φ fun j => if i = j then 1 else 0) with h | h <;> rw [h] <;> simp

theorem exists_oddDep {n m : ℕ} (row : Fin m → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (rhs : Fin m → ZMod 2) (R : Finset (Fin m))
    (h : ∀ x : Fin n → ZMod 2, ∃ i ∈ R, row i x ≠ rhs i) :
    ∃ P : Finset (Fin m), P ⊆ R ∧ P.sum row = 0 ∧ P.sum rhs = 1 := by
  classical
  let A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    LinearMap.pi (fun i => if i ∈ R then row i else 0)
  let b : Fin m → ZMod 2 := fun i => if i ∈ R then rhs i else 0
  have hb : b ∉ LinearMap.range A := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, hne⟩ := h x
    apply hne
    have := congrFun hx i
    simpa [A, b, hi] using this
  obtain ⟨φ, hφb, hφ⟩ := Submodule.exists_le_ker_of_notMem hb
  refine ⟨R.filter (fun i => φ (fun j => if i = j then 1 else 0) = 1),
    Finset.filter_subset _ _, ?_, ?_⟩
  · refine LinearMap.ext (fun x => ?_)
    have hx : φ (A x) = 0 := LinearMap.mem_ker.mp (hφ (LinearMap.mem_range_self A x))
    rw [functional_eq_sum φ R (A x) (fun i hi => by simp [A, hi])] at hx
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    refine Eq.trans (Finset.sum_congr rfl (fun i hi => ?_)) hx
    have hiR : i ∈ R := (Finset.mem_filter.mp hi).1
    simp [A, hiR]
  · have hb1 : φ b = 1 := (zmod2_cases (φ b)).resolve_left hφb
    rw [functional_eq_sum φ R b (fun i hi => by simp [b, hi])] at hb1
    refine Eq.trans (Finset.sum_congr rfl (fun i hi => ?_)) hb1
    have hiR : i ∈ R := (Finset.mem_filter.mp hi).1
    simp [b, hiR]

theorem fiber_card {k t : ℕ} (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (u0 : Fin k → ZMod 2) :
    2 ^ Module.finrank (ZMod 2) (LinearMap.range A) *
      (Finset.univ.filter (fun u : Fin k → ZMod 2 => A u = A u0)).card
      = Fintype.card (Fin k → ZMod 2) := by
  classical
  have hker : (Finset.univ.filter (fun u : Fin k → ZMod 2 => A u = A u0)).card
      = Fintype.card (LinearMap.ker A) := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr
      ⟨fun u => ⟨u.1 - u0, by simp [LinearMap.mem_ker, map_sub, u.2]⟩,
        fun v => ⟨v.1 + u0, by simp [map_add, LinearMap.mem_ker.mp v.2]⟩,
        fun u => Subtype.ext (by simp), fun v => Subtype.ext (by simp)⟩
  rw [hker, Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker A),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := Fin k → ZMod 2), ZMod.card, ← pow_add,
    LinearMap.finrank_range_add_finrank_ker]

theorem double_count {k t m : ℕ} (M : Fin m → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (B : Finset (Fin m × (Fin t → ZMod 2))) :
    ∑ u : Fin k → ZMod 2, ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i, M i u) ∈ B),
        2 ^ Module.finrank (ZMod 2) (LinearMap.range (M i))
      = ∑ b ∈ B, (if ∃ u : Fin k → ZMod 2, b.2 = M b.1 u then
          Fintype.card (Fin k → ZMod 2) else 0) := by
  classical
  have step : ∀ u : Fin k → ZMod 2,
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i, M i u) ∈ B),
          (2 : ℕ) ^ Module.finrank (ZMod 2) (LinearMap.range (M i))
        = ∑ b ∈ B, if b.2 = M b.1 u then
            (2 : ℕ) ^ Module.finrank (ZMod 2) (LinearMap.range (M b.1)) else 0 := by
    intro u
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun i => (i, M i u)) (fun b => b.1) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, rfl⟩
    · intro b hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← (Finset.mem_filter.mp hb).2]
      exact (Finset.mem_filter.mp hb).1
    · intro i _
      rfl
    · intro b hb
      exact Prod.ext rfl (Finset.mem_filter.mp hb).2.symm
    · intro i _
      rfl
  rw [Finset.sum_congr rfl (fun u _ => step u), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  by_cases hex : ∃ u : Fin k → ZMod 2, b.2 = M b.1 u
  · obtain ⟨u0, h0⟩ := hex
    rw [ite_eq_left ⟨u0, h0⟩, mul_comm]
    have hf : Finset.univ.filter (fun u : Fin k → ZMod 2 => b.2 = M b.1 u)
        = Finset.univ.filter (fun u : Fin k → ZMod 2 => M b.1 u = M b.1 u0) := by
      refine Finset.filter_congr (fun u _ => ?_)
      rw [h0]
      exact eq_comm
    rw [hf]
    exact fiber_card (M b.1) u0
  · rw [ite_eq_right hex]
    have hf : Finset.univ.filter (fun u : Fin k → ZMod 2 => b.2 = M b.1 u) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun u _ hu => hex ⟨u, hu⟩)
    rw [hf]
    simp

theorem sup_invariant {k : ℕ} {α ι : Type} (F : (Fin k → ZMod 2) → α) (I : Finset ι)
    (K : ι → Submodule (ZMod 2) (Fin k → ZMod 2))
    (h : ∀ i ∈ I, ∀ v ∈ K i, ∀ u, F (u + v) = F u) :
    ∀ v ∈ I.sup K, ∀ u, F (u + v) = F u := by
  let S : Submodule (ZMod 2) (Fin k → ZMod 2) :=
    { carrier := {v | ∀ u, F (u + v) = F u}, add_mem' := by
        intro a b ha hb
        have ha' : ∀ u, F (u + a) = F u := ha
        have hb' : ∀ u, F (u + b) = F u := hb
        change ∀ u, F (u + (a + b)) = F u
        intro u
        rw [← add_assoc, hb' (u + a), ha' u]
      , zero_mem' := by
        change ∀ u, F (u + 0) = F u
        intro u
        rw [add_zero]
      , smul_mem' := by
        intro c v hv
        have hv' : ∀ u, F (u + v) = F u := hv
        change ∀ u, F (u + c • v) = F u
        intro u
        rcases zmod2_cases c with rfl | rfl
        · rw [zero_smul, add_zero]
        · rw [one_smul]
          exact hv' u }
  have hle : I.sup K ≤ S := Finset.sup_le (fun i hi v hv => h i hi v hv)
  exact fun v hv => hle hv

theorem exists_separating {k : ℕ} (H : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    ∃ L : List ((Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2),
      ∀ u u' : Fin k → ZMod 2, (∀ l ∈ L, l u = l u') ↔ u - u' ∈ H := by
  classical
  have hsep : ∀ v : Fin k → ZMod 2, ∃ f : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      H ≤ LinearMap.ker f ∧ (v ∉ H → f v ≠ 0) := by
    intro v
    by_cases hv : v ∈ H
    · exact ⟨0, by simp, fun hn => absurd hv hn⟩
    · obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_notMem hv
      exact ⟨f, hle, fun _ => hf⟩
  choose g hg1 hg2 using hsep
  refine ⟨(Finset.univ : Finset (Fin k → ZMod 2)).toList.map g,
    fun u u' => ⟨fun hall => ?_, fun hmem l hl => ?_⟩⟩
  · by_contra hn
    apply hg2 (u - u') hn
    rw [map_sub, sub_eq_zero]
    exact hall _ (List.mem_map.mpr ⟨u - u', Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩)
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
    have hz := LinearMap.mem_ker.mp (hg1 v hmem)
    rwa [map_sub, sub_eq_zero] at hz


abbrev Vec (n : ℕ) : Type := Fin n → ZMod 2

def Queries (V : Type) [AddCommGroup V] [Module (ZMod 2) V] : Set (V → Bool) :=
  {f | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}

def Cert {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
    (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) : Prop :=
  DT.Shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
    (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)

theorem exists_leaf {V : Type} (N J : Finset (List Bool)) (q : List Bool → V → Bool)
    (hs : DT.Shape N J) (z : V) :
    ∃ p ∈ N \ J, ∀ j : Fin p.length, q (p.take j.val) z = p.get j := by
  classical
  obtain ⟨h0, hJN, -, hch⟩ := hs
  let C := N.filter (fun p => ∀ j : Fin p.length, q (p.take j.val) z = p.get j)
  have hC : C.Nonempty := ⟨[], by simp [C, h0]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image C List.length hC
  have hp2 := Finset.mem_filter.mp hp
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hp2.1, fun hpJ => ?_⟩, hp2.2⟩
  have hmem : p ++ [q p z] ∈ N := by
    cases hb : q p z
    · exact (hch p hpJ).1
    · exact (hch p hpJ).2
  have hc : p ++ [q p z] ∈ C := by
    refine Finset.mem_filter.mpr ⟨hmem, fun j => ?_⟩
    have hj : j.val < p.length + 1 := by simpa using j.isLt
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · rw [List.take_append_of_le_length (le_of_lt h)]
      have h1 := hp2.2 ⟨j.val, h⟩
      rw [List.get_eq_getElem] at h1 ⊢
      rw [List.getElem_append_left h]
      exact h1
    · have h2 : (p ++ [q p z]).take j.val = p := by rw [h]; simp
      rw [h2, List.get_eq_getElem]
      simp [h]
  have h3 := hmax _ hc
  simp at h3

section Main
variable {n k t m : ℕ} (row : Fin m → Vec n →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
  (M : Fin m → Vec k →ₗ[ZMod 2] Vec t)

def OddDep (P : Finset (Fin m)) : Prop := P.sum row = 0 ∧ P.sum rhs = 1

noncomputable def wt (i : Fin m) : ℕ := 2 ^ Module.finrank (ZMod 2) (LinearMap.range (M i))

def Answer (z : Vec n × Vec k) (a : Fin m × Vec t) : Prop :=
  row a.1 z.1 ≠ rhs a.1 ∧ a.2 = M a.1 z.2

def Rset (B : Finset (Fin m × Vec t)) (u : Vec k) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (i, M i u) ∈ B)

def Realizable (W : ℕ) (B : Finset (Fin m × Vec t)) : Prop :=
  ∃ (N J : Finset (List Bool)) (q : List Bool → (Vec n × Vec k) → Bool)
    (out : List Bool → Fin m × Vec t),
    Cert (Queries (Vec n × Vec k)) (Answer row rhs M) N J q out ∧
    (N \ J).card = W ∧ (N \ J).image out = B

theorem wt_pos (i : Fin m) : 0 < wt M i := by unfold wt; positivity

theorem cert_oddDep (N J : Finset (List Bool)) (q : List Bool → (Vec n × Vec k) → Bool)
    (out : List Bool → Fin m × Vec t)
    (hc : Cert (Queries (Vec n × Vec k)) (Answer row rhs M) N J q out) (u : Vec k) :
    ∃ P : Finset (Fin m), P ⊆ Rset M ((N \ J).image out) u ∧ OddDep row rhs P := by
  refine exists_oddDep row rhs (Rset M ((N \ J).image out) u) (fun x => ?_)
  obtain ⟨p, hp, hcons⟩ := exists_leaf N J q hc.1 (x, u)
  have ha := hc.2.2 p hp (x, u) hcons
  refine ⟨(out p).1, ?_, ha.1⟩
  simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : ((out p).1, M (out p).1 u) = out p := Prod.ext rfl ha.2.symm
  rw [h1]; exact Finset.mem_image_of_mem out hp

theorem card_lower (W : ℕ) (B : Finset (Fin m × Vec t))
    (h : ∀ u, W ≤ ∑ i ∈ Rset M B u, wt M i) : W ≤ B.card := by
  have hdc : ∑ u : Vec k, ∑ i ∈ Rset M B u, wt M i = ∑ b ∈ B,
      (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0) := double_count M B
  have h1 : ∑ _u : Vec k, W ≤ ∑ u : Vec k, ∑ i ∈ Rset M B u, wt M i :=
    Finset.sum_le_sum (fun u _ => h u)
  have h2 : ∑ b ∈ B, (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0)
      ≤ ∑ _b ∈ B, Fintype.card (Vec k) :=
    Finset.sum_le_sum (fun b _ => by split_ifs <;> simp)
  have hsumW : ∑ _u : Vec k, W = Fintype.card (Vec k) * W := by simp [Finset.card_univ]
  have hsumc : ∑ _b ∈ B, Fintype.card (Vec k) = Fintype.card (Vec k) * B.card := by
    simp [mul_comm]
  have hpos : 0 < Fintype.card (Vec k) := Fintype.card_pos
  have h3 : Fintype.card (Vec k) * W ≤ Fintype.card (Vec k) * B.card := by
    rw [← hsumW, ← hsumc]; exact le_trans h1 (hdc ▸ h2)
  exact Nat.le_of_mul_le_mul_left h3 hpos

variable (S T : Finset (Fin m))

def hidden : Submodule (ZMod 2) (Vec k) :=
  ((S \ T) ∪ (T \ S)).sup (fun i => LinearMap.ker (M i))

def cg (g : (Vec k ⧸ hidden M S T) → Bool) (u : Vec k) : Finset (Fin m) :=
  if g (Submodule.Quotient.mk u) then S else T

open Classical in
noncomputable def Bg (g : (Vec k ⧸ hidden M S T) → Bool) : Finset (Fin m × Vec t) :=
  Finset.univ.filter (fun b => ∃ u : Vec k, b.2 = M b.1 u ∧ b.1 ∈ cg M S T g u)

def Best2 : Prop :=
  ∀ P, (OddDep row rhs P ∧ ∀ T2, OddDep row rhs T2 → P.sum (wt M) ≤ T2.sum (wt M)) ↔
    P = S ∨ P = T

theorem best_S (hb : Best2 row rhs M S T) :
    OddDep row rhs S ∧ ∀ T2, OddDep row rhs T2 → ∑ i ∈ S, wt M i ≤ ∑ i ∈ T2, wt M i :=
  (hb S).2 (Or.inl rfl)

theorem best_T (hb : Best2 row rhs M S T) :
    OddDep row rhs T ∧ ∀ T2, OddDep row rhs T2 → ∑ i ∈ T, wt M i ≤ ∑ i ∈ T2, wt M i :=
  (hb T).2 (Or.inr rfl)

theorem wS_eq_wT (hb : Best2 row rhs M S T) : ∑ i ∈ S, wt M i = ∑ i ∈ T, wt M i :=
  le_antisymm ((best_S row rhs M S T hb).2 T (best_T row rhs M S T hb).1)
    ((best_T row rhs M S T hb).2 S (best_S row rhs M S T hb).1)

theorem sdiff_nonempty_of_wt {A B : Finset (Fin m)} (hne : A ≠ B)
    (hw : ∑ i ∈ A, wt M i = ∑ i ∈ B, wt M i) : (A \ B).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
  have hss : A ⊂ B := lt_of_le_of_ne h hne
  obtain ⟨i, hiB, hiA⟩ := Finset.exists_of_ssubset hss
  have h1 : ∑ j ∈ A, wt M j < ∑ j ∈ B, wt M j :=
    Finset.sum_lt_sum_of_subset h hiB hiA (wt_pos M i) (fun j _ _ => Nat.zero_le _)
  omega

theorem classify (hb : Best2 row rhs M S T) (B : Finset (Fin m × Vec t))
    (hB : Realizable row rhs M (∑ i ∈ S, wt M i) B) :
    (∀ u, Rset M B u = S ∨ Rset M B u = T) ∧ ∀ b ∈ B, ∃ u : Vec k, b.2 = M b.1 u := by
  classical
  obtain ⟨N, J, q, out, hc, hcard, him⟩ := hB
  have hBc : B.card ≤ ∑ i ∈ S, wt M i := by
    rw [← him, ← hcard]; exact Finset.card_image_le
  have hP : ∀ u, ∃ P : Finset (Fin m), P ⊆ Rset M B u ∧ OddDep row rhs P := by
    intro u
    have h0 := cert_oddDep row rhs M N J q out hc u
    rwa [him] at h0
  have hge : ∀ u, ∑ i ∈ S, wt M i ≤ ∑ i ∈ Rset M B u, wt M i := by
    intro u
    obtain ⟨P, hPs, hPo⟩ := hP u
    exact le_trans ((best_S row rhs M S T hb).2 P hPo) (Finset.sum_le_sum_of_subset hPs)
  have hdc : ∑ u : Vec k, ∑ i ∈ Rset M B u, wt M i = ∑ b ∈ B,
      (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0) := double_count M B
  have hle2 : ∀ b ∈ B, (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0)
      ≤ Fintype.card (Vec k) := by
    intro b _; split_ifs <;> simp
  have hsumc : ∑ _b ∈ B, Fintype.card (Vec k) = Fintype.card (Vec k) * B.card := by
    simp [mul_comm]
  have hsumW : ∑ _u : Vec k, ∑ i ∈ S, wt M i = Fintype.card (Vec k) * ∑ i ∈ S, wt M i := by
    simp [Finset.card_univ]
  have h1 : ∑ _u : Vec k, ∑ i ∈ S, wt M i ≤ ∑ u : Vec k, ∑ i ∈ Rset M B u, wt M i :=
    Finset.sum_le_sum (fun u _ => hge u)
  have h2 : ∑ b ∈ B, (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0)
      ≤ ∑ _b ∈ B, Fintype.card (Vec k) := Finset.sum_le_sum hle2
  have h3 : Fintype.card (Vec k) * B.card ≤ Fintype.card (Vec k) * ∑ i ∈ S, wt M i :=
    Nat.mul_le_mul_left _ hBc
  have e1 : ∑ _u : Vec k, ∑ i ∈ S, wt M i = ∑ u : Vec k, ∑ i ∈ Rset M B u, wt M i := by
    apply le_antisymm h1
    rw [hdc, hsumW]; exact le_trans h2 (hsumc ▸ h3)
  have e2 : ∑ b ∈ B, (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0)
      = ∑ _b ∈ B, Fintype.card (Vec k) := by
    apply le_antisymm h2
    rw [← hdc, hsumc]; exact le_trans h3 (hsumW ▸ h1)
  have t1 := (Finset.sum_eq_sum_iff_of_le (fun u _ => hge u)).mp e1
  have t2 := (Finset.sum_eq_sum_iff_of_le hle2).mp e2
  constructor
  · intro u
    obtain ⟨P, hPs, hPo⟩ := hP u
    have hu : ∑ i ∈ S, wt M i = ∑ i ∈ Rset M B u, wt M i := t1 u (Finset.mem_univ u)
    have hPW : ∑ i ∈ S, wt M i ≤ ∑ i ∈ P, wt M i := (best_S row rhs M S T hb).2 P hPo
    have hPeq : P = Rset M B u := by
      by_contra hne
      have hss : P ⊂ Rset M B u := lt_of_le_of_ne hPs hne
      obtain ⟨i, hi1, hi2⟩ := Finset.exists_of_ssubset hss
      have h4 : ∑ j ∈ P, wt M j < ∑ j ∈ Rset M B u, wt M j :=
        Finset.sum_lt_sum_of_subset hPs hi1 hi2 (wt_pos M i) (fun j _ _ => Nat.zero_le _)
      omega
    rw [← hPeq]
    refine (hb P).1 ⟨hPo, fun T2 hT2 => ?_⟩
    have h5 : ∑ i ∈ S, wt M i ≤ ∑ i ∈ T2, wt M i := (best_S row rhs M S T hb).2 T2 hT2
    have h6 : ∑ i ∈ P, wt M i = ∑ i ∈ S, wt M i := by rw [hPeq]; exact hu.symm
    exact h6 ▸ h5
  · intro b hbB
    have h7 := t2 b hbB
    by_contra hne
    rw [if_neg hne] at h7
    have hpos : 0 < Fintype.card (Vec k) := Fintype.card_pos
    omega

theorem Rset_invariant (B : Finset (Fin m × Vec t))
    (hcl : ∀ u, Rset M B u = S ∨ Rset M B u = T) :
    ∀ v ∈ hidden M S T, ∀ u, Rset M B (u + v) = Rset M B u := by
  refine sup_invariant (fun u => Rset M B u) ((S \ T) ∪ (T \ S))
    (fun i => LinearMap.ker (M i)) ?_
  intro i hi v hv u
  have hMv : M i (u + v) = M i u := by rw [map_add, LinearMap.mem_ker.mp hv, add_zero]
  have hiff : i ∈ Rset M B (u + v) ↔ i ∈ Rset M B u := by
    simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hMv]
  simp only [Finset.mem_union, Finset.mem_sdiff] at hi
  rcases hcl (u + v) with h1 | h1 <;> rcases hcl u with h2 | h2
  · show Rset M B (u + v) = Rset M B u
    rw [h1, h2]
  · exfalso; rw [h1, h2] at hiff; tauto
  · exfalso; rw [h1, h2] at hiff; tauto
  · show Rset M B (u + v) = Rset M B u
    rw [h1, h2]

theorem cg_cases (g : (Vec k ⧸ hidden M S T) → Bool) (u : Vec k) :
    cg M S T g u = S ∨ cg M S T g u = T := by
  unfold cg; split_ifs <;> simp

theorem ker_le_hidden {i : Fin m} (hi : i ∈ (S \ T) ∪ (T \ S)) :
    LinearMap.ker (M i) ≤ hidden M S T :=
  Finset.le_sup (f := fun i => LinearMap.ker (M i)) hi

theorem Rset_Bg (g : (Vec k ⧸ hidden M S T) → Bool) (u : Vec k) :
    Rset M (Bg M S T g) u = cg M S T g u := by
  classical
  ext i
  simp only [Rset, Bg, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u2, hu2, hi⟩
    have hu3 : M i u = M i u2 := hu2
    have hi2 : i ∈ cg M S T g u2 := hi
    by_cases hmk : (Submodule.Quotient.mk u : Vec k ⧸ hidden M S T) = Submodule.Quotient.mk u2
    · have h1 : cg M S T g u = cg M S T g u2 := by unfold cg; rw [hmk]
      rw [h1]; exact hi2
    · have hnd : i ∉ (S \ T) ∪ (T \ S) := by
        intro hd
        apply hmk
        rw [Submodule.Quotient.eq]
        apply ker_le_hidden M S T hd
        rw [LinearMap.mem_ker, map_sub, hu3, sub_self]
      simp only [Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not] at hnd
      rcases cg_cases M S T g u2 with h | h <;> rcases cg_cases M S T g u with h2 | h2 <;>
        rw [h] at hi2 <;> rw [h2] <;> tauto
  · intro hi; exact ⟨u, rfl, hi⟩

theorem Bg_of_realizable (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (B : Finset (Fin m × Vec t)) (hB : Realizable row rhs M (∑ i ∈ S, wt M i) B) :
    ∃ g, B = Bg M S T g := by
  classical
  obtain ⟨hcl, hrange⟩ := classify row rhs M S T hb B hB
  have hinv := Rset_invariant M S T B hcl
  refine ⟨fun q => decide (Rset M B (Quotient.out q) = S), ?_⟩
  have hcg : ∀ u, cg M S T (fun q => decide (Rset M B (Quotient.out q) = S)) u
      = Rset M B u := by
    intro u
    have hmem : u - Quotient.out (Submodule.Quotient.mk u : Vec k ⧸ hidden M S T)
        ∈ hidden M S T := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_out]
    have hR : Rset M B (Quotient.out (Submodule.Quotient.mk u : Vec k ⧸ hidden M S T))
        = Rset M B u := by
      have h1 := hinv _ hmem (Quotient.out (Submodule.Quotient.mk u : Vec k ⧸ hidden M S T))
      rw [← h1]; congr 1; abel
    unfold cg
    simp only [decide_eq_true_eq]
    rw [hR]
    rcases hcl u with h | h
    · rw [if_pos h, h]
    · rw [if_neg (by rw [h]; exact fun e => hST e.symm), h]
  ext b
  constructor
  · intro hbB
    obtain ⟨u, hu⟩ := hrange b hbB
    simp only [Bg, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨u, hu, ?_⟩
    rw [hcg]
    simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hu]; exact hbB
  · intro hbg
    simp only [Bg, Finset.mem_filter, Finset.mem_univ, true_and] at hbg
    obtain ⟨u, hu, hi⟩ := hbg
    rw [hcg] at hi
    simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [← hu] at hi; exact hi

theorem card_Bg (hb : Best2 row rhs M S T) (g : (Vec k ⧸ hidden M S T) → Bool) :
    (Bg M S T g).card = ∑ i ∈ S, wt M i := by
  have hdc : ∑ u : Vec k, ∑ i ∈ Rset M (Bg M S T g) u, wt M i = ∑ b ∈ Bg M S T g,
      (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0) :=
    double_count M (Bg M S T g)
  have hl : ∑ u : Vec k, ∑ i ∈ Rset M (Bg M S T g) u, wt M i
      = ∑ _u : Vec k, ∑ i ∈ S, wt M i := by
    apply Finset.sum_congr rfl
    intro u _
    rw [Rset_Bg]
    rcases cg_cases M S T g u with h | h <;> rw [h]
    exact (wS_eq_wT row rhs M S T hb).symm
  have hr : ∑ b ∈ Bg M S T g, (if ∃ u : Vec k, b.2 = M b.1 u then Fintype.card (Vec k) else 0)
      = ∑ _b ∈ Bg M S T g, Fintype.card (Vec k) := by
    apply Finset.sum_congr rfl
    intro b hbm
    simp only [Bg, Finset.mem_filter, Finset.mem_univ, true_and] at hbm
    obtain ⟨u, hu, _⟩ := hbm
    rw [if_pos ⟨u, hu⟩]
  have hsumc : ∑ _b ∈ Bg M S T g, Fintype.card (Vec k)
      = Fintype.card (Vec k) * (Bg M S T g).card := by simp [mul_comm]
  have hsumW : ∑ _u : Vec k, ∑ i ∈ S, wt M i = Fintype.card (Vec k) * ∑ i ∈ S, wt M i := by
    simp [Finset.card_univ]
  have hpos : 0 < Fintype.card (Vec k) := Fintype.card_pos
  have h1 : Fintype.card (Vec k) * (Bg M S T g).card
      = Fintype.card (Vec k) * ∑ i ∈ S, wt M i := by
    rw [← hsumc, ← hsumW, ← hl, ← hr, hdc]
  exact Nat.eq_of_mul_eq_mul_left hpos h1

theorem Bg_injective (hST : S ≠ T) : Function.Injective (Bg M S T) := by
  intro g g2 h
  funext q
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have h1 := Rset_Bg M S T g u
  have h2 := Rset_Bg M S T g2 u
  rw [h] at h1
  have h3 : cg M S T g u = cg M S T g2 u := h1.symm.trans h2
  unfold cg at h3
  cases hg : g (Submodule.Quotient.mk u) <;> cases hg2 : g2 (Submodule.Quotient.mk u) <;>
    simp_all

end Main

section Build
variable {n k t m : ℕ} (row : Fin m → Vec n →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
  (M : Fin m → Vec k →ₗ[ZMod 2] Vec t) (S T : Finset (Fin m))

theorem zmod2_ne (a b : ZMod 2) : a = b + 1 ↔ a ≠ b := by revert a b; decide

theorem zmod2_one (a : ZMod 2) : a ≠ 1 → a = 0 := by revert a; decide

theorem zmod2_dec (a b : ZMod 2) : decide (a = 1) = decide (b = 1) → a = b := by
  revert a b; decide

theorem zmod2_ite (v : ZMod 2) : (if decide (v = 1) = true then (1 : ZMod 2) else 0) = v := by
  revert v; decide

theorem zmod2_par (a b : ZMod 2) : a = b + 1 ↔ a + b = 1 := by revert a b; decide

def failq (i : Fin m) : Vec n × Vec k → Bool := fun z => decide (row i z.1 = rhs i + 1)

theorem failq_mem (i : Fin m) : failq (k := k) row rhs i ∈ Queries (Vec n × Vec k) :=
  ⟨(row i).comp (LinearMap.fst (ZMod 2) (Vec n) (Vec k)), rhs i + 1, rfl⟩

theorem failq_iff (i : Fin m) (z : Vec n × Vec k) :
    failq row rhs i z = true ↔ row i z.1 ≠ rhs i := by
  simp only [failq, decide_eq_true_eq]; exact zmod2_ne _ _

def coordq (i : Fin m) (j : Fin t) : Vec n × Vec k → Bool := fun z => decide (M i z.2 j = 1)

theorem coordq_mem (i : Fin m) (j : Fin t) :
    coordq (n := n) M i j ∈ Queries (Vec n × Vec k) :=
  ⟨(LinearMap.proj j).comp ((M i).comp (LinearMap.snd (ZMod 2) (Vec n) (Vec k))), 1, rfl⟩

def coordQ (i : Fin m) : List (Vec n × Vec k → Bool) := List.ofFn (coordq M i)

def yOf (bs : List Bool) : Vec t := fun j => if bs.getD j.val false then 1 else 0

theorem yOf_sig (i : Fin m) (z : Vec n × Vec k) :
    yOf ((coordQ (n := n) M i).map (fun f => f z)) = M i z.2 := by
  funext j
  have h : ((coordQ (n := n) M i).map (fun f => f z)).getD j.val false
      = decide (M i z.2 j = 1) := by
    simp [coordQ, coordq, List.getD_eq_getElem?_getD]
  simp only [yOf, h]
  exact zmod2_ite _

def obsT (i : Fin m) (D : Finset (Vec n × Vec k)) : DT (Vec n × Vec k) (Fin m × Vec t) :=
  DT.readQ (coordQ M i) D (fun bs => DT.leaf (i, yOf bs))

theorem run_obsT (i : Fin m) (D : Finset (Vec n × Vec k)) (z : Vec n × Vec k) (hz : z ∈ D) :
    (obsT M i D).run z = (i, M i z.2) := by
  unfold obsT
  rw [DT.run_readQ _ _ _ _ hz]
  simp only [DT.run]
  rw [yOf_sig]

theorem mem_outs_obsT (i : Fin m) (D : Finset (Vec n × Vec k)) (hD : D.Nonempty)
    (o : Fin m × Vec t) (ho : o ∈ (obsT M i D).outs) : ∃ z ∈ D, o = (i, M i z.2) := by
  obtain ⟨z, hz, h⟩ := DT.mem_outs_readQ _ _ _ hD o ho
  refine ⟨z, hz, ?_⟩
  simp only [DT.outs, List.mem_singleton] at h
  rw [h, yOf_sig]

theorem nodup_outs_obsT (i : Fin m) (D : Finset (Vec n × Vec k)) (hD : D.Nonempty) :
    (obsT M i D).outs.Nodup := by
  apply DT.nodup_outs_readQ _ _ _ hD
  · intro z _; simp [DT.outs]
  · intro z _ z2 _ hne o ho1 ho2
    simp only [DT.outs, List.mem_singleton] at ho1 ho2
    rw [yOf_sig] at ho1 ho2
    apply hne
    have h1 : M i z.2 = M i z2.2 := (Prod.mk.inj (ho1.symm.trans ho2)).2
    simp only [coordQ, List.map_ofFn]
    congr 1
    funext j
    simp [coordq, h1]

theorem aff_obsT (i : Fin m) (D : Finset (Vec n × Vec k)) :
    (obsT M i D).Aff (Queries (Vec n × Vec k)) := by
  apply DT.aff_readQ
  · intro f hf
    simp only [coordQ, List.mem_ofFn] at hf
    obtain ⟨j, rfl⟩ := hf
    exact coordq_mem M i j
  · intro bs; simp only [DT.Aff]

noncomputable def cosL : List (Vec k →ₗ[ZMod 2] ZMod 2) :=
  Classical.choose (exists_separating (hidden M S T))

theorem cosL_spec (u u2 : Vec k) :
    (∀ l ∈ cosL M S T, l u = l u2) ↔ u - u2 ∈ hidden M S T :=
  Classical.choose_spec (exists_separating (hidden M S T)) u u2

noncomputable def cosQ : List (Vec n × Vec k → Bool) :=
  (cosL M S T).map (fun l z => decide (l z.2 = 1))

noncomputable def cosSig (z : Vec n × Vec k) : List Bool :=
  (cosQ (n := n) M S T).map (fun f => f z)

theorem cosSig_eq_iff (z z2 : Vec n × Vec k) :
    cosSig M S T z = cosSig M S T z2 ↔
      (Submodule.Quotient.mk z.2 : Vec k ⧸ hidden M S T) = Submodule.Quotient.mk z2.2 := by
  rw [Submodule.Quotient.eq, ← cosL_spec]
  simp only [cosSig, cosQ, List.map_map, List.map_inj_left, Function.comp_apply]
  constructor
  · intro h l hl; exact zmod2_dec _ _ (h l hl)
  · intro h l hl; rw [h l hl]

theorem mem_cosD (z : Vec n × Vec k) :
    z ∈ Finset.univ.filter (fun w : Vec n × Vec k => cosSig M S T w = cosSig M S T z) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ z, rfl⟩

theorem cosQ_mem (f : Vec n × Vec k → Bool) (hf : f ∈ cosQ (n := n) M S T) :
    f ∈ Queries (Vec n × Vec k) := by
  simp only [cosQ, List.mem_map] at hf
  obtain ⟨l, _, rfl⟩ := hf
  exact ⟨l.comp (LinearMap.snd (ZMod 2) (Vec n) (Vec k)), 1, rfl⟩

open Classical in
noncomputable def partOf (g : (Vec k ⧸ hidden M S T) → Bool) (bs : List Bool) :
    Finset (Fin m) :=
  if ∃ w : Vec n × Vec k, cosSig M S T w = bs ∧ g (Submodule.Quotient.mk w.2) = true
  then S \ T else T \ S

theorem partOf_sig (g : (Vec k ⧸ hidden M S T) → Bool) (z : Vec n × Vec k) :
    partOf (n := n) M S T g (cosSig M S T z)
      = if g (Submodule.Quotient.mk z.2) then S \ T else T \ S := by
  classical
  unfold partOf
  by_cases hg : g (Submodule.Quotient.mk z.2) = true
  · rw [if_pos ⟨z, rfl, hg⟩, if_pos hg]
  · rw [if_neg hg, if_neg]
    rintro ⟨w, hw, hgw⟩
    rw [cosSig_eq_iff] at hw
    rw [hw] at hgw
    exact hg hgw

theorem partOf_sub (g : (Vec k ⧸ hidden M S T) → Bool) (bs : List Bool) :
    partOf (n := n) M S T g bs ⊆ (S \ T) ∪ (T \ S) := by
  unfold partOf
  split_ifs
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

theorem partOf_nonempty (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (g : (Vec k ⧸ hidden M S T) → Bool) (bs : List Bool) :
    (partOf (n := n) M S T g bs).Nonempty := by
  unfold partOf
  split_ifs
  · exact sdiff_nonempty_of_wt M hST (wS_eq_wT row rhs M S T hb)
  · exact sdiff_nonempty_of_wt M (Ne.symm hST) (wS_eq_wT row rhs M S T hb).symm

theorem partOf_toList_ne (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (g : (Vec k ⧸ hidden M S T) → Bool) (bs : List Bool) :
    (partOf (n := n) M S T g bs).toList ≠ [] := by
  intro h
  rw [Finset.toList_eq_nil] at h
  exact (partOf_nonempty row rhs M S T hST hb g bs).ne_empty h

noncomputable def evenK (g : (Vec k ⧸ hidden M S T) → Bool)
    (d : DT (Vec n × Vec k) (Fin m × Vec t)) (bs : List Bool) :
    DT (Vec n × Vec k) (Fin m × Vec t) :=
  DT.scan (failq row rhs)
    (fun i => obsT M i (Finset.univ.filter (fun w => cosSig M S T w = bs))) d
    (partOf (n := n) M S T g bs).toList

noncomputable def evenT (g : (Vec k ⧸ hidden M S T) → Bool)
    (d : DT (Vec n × Vec k) (Fin m × Vec t)) : DT (Vec n × Vec k) (Fin m × Vec t) :=
  DT.readQ (cosQ M S T) Finset.univ (evenK row rhs M S T g d)

noncomputable def oddT (d : DT (Vec n × Vec k) (Fin m × Vec t)) :
    DT (Vec n × Vec k) (Fin m × Vec t) :=
  DT.scan (failq row rhs) (fun i => obsT M i Finset.univ) d (S ∩ T).toList

def parq : Vec n × Vec k → Bool :=
  fun z => decide ((∑ i ∈ S ∩ T, row i) z.1 = (∑ i ∈ S ∩ T, rhs i) + 1)

theorem parq_mem : parq (k := k) row rhs S T ∈ Queries (Vec n × Vec k) :=
  ⟨(∑ i ∈ S ∩ T, row i).comp (LinearMap.fst (ZMod 2) (Vec n) (Vec k)),
    (∑ i ∈ S ∩ T, rhs i) + 1, rfl⟩

theorem parq_iff (z : Vec n × Vec k) :
    parq row rhs S T z = true ↔ ∑ i ∈ S ∩ T, (row i z.1 + rhs i) = 1 := by
  simp only [parq, decide_eq_true_eq, Finset.sum_add_distrib, LinearMap.sum_apply]
  exact zmod2_par _ _

noncomputable def fullT (g : (Vec k ⧸ hidden M S T) → Bool)
    (d : DT (Vec n × Vec k) (Fin m × Vec t)) : DT (Vec n × Vec k) (Fin m × Vec t) :=
  if (S ∩ T).Nonempty then
    DT.node (parq row rhs S T) (oddT row rhs M S T d) (evenT row rhs M S T g d)
  else evenT row rhs M S T g d

theorem sum_fail_of_oddDep (P : Finset (Fin m)) (hP : OddDep row rhs P) (x : Vec n) :
    ∑ i ∈ P, (row i x + rhs i) = 1 := by
  have h1 : (∑ i ∈ P, row i) = 0 := hP.1
  have h2 : (∑ i ∈ P, rhs i) = 1 := hP.2
  rw [Finset.sum_add_distrib, ← LinearMap.sum_apply, h1, h2]
  simp

theorem exists_fail (A : Finset (Fin m)) (x : Vec n)
    (h : ∑ i ∈ A, (row i x + rhs i) = 1) : ∃ i ∈ A, row i x ≠ rhs i := by
  by_contra hne
  simp only [not_exists, not_and, not_not] at hne
  have h0 : ∑ i ∈ A, (row i x + rhs i) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hne i hi]; exact CharTwo.add_self_eq_zero _)
  rw [h0] at h
  exact zero_ne_one h

theorem run_evenK (hb : Best2 row rhs M S T) (g : (Vec k ⧸ hidden M S T) → Bool)
    (d : DT (Vec n × Vec k) (Fin m × Vec t)) (z : Vec n × Vec k)
    (hz : ∑ i ∈ S ∩ T, (row i z.1 + rhs i) = 0) :
    Answer row rhs M z ((evenK row rhs M S T g d (cosSig M S T z)).run z) := by
  have hpart : ∃ i ∈ (partOf (n := n) M S T g (cosSig M S T z)).toList,
      failq row rhs i z = true := by
    rw [partOf_sig]
    have hS := sum_fail_of_oddDep row rhs S (best_S row rhs M S T hb).1 z.1
    have hT := sum_fail_of_oddDep row rhs T (best_T row rhs M S T hb).1 z.1
    rw [← Finset.sum_inter_add_sum_sdiff S T, hz, zero_add] at hS
    rw [← Finset.sum_inter_add_sum_sdiff T S, Finset.inter_comm, hz, zero_add] at hT
    split_ifs
    · obtain ⟨i, hi, hf⟩ := exists_fail row rhs _ z.1 hS
      exact ⟨i, Finset.mem_toList.mpr hi, (failq_iff row rhs i z).mpr hf⟩
    · obtain ⟨i, hi, hf⟩ := exists_fail row rhs _ z.1 hT
      exact ⟨i, Finset.mem_toList.mpr hi, (failq_iff row rhs i z).mpr hf⟩
  obtain ⟨i, hi, hf, hrun⟩ := DT.run_scan (failq row rhs)
    (fun i => obsT M i (Finset.univ.filter (fun w => cosSig M S T w = cosSig M S T z))) d _ z hpart
  unfold evenK
  rw [hrun, run_obsT M i _ z (mem_cosD M S T z)]
  exact ⟨(failq_iff row rhs i z).mp hf, rfl⟩

theorem run_evenT (hb : Best2 row rhs M S T) (g : (Vec k ⧸ hidden M S T) → Bool)
    (d : DT (Vec n × Vec k) (Fin m × Vec t)) (z : Vec n × Vec k)
    (hz : ∑ i ∈ S ∩ T, (row i z.1 + rhs i) = 0) :
    Answer row rhs M z ((evenT row rhs M S T g d).run z) := by
  unfold evenT
  rw [DT.run_readQ _ _ _ _ (Finset.mem_univ z)]
  exact run_evenK row rhs M S T hb g d z hz

theorem run_oddT (d : DT (Vec n × Vec k) (Fin m × Vec t)) (z : Vec n × Vec k)
    (hz : ∑ i ∈ S ∩ T, (row i z.1 + rhs i) = 1) :
    Answer row rhs M z ((oddT row rhs M S T d).run z) := by
  obtain ⟨i, hi, hf⟩ := exists_fail row rhs _ z.1 hz
  obtain ⟨j, hj, hjf, hrun⟩ := DT.run_scan (failq row rhs)
    (fun i => obsT M i Finset.univ) d (S ∩ T).toList z
    ⟨i, Finset.mem_toList.mpr hi, (failq_iff row rhs i z).mpr hf⟩
  unfold oddT
  rw [hrun, run_obsT M j _ z (Finset.mem_univ z)]
  exact ⟨(failq_iff row rhs j z).mp hjf, rfl⟩

theorem run_fullT (hb : Best2 row rhs M S T) (g : (Vec k ⧸ hidden M S T) → Bool)
    (d : DT (Vec n × Vec k) (Fin m × Vec t)) (z : Vec n × Vec k) :
    Answer row rhs M z ((fullT row rhs M S T g d).run z) := by
  unfold fullT
  split_ifs with hC
  · simp only [DT.run]
    split_ifs with hp
    · exact run_oddT row rhs M S T d z ((parq_iff row rhs S T z).mp hp)
    · apply run_evenT row rhs M S T hb g d z
      exact zmod2_one _ (fun h => hp ((parq_iff row rhs S T z).mpr h))
  · apply run_evenT row rhs M S T hb g d z
    rw [Finset.not_nonempty_iff_eq_empty.mp hC]
    simp

theorem mem_outs_evenK (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (g : (Vec k ⧸ hidden M S T) → Bool) (d : DT (Vec n × Vec k) (Fin m × Vec t))
    (z : Vec n × Vec k) (o : Fin m × Vec t)
    (ho : o ∈ (evenK row rhs M S T g d (cosSig M S T z)).outs) :
    ∃ (w : Vec n × Vec k) (i : Fin m), i ∈ partOf (n := n) M S T g (cosSig M S T z) ∧
      cosSig M S T w = cosSig M S T z ∧ o = (i, M i w.2) := by
  unfold evenK at ho
  obtain ⟨i, hi, hio⟩ := DT.mem_outs_scan _ _ d _
    (partOf_toList_ne row rhs M S T hST hb g _) o ho
  obtain ⟨w, hw, rfl⟩ := mem_outs_obsT M i _
    ⟨z, mem_cosD M S T z⟩ o hio
  exact ⟨w, i, Finset.mem_toList.mp hi, (Finset.mem_filter.mp hw).2, rfl⟩

theorem nodup_evenK (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (g : (Vec k ⧸ hidden M S T) → Bool) (d : DT (Vec n × Vec k) (Fin m × Vec t))
    (z : Vec n × Vec k) : (evenK row rhs M S T g d (cosSig M S T z)).outs.Nodup := by
  unfold evenK
  have hD : (Finset.univ.filter (fun w : Vec n × Vec k =>
      cosSig M S T w = cosSig M S T z)).Nonempty :=
    ⟨z, mem_cosD M S T z⟩
  apply DT.nodup_outs_scan _ _ d _ (partOf_toList_ne row rhs M S T hST hb g _)
    (Finset.nodup_toList _)
  · intro i _; exact nodup_outs_obsT M i _ hD
  · intro i _ j _ hij o ho1 ho2
    obtain ⟨w1, _, h1⟩ := mem_outs_obsT M i _ hD o ho1
    obtain ⟨w2, _, h2⟩ := mem_outs_obsT M j _ hD o ho2
    exact hij (Prod.mk.inj (h1.symm.trans h2)).1

theorem mem_Bg_of_evenK (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (g : (Vec k ⧸ hidden M S T) → Bool) (d : DT (Vec n × Vec k) (Fin m × Vec t))
    (z : Vec n × Vec k) (o : Fin m × Vec t)
    (ho : o ∈ (evenK row rhs M S T g d (cosSig M S T z)).outs) : o ∈ Bg M S T g := by
  classical
  obtain ⟨w, i, hi, hsig, rfl⟩ := mem_outs_evenK row rhs M S T hST hb g d z o ho
  simp only [Bg, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨w.2, rfl, ?_⟩
  show i ∈ cg M S T g w.2
  rw [cosSig_eq_iff] at hsig
  rw [partOf_sig] at hi
  unfold cg
  rw [hsig]
  split_ifs at hi ⊢
  · exact (Finset.mem_sdiff.mp hi).1
  · exact (Finset.mem_sdiff.mp hi).1

theorem nodup_evenT (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (g : (Vec k ⧸ hidden M S T) → Bool) (d : DT (Vec n × Vec k) (Fin m × Vec t)) :
    (evenT row rhs M S T g d).outs.Nodup := by
  unfold evenT
  apply DT.nodup_outs_readQ _ _ _ Finset.univ_nonempty
  · intro z _; exact nodup_evenK row rhs M S T hST hb g d z
  · intro z _ z2 _ hne o ho1 ho2
    obtain ⟨w, i, hi, hsig, h1⟩ := mem_outs_evenK row rhs M S T hST hb g d z o ho1
    obtain ⟨w2, j, hj, hsig2, h2⟩ := mem_outs_evenK row rhs M S T hST hb g d z2 o ho2
    have hij : i = j := (Prod.mk.inj (h1.symm.trans h2)).1
    subst hij
    have hM : M i w.2 = M i w2.2 := (Prod.mk.inj (h1.symm.trans h2)).2
    have hd : i ∈ (S \ T) ∪ (T \ S) := partOf_sub M S T g _ hi
    have hmk : (Submodule.Quotient.mk w.2 : Vec k ⧸ hidden M S T)
        = Submodule.Quotient.mk w2.2 := by
      rw [Submodule.Quotient.eq]
      apply ker_le_hidden M S T hd
      rw [LinearMap.mem_ker, map_sub, hM, sub_self]
    have h3 := (cosSig_eq_iff M S T w w2).mpr hmk
    apply hne
    show cosSig M S T z = cosSig M S T z2
    rw [← hsig, ← hsig2]
    exact h3

theorem mem_outs_evenT (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (g : (Vec k ⧸ hidden M S T) → Bool) (d : DT (Vec n × Vec k) (Fin m × Vec t))
    (o : Fin m × Vec t) (ho : o ∈ (evenT row rhs M S T g d).outs) :
    o ∈ Bg M S T g ∧ o.1 ∈ (S \ T) ∪ (T \ S) := by
  unfold evenT at ho
  obtain ⟨z, -, hz⟩ := DT.mem_outs_readQ _ _ _ Finset.univ_nonempty o ho
  refine ⟨mem_Bg_of_evenK row rhs M S T hST hb g d z o hz, ?_⟩
  obtain ⟨w, i, hi, -, rfl⟩ := mem_outs_evenK row rhs M S T hST hb g d z o hz
  exact partOf_sub M S T g _ hi

theorem mem_outs_oddT (hC : (S ∩ T).Nonempty) (d : DT (Vec n × Vec k) (Fin m × Vec t))
    (o : Fin m × Vec t) (ho : o ∈ (oddT row rhs M S T d).outs) :
    ∃ i ∈ S ∩ T, ∃ w : Vec n × Vec k, o = (i, M i w.2) := by
  unfold oddT at ho
  have hne : (S ∩ T).toList ≠ [] := by
    intro h; rw [Finset.toList_eq_nil] at h; exact hC.ne_empty h
  obtain ⟨i, hi, hio⟩ := DT.mem_outs_scan _ _ d _ hne o ho
  obtain ⟨w, -, rfl⟩ := mem_outs_obsT M i _ Finset.univ_nonempty o hio
  exact ⟨i, Finset.mem_toList.mp hi, w, rfl⟩

theorem nodup_oddT (hC : (S ∩ T).Nonempty) (d : DT (Vec n × Vec k) (Fin m × Vec t)) :
    (oddT row rhs M S T d).outs.Nodup := by
  unfold oddT
  have hne : (S ∩ T).toList ≠ [] := by
    intro h; rw [Finset.toList_eq_nil] at h; exact hC.ne_empty h
  apply DT.nodup_outs_scan _ _ d _ hne (Finset.nodup_toList _)
  · intro i _; exact nodup_outs_obsT M i _ Finset.univ_nonempty
  · intro i _ j _ hij o ho1 ho2
    obtain ⟨w1, _, h1⟩ := mem_outs_obsT M i _ Finset.univ_nonempty o ho1
    obtain ⟨w2, _, h2⟩ := mem_outs_obsT M j _ Finset.univ_nonempty o ho2
    exact hij (Prod.mk.inj (h1.symm.trans h2)).1

theorem aff_evenT (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (g : (Vec k ⧸ hidden M S T) → Bool) (d : DT (Vec n × Vec k) (Fin m × Vec t)) :
    (evenT row rhs M S T g d).Aff (Queries (Vec n × Vec k)) := by
  unfold evenT
  apply DT.aff_readQ
  · exact cosQ_mem M S T
  · intro bs
    unfold evenK
    apply DT.aff_scan _ _ _ d _ (partOf_toList_ne row rhs M S T hST hb g bs)
    · intro i _; exact failq_mem row rhs i
    · intro i _; exact aff_obsT M i _

theorem aff_oddT (hC : (S ∩ T).Nonempty) (d : DT (Vec n × Vec k) (Fin m × Vec t)) :
    (oddT row rhs M S T d).Aff (Queries (Vec n × Vec k)) := by
  unfold oddT
  have hne : (S ∩ T).toList ≠ [] := by
    intro h; rw [Finset.toList_eq_nil] at h; exact hC.ne_empty h
  apply DT.aff_scan _ _ _ d _ hne
  · intro i _; exact failq_mem row rhs i
  · intro i _; exact aff_obsT M i _

theorem fullT_spec (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (g : (Vec k ⧸ hidden M S T) → Bool) (d : DT (Vec n × Vec k) (Fin m × Vec t)) :
    (fullT row rhs M S T g d).Aff (Queries (Vec n × Vec k)) ∧
    (∀ z, Answer row rhs M z ((fullT row rhs M S T g d).run z)) ∧
    (fullT row rhs M S T g d).outs.Nodup ∧
    ∀ o ∈ (fullT row rhs M S T g d).outs, o ∈ Bg M S T g := by
  classical
  refine ⟨?_, run_fullT row rhs M S T hb g d, ?_, ?_⟩
  · unfold fullT
    split_ifs with hC
    · simp only [DT.Aff]
      exact ⟨parq_mem row rhs S T, aff_oddT row rhs M S T hC d,
        aff_evenT row rhs M S T hST hb g d⟩
    · exact aff_evenT row rhs M S T hST hb g d
  · unfold fullT
    split_ifs with hC
    · simp only [DT.outs]
      refine List.Nodup.append (nodup_oddT row rhs M S T hC d)
        (nodup_evenT row rhs M S T hST hb g d) ?_
      intro o ho1 ho2
      obtain ⟨i, hi, w, rfl⟩ := mem_outs_oddT row rhs M S T hC d o ho1
      have h2 := (mem_outs_evenT row rhs M S T hST hb g d _ ho2).2
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at h2 hi
      tauto
    · exact nodup_evenT row rhs M S T hST hb g d
  · intro o ho
    unfold fullT at ho
    split_ifs at ho with hC
    · simp only [DT.outs, List.mem_append] at ho
      rcases ho with ho | ho
      · obtain ⟨i, hi, w, rfl⟩ := mem_outs_oddT row rhs M S T hC d o ho
        simp only [Bg, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨w.2, rfl, ?_⟩
        show i ∈ cg M S T g w.2
        simp only [Finset.mem_inter] at hi
        rcases cg_cases M S T g w.2 with h | h <;> rw [h] <;> tauto
      · exact (mem_outs_evenT row rhs M S T hST hb g d o ho).1
    · exact (mem_outs_evenT row rhs M S T hST hb g d o ho).1

theorem realizable_Bg (hST : S ≠ T) (hb : Best2 row rhs M S T)
    (g : (Vec k ⧸ hidden M S T) → Bool) :
    Realizable row rhs M (∑ i ∈ S, wt M i) (Bg M S T g) := by
  obtain ⟨i0, _⟩ := sdiff_nonempty_of_wt M hST (wS_eq_wT row rhs M S T hb)
  obtain ⟨haff, hrun, hnd, hsub⟩ :=
    fullT_spec row rhs M S T hST hb g (DT.leaf (i0, 0))
  obtain ⟨N, J, q, out, hsh, hq, hout, hcard, him⟩ :=
    DT.bridge (Queries (Vec n × Vec k)) _ haff
  have hc : Cert (Queries (Vec n × Vec k)) (Answer row rhs M) N J q out :=
    ⟨hsh, hq, fun p hp x hx => by rw [hout p hp x hx]; exact hrun x⟩
  have hsubF : (fullT row rhs M S T g (DT.leaf (i0, 0))).outs.toFinset ⊆ Bg M S T g :=
    fun o ho => hsub o (List.mem_toFinset.mp ho)
  have hlow : ∑ i ∈ S, wt M i ≤ ((N \ J).image out).card := by
    apply card_lower M
    intro u
    obtain ⟨P, hPs, hPo⟩ := cert_oddDep row rhs M N J q out hc u
    exact le_trans ((best_S row rhs M S T hb).2 P hPo) (Finset.sum_le_sum_of_subset hPs)
  have heq : (fullT row rhs M S T g (DT.leaf (i0, 0))).outs.toFinset = Bg M S T g :=
    Finset.eq_of_subset_of_card_le hsubF
      (by rw [card_Bg row rhs M S T hb g, ← him]; exact hlow)
  refine ⟨N, J, q, out, hc, ?_, by rw [him, heq]⟩
  rw [hcard, ← List.toFinset_card_of_nodup hnd, heq, card_Bg row rhs M S T hb g]

theorem main_count (hST : S ≠ T) (hb : Best2 row rhs M S T) :
    Nat.card {B : Finset (Fin m × Vec t) // Realizable row rhs M (∑ i ∈ S, wt M i) B}
      = 2 ^ Nat.card (Vec k ⧸ hidden M S T) := by
  have e : ((Vec k ⧸ hidden M S T) → Bool) ≃
      {B : Finset (Fin m × Vec t) // Realizable row rhs M (∑ i ∈ S, wt M i) B} :=
    Equiv.ofBijective (fun g => ⟨Bg M S T g, realizable_Bg row rhs M S T hST hb g⟩)
      ⟨fun g g2 h => Bg_injective M S T hST (congrArg Subtype.val h),
        fun B => by
          obtain ⟨g, hg⟩ := Bg_of_realizable row rhs M S T hST hb B.1 B.2
          exact ⟨g, Subtype.ext hg.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_fun]
  simp

end Build

end PEqualNP.Outside.L_pcx_344_aux

theorem PEqualNP.Outside.L_pcx_344 : (∀ (n k t : ℕ),
  let X := Fin n → ZMod 2
  let U := Fin k → ZMod 2
  let Y := Fin t → ZMod 2
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  ∀ (m : ℕ) (row : Fin m → X →ₗ[ZMod 2] ZMod 2) (rhs : Fin m → ZMod 2)
      (M : Fin m → U →ₗ[ZMod 2] Y),
    let oddDep := fun S : Finset (Fin m) => S.sum row = 0 ∧ S.sum rhs = 1
    let wt := fun i : Fin m => 2^(Module.finrank (ZMod 2) (LinearMap.range (M i)))
    let answer := fun (z : X × U) (a : Fin m × Y) => row a.1 z.1 ≠ rhs a.1 ∧ a.2 = M a.1 z.2
    let best := fun S : Finset (Fin m) => oddDep S ∧ ∀ T, oddDep T → S.sum wt ≤ T.sum wt
    ∀ S T : Finset (Fin m), S ≠ T → (∀ P, best P ↔ P = S ∨ P = T) →
      let delta := (S \ T) ∪ (T \ S)
      let hidden := delta.sup (fun i => LinearMap.ker (M i))
      let realizable := fun B : Finset (Fin m × Y) =>
        ∃ (N J : Finset (List Bool)) (q : List Bool → (X × U) → Bool)
          (out : List Bool → Fin m × Y), cert (queries (X × U)) answer N J q out ∧
          (N \ J).card = S.sum wt ∧ (N \ J).image out = B
      Nat.card {B : Finset (Fin m × Y) // realizable B} = 2^(Nat.card (U ⧸ hidden))) := by
  intro n k t X U Y shape queries cert m row rhs M oddDep wt answer best S T hST hbest delta hidden realizable
  exact PEqualNP.Outside.L_pcx_344_aux.main_count row rhs M S T hST hbest
