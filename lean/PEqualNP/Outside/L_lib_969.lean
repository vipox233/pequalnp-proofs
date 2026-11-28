import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_969

def perp {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (x : (Fin n → ZMod 2)) : Prop :=
  ∀ y ∈ S, (∑ i, y i * x i) = 0

def pivot {n : ℕ} (L : Submodule (ZMod 2) (Fin n → ZMod 2)) (i : Fin n) : Prop :=
  ∃ v ∈ L, v i ≠ 0 ∧ ∀ j, j < i → v j = 0

noncomputable def bit (q : Prop) : ℕ := @ite ℕ q (Classical.propDecidable q) 1 0

theorem bit_le (q : Prop) : bit q ≤ 1 := by
  unfold bit
  split_ifs <;> simp

theorem bit_pos {q : Prop} (h : q) : bit q = 1 := by
  simp [bit, h]

theorem bit_neg {q : Prop} (h : ¬ q) : bit q = 0 := by
  simp [bit, h]

def edgeVec {n : ℕ} (p : Fin n × Fin n) (x : (Fin n → ZMod 2)) : (Fin n → ZMod 2) :=
  fun a => (if a = p.1 then x p.2 else 0) + (if a = p.2 then x p.1 else 0)

theorem z2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

theorem lead {n : ℕ} (v : (Fin n → ZMod 2)) (hv : v ≠ 0) : ∃ i, v i ≠ 0 ∧ ∀ j, j < i → v j = 0 := by
  classical
  have hne : (Finset.univ.filter (fun i => v i ≠ 0)).Nonempty := by
    by_contra h
    apply hv
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨(Finset.univ.filter (fun i => v i ≠ 0)).min' hne, ?_, ?_⟩
  · have h1 := Finset.min'_mem _ hne
    simpa using h1
  · intro j hj
    by_contra hvj
    have hmem : j ∈ Finset.univ.filter (fun i => v i ≠ 0) := by simp [hvj]
    have h1 := Finset.min'_le _ j hmem
    exact absurd hj (not_lt.2 h1)

theorem pivot_count {n : ℕ} (L : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    ∑ i, bit (pivot L i) = Module.finrank (ZMod 2) L := by
  classical
  have hsum : ∑ i, bit (pivot L i) = Fintype.card {i : Fin n // pivot L i} := by
    rw [Fintype.card_subtype, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : pivot L i
    · rw [bit_pos h]
      simp [h]
    · rw [bit_neg h]
      simp [h]
  rw [hsum]
  apply le_antisymm
  · choose c hcL hc1 hc0 using (fun i : {i : Fin n // pivot L i} => i.2)
    have hli : LinearIndependent (ZMod 2) c := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      by_contra hcon
      obtain ⟨i1, hi1⟩ := not_forall.1 hcon
      have hne : (Finset.univ.filter (fun i : {i : Fin n // pivot L i} => g i ≠ 0)).Nonempty :=
        ⟨i1, by simp [hi1]⟩
      obtain ⟨i0, hi0⟩ : ∃ i0, i0 = (Finset.univ.filter
          (fun i : {i : Fin n // pivot L i} => g i ≠ 0)).min' hne := ⟨_, rfl⟩
      have hgi0 : g i0 ≠ 0 := by
        have h1 := Finset.min'_mem _ hne
        rw [← hi0] at h1
        simpa using h1
      have hmin : ∀ i, g i ≠ 0 → i0 ≤ i := by
        intro i hi
        rw [hi0]
        exact Finset.min'_le _ i (by simp [hi])
      have h1 := congrFun hg i0.val
      rw [Finset.sum_apply, Finset.sum_eq_single i0] at h1
      · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
        rcases mul_eq_zero.1 h1 with h | h
        · exact hgi0 h
        · exact hc1 i0 h
      · intro i _ hne'
        by_cases hgi : g i = 0
        · simp [hgi]
        · have hlt : i0 < i := lt_of_le_of_ne (hmin i hgi) (Ne.symm hne')
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [hc0 i i0.val hlt, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h2 : Submodule.span (ZMod 2) (Set.range c) ≤ L :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hcL i)
    have h3 := finrank_span_eq_card hli
    calc Fintype.card {i : Fin n // pivot L i}
        = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c)) := h3.symm
      _ ≤ Module.finrank (ZMod 2) L := Submodule.finrank_mono h2
  · let r : L →ₗ[ZMod 2] ({i : Fin n // pivot L i} → ZMod 2) :=
      (LinearMap.funLeft (ZMod 2) (ZMod 2) Subtype.val) ∘ₗ L.subtype
    have hinj : Function.Injective r := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      by_contra hne
      have hv0 : (v : (Fin n → ZMod 2)) ≠ 0 := fun h => hne (Subtype.ext h)
      obtain ⟨i, hi1, hi0⟩ := lead _ hv0
      have hp : pivot L i := ⟨v, v.2, hi1, hi0⟩
      have h1 := congrFun hv ⟨i, hp⟩
      exact hi1 h1
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using h1

theorem dual_pivot {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (i : Fin n) (h : ¬ pivot S i) :
    ∃ x : (Fin n → ZMod 2), perp S x ∧ x i = 1 ∧ ∀ j, i < j → x j = 0 := by
  classical
  let tr : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearMap.pi (fun j => if j ≤ i then LinearMap.proj j else 0)
  have htr : ∀ (s : (Fin n → ZMod 2)) (j : Fin n), tr s j = if j ≤ i then s j else 0 := by
    intro s j
    by_cases hj : j ≤ i
    · simp [tr, hj]
    · simp [tr, hj]
  have hnot : (fun k : Fin n => if i = k then (1 : ZMod 2) else 0) ∉ S.map tr := by
    rintro ⟨s, hs, hse⟩
    apply h
    refine ⟨s, hs, ?_, ?_⟩
    · have h1 := congrFun hse i
      rw [htr] at h1
      simp only [le_refl, ↓reduceIte] at h1
      rw [h1]
      exact one_ne_zero
    · intro j hj
      have h1 := congrFun hse j
      rw [htr] at h1
      simp only [hj.le, ↓reduceIte] at h1
      rw [h1]
      simp [hj.ne']
  obtain ⟨ψ, hψ1, hψ0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨fun j => if j ≤ i then ψ (fun k => if j = k then 1 else 0) else 0, ?_, ?_, ?_⟩
  · intro s hs
    have h1 : ψ (tr s) = 0 := by
      have h2 : ψ (tr s) ∈ (S.map tr).map ψ := ⟨tr s, ⟨s, hs, rfl⟩, rfl⟩
      rw [hψ0] at h2
      exact h2
    have h3 : (∑ j, s j * (if j ≤ i then ψ (fun k => if j = k then 1 else 0) else 0))
        = ψ (tr s) := by
      rw [LinearMap.pi_apply_eq_sum_univ ψ (tr s)]
      apply Finset.sum_congr rfl
      intro j _
      rw [htr]
      by_cases hj : j ≤ i
      · simp [hj]
      · simp [hj]
    show (∑ j, s j * (if j ≤ i then ψ (fun k => if j = k then 1 else 0) else 0)) = 0
    rw [h3]
    exact h1
  · simp only [le_refl, ↓reduceIte]
    exact z2 _ hψ1
  · intro j hj
    simp [not_le.2 hj]

theorem edge_wt {n : ℕ} (I S : Submodule (ZMod 2) (Fin n → ZMod 2)) (hIS : I ≤ S) (p : Fin n × Fin n)
    (hp : p.1 < p.2) (hok : ∀ x, perp S x → edgeVec p x ∈ I) :
    2 ≤ (bit (pivot I p.1) + bit (pivot S p.1)) + (bit (pivot I p.2) + bit (pivot S p.2)) := by
  have hmono : ∀ i, pivot I i → pivot S i := by
    rintro i ⟨v, hv, h1, h2⟩
    exact ⟨v, hIS hv, h1, h2⟩
  by_cases hSu : pivot S p.1
  · by_cases hSv : pivot S p.2
    · rw [bit_pos hSu, bit_pos hSv]
      omega
    · obtain ⟨x, hx, hx1, hx0⟩ := dual_pivot S p.2 hSv
      have hI : pivot I p.1 := by
        refine ⟨edgeVec p x, hok x hx, ?_, ?_⟩
        · simp [edgeVec, hx1, hp.ne]
        · intro j hj
          have h1 : j ≠ p.1 := hj.ne
          have h2 : j ≠ p.2 := (hj.trans hp).ne
          simp [edgeVec, h1, h2]
      rw [bit_pos hI, bit_pos hSu]
      omega
  · obtain ⟨x, hx, hx1, hx0⟩ := dual_pivot S p.1 hSu
    have hxv : x p.2 = 0 := hx0 p.2 hp
    have hI : pivot I p.2 := by
      refine ⟨edgeVec p x, hok x hx, ?_, ?_⟩
      · simp [edgeVec, hx1, hxv]
      · intro j hj
        have h2 : j ≠ p.2 := hj.ne
        simp [edgeVec, h2, hxv]
    rw [bit_pos hI, bit_pos (hmono _ hI)]
    omega

theorem cs_zero {n : ℕ} (T : Fin n → Prop) : ∀ i, ¬ T i → (0 : (Fin n → ZMod 2)) i = 0 := by
  intro i _
  rfl

theorem cs_add {n : ℕ} (T : Fin n → Prop) (a b : (Fin n → ZMod 2)) (ha : ∀ i, ¬ T i → a i = 0)
    (hb : ∀ i, ¬ T i → b i = 0) : ∀ i, ¬ T i → (a + b) i = 0 := by
  intro i hi
  simp [ha i hi, hb i hi]

theorem cs_smul {n : ℕ} (T : Fin n → Prop) (c : ZMod 2) (a : (Fin n → ZMod 2))
    (ha : ∀ i, ¬ T i → a i = 0) : ∀ i, ¬ T i → (c • a) i = 0 := by
  intro i hi
  simp [ha i hi]

def coordSub {n : ℕ} (T : Fin n → Prop) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  { carrier := {v | ∀ i, ¬ T i → v i = 0}, zero_mem' := cs_zero T,
    smul_mem' := fun c a ha => cs_smul T c a ha, add_mem' := fun {a b} ha hb => cs_add T a b ha hb }

theorem pivot_coord {n : ℕ} (T : Fin n → Prop) (i : Fin n) : pivot (coordSub T) i ↔ T i := by
  constructor
  · rintro ⟨v, hv, h1, _⟩
    by_contra hT
    exact h1 (hv i hT)
  · intro hT
    refine ⟨fun k => if i = k then 1 else 0, ?_, ?_, ?_⟩
    · intro k hk
      have h1 : i ≠ k := by
        rintro rfl
        exact hk hT
      simp [h1]
    · simp
    · intro j hj
      simp [hj.ne']

theorem cover_spaces {n : ℕ} (edges : Finset (Fin n × Fin n)) (w : Fin n → Fin 3)
    (hcov : ∀ p ∈ edges, 2 ≤ (w p.1).val + (w p.2).val) :
    coordSub (fun i => (w i).val = 2) ≤ coordSub (fun i => (w i).val ≠ 0) ∧
    Module.finrank (ZMod 2) (coordSub (fun i : Fin n => (w i).val = 2))
      + Module.finrank (ZMod 2) (coordSub (fun i : Fin n => (w i).val ≠ 0))
      = ∑ i, (w i).val ∧
    ∀ p ∈ edges, ∀ x, perp (coordSub (fun i => (w i).val ≠ 0)) x →
      edgeVec p x ∈ coordSub (fun i => (w i).val = 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv i hi
    apply hv i
    intro h2
    apply hi
    rw [h2]
    norm_num
  · rw [← pivot_count, ← pivot_count, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h3 : (w i).val < 3 := (w i).2
    by_cases h2 : (w i).val = 2
    · have hne : (w i).val ≠ 0 := by omega
      rw [bit_pos ((pivot_coord _ i).2 h2), bit_pos ((pivot_coord (fun i => (w i).val ≠ 0) i).2 hne)]
      omega
    · by_cases h0 : (w i).val = 0
      · rw [bit_neg (fun h => h2 ((pivot_coord (fun i => (w i).val = 2) i).1 h)),
          bit_neg (fun h => ((pivot_coord (fun i => (w i).val ≠ 0) i).1 h) h0)]
        omega
      · rw [bit_neg (fun h => h2 ((pivot_coord (fun i => (w i).val = 2) i).1 h)),
          bit_pos ((pivot_coord (fun i => (w i).val ≠ 0) i).2 h0)]
        omega
  · intro p hp x hx
    have hx0 : ∀ j : Fin n, (w j).val ≠ 0 → x j = 0 := by
      intro j hj
      have hmem : (fun k : Fin n => if j = k then (1 : ZMod 2) else 0)
          ∈ coordSub (fun i => (w i).val ≠ 0) := by
        intro k hk
        have h1 : j ≠ k := by
          rintro rfl
          exact hk hj
        simp [h1]
      have h1 := hx _ hmem
      simpa using h1
    have hc := hcov p hp
    have h31 : (w p.1).val < 3 := (w p.1).2
    have h32 : (w p.2).val < 3 := (w p.2).2
    intro a ha
    have t1 : (if a = p.1 then x p.2 else 0) = 0 := by
      by_cases h1 : a = p.1
      · rw [h1] at ha
        have h2 : x p.2 = 0 := hx0 p.2 (by omega)
        simp [h2]
      · simp [h1]
    have t2 : (if a = p.2 then x p.1 else 0) = 0 := by
      by_cases h1 : a = p.2
      · rw [h1] at ha
        have h2 : x p.1 = 0 := hx0 p.1 (by omega)
        simp [h2]
      · simp [h1]
    show (if a = p.1 then x p.2 else 0) + (if a = p.2 then x p.1 else 0) = 0
    rw [t1, t2, add_zero]

end PEqualNP.Outside.L_lib_969

theorem PEqualNP.Outside.L_lib_969 : (let F := ZMod 2
∀ (n : ℕ) (edges : Finset (Fin n × Fin n)), (∀ p ∈ edges, p.1 < p.2) →
  let perp := fun (S : Submodule F (Fin n → F)) (x : Fin n → F) =>
    ∀ y ∈ S, (∑ i, y i * x i) = 0
  let cover := fun (w : Fin n → Fin 3) =>
    ∀ p ∈ edges, 2 ≤ (w p.1).val + (w p.2).val
  let V := Fin n → F
  let edgeOK := fun (I S : Submodule F V) (p : Fin n × Fin n) =>
    ∀ x, perp S x →
      (fun a => (if a = p.1 then x p.2 else 0) + (if a = p.2 then x p.1 else 0)) ∈ I
  let pivot := fun (L : Submodule F V) (i : Fin n) =>
    ∃ v ∈ L, v i ≠ 0 ∧ ∀ j, j < i → v j = 0
  let bit := fun q : Prop => @ite ℕ q (Classical.propDecidable q) 1 0
  let wt := fun (I S : Submodule F V) (i : Fin n) => bit (pivot I i) + bit (pivot S i)
  (∀ I S : Submodule F V, I ≤ S →
    (∑ i, wt I S i) = Module.finrank F I + Module.finrank F S ∧
      ∀ p ∈ edges, edgeOK I S p → 2 ≤ wt I S p.1 + wt I S p.2) ∧
    ∀ b : ℕ,
      (∃ I S : Submodule F V, I ≤ S ∧ Module.finrank F I + Module.finrank F S ≤ b ∧
        ∀ p ∈ edges, edgeOK I S p) ↔
      ∃ w : Fin n → Fin 3, cover w ∧ (∑ i, (w i).val) ≤ b) := by
  intro F n edges hedges perp cover V edgeOK pivot bit wt
  refine ⟨fun I S hIS => ⟨?_, fun p hp hok => ?_⟩, fun b => ⟨?_, ?_⟩⟩
  · have h1 := PEqualNP.Outside.L_lib_969.pivot_count I
    have h2 := PEqualNP.Outside.L_lib_969.pivot_count S
    rw [← h1, ← h2, ← Finset.sum_add_distrib]
    rfl
  · exact PEqualNP.Outside.L_lib_969.edge_wt I S hIS p (hedges p hp) hok
  · rintro ⟨I, S, hIS, hb, hok⟩
    have hlt : ∀ i : Fin n, PEqualNP.Outside.L_lib_969.bit (PEqualNP.Outside.L_lib_969.pivot I i)
        + PEqualNP.Outside.L_lib_969.bit (PEqualNP.Outside.L_lib_969.pivot S i) < 3 := by
      intro i
      have h1 := PEqualNP.Outside.L_lib_969.bit_le (PEqualNP.Outside.L_lib_969.pivot I i)
      have h2 := PEqualNP.Outside.L_lib_969.bit_le (PEqualNP.Outside.L_lib_969.pivot S i)
      omega
    refine ⟨fun i => ⟨_, hlt i⟩, fun p hp => ?_, ?_⟩
    · exact PEqualNP.Outside.L_lib_969.edge_wt I S hIS p (hedges p hp) (hok p hp)
    · have h1 := PEqualNP.Outside.L_lib_969.pivot_count I
      have h2 := PEqualNP.Outside.L_lib_969.pivot_count S
      rw [← h1, ← h2, ← Finset.sum_add_distrib] at hb
      exact hb
  · rintro ⟨w, hcov, hb⟩
    obtain ⟨h1, h2, h3⟩ := PEqualNP.Outside.L_lib_969.cover_spaces edges w hcov
    exact ⟨_, _, h1, by rw [h2]; exact hb, h3⟩
