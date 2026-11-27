import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_626_aux

open Classical

abbrev Vec (n : ℕ) : Type := Fin n → ZMod 2
abbrev Entry (n names : ℕ) : Type := Fin names × Vec n

def Adaptive (n names q : ℕ) (P N : Finset (Entry n names)) : Prop :=
  ∃ (ask : (j : Fin q) → Fin names → (Fin j.val → ZMod 2) → (Vec n →ₗ[ZMod 2] ZMod 2))
    (answers : Entry n names → Fin q → ZMod 2)
    (decode : Fin names → (Fin q → ZMod 2) → Bool),
    (∀ (z : Entry n names) (j : Fin q), answers z j =
      ask j z.1 (fun i => answers z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z.2) ∧
    (∃ p ∈ P, decode p.1 (answers p) = true) ∧
    ∀ z ∈ N, decode z.1 (answers z) = false

lemma adaptive_iff (n names q : ℕ) (P N : Finset (Entry n names)) :
    Adaptive n names q P N ↔
      ∃ p ∈ P, ∃ Q : Vec n →ₗ[ZMod 2] (Fin q → ZMod 2),
        ∀ z ∈ N, z.1 = p.1 → Q z.2 ≠ Q p.2 := by
  constructor
  · rintro ⟨ask, answers, decode, hstep, ⟨p, hpP, hdec_p⟩, hdec_N⟩
    let Q : Vec n →ₗ[ZMod 2] (Fin q → ZMod 2) :=
      LinearMap.pi (fun j : Fin q =>
        ask j p.1 (fun i => answers p ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩))
    refine ⟨p, hpP, Q, ?_⟩
    intro z hzN hz1 hQeq
    have hans_eq : ∀ m, ∀ (hm : m < q), answers z ⟨m, hm⟩ = answers p ⟨m, hm⟩ := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro hm
        have hz_j := hstep z ⟨m, hm⟩
        have hp_j := hstep p ⟨m, hm⟩
        have hpref : (fun i : Fin m => answers z ⟨i.val, Nat.lt_trans i.isLt hm⟩) =
            (fun i : Fin m => answers p ⟨i.val, Nat.lt_trans i.isLt hm⟩) := by
          funext i
          exact ih i.val i.isLt (Nat.lt_trans i.isLt hm)
        rw [hz_j, hz1, hpref]
        have hQj : Q z.2 ⟨m, hm⟩ = Q p.2 ⟨m, hm⟩ := congrFun hQeq ⟨m, hm⟩
        simp only [Q, LinearMap.pi_apply] at hQj
        rw [hQj, ← hp_j]
    have hans : answers z = answers p := by
      funext j
      exact hans_eq j.val j.isLt
    have h1 := hdec_N z hzN
    rw [hz1, hans, hdec_p] at h1
    cases h1
  · rintro ⟨p, hpP, Q, hsep⟩
    let ask : (j : Fin q) → Fin names → (Fin j.val → ZMod 2) → (Vec n →ₗ[ZMod 2] ZMod 2) :=
      fun j _ _ => (LinearMap.proj j).comp Q
    let answers : Entry n names → Fin q → ZMod 2 := fun z => Q z.2
    let decode : Fin names → (Fin q → ZMod 2) → Bool :=
      fun nm ans => decide (nm = p.1 ∧ ans = Q p.2)
    refine ⟨ask, answers, decode, ?_, ⟨p, hpP, by simp [decode, answers]⟩, ?_⟩
    · intro z j
      rfl
    · intro z hzN
      simp only [decode, answers, decide_eq_false_iff_not, not_and]
      intro hz1
      exact hsep z hzN hz1

lemma exists_good_subspace {n q : ℕ} (D : Finset (Vec n))
    (h0 : (0 : Vec n) ∉ D) (hD : D.card + 1 < 2 ^ (q + 1)) :
    ∃ W : Submodule (ZMod 2) (Vec n),
      (∀ w ∈ W, w ∉ D) ∧ Module.finrank (ZMod 2) (Vec n ⧸ W) ≤ q := by
  have hfinV : Module.finrank (ZMod 2) (Vec n) = n := by
    simp [Vec]
  have hstep : ∀ m, ∀ W : Submodule (ZMod 2) (Vec n),
      (∀ w ∈ W, w ∉ D) →
      n - Module.finrank (ZMod 2) W ≤ m →
      ∃ W' : Submodule (ZMod 2) (Vec n),
        (∀ w ∈ W', w ∉ D) ∧ Module.finrank (ZMod 2) (Vec n ⧸ W') ≤ q := by
    intro m
    induction m with
    | zero =>
      intro W hWD hm
      refine ⟨W, hWD, ?_⟩
      have hr := Submodule.finrank_quotient_add_finrank W
      rw [hfinV] at hr
      omega
    | succ m ih =>
      intro W hWD hm
      by_cases hle : Module.finrank (ZMod 2) (Vec n ⧸ W) ≤ q
      · exact ⟨W, hWD, hle⟩
      · have hgt : q + 1 ≤ Module.finrank (ZMod 2) (Vec n ⧸ W) := by omega
        let d := Module.finrank (ZMod 2) (Vec n ⧸ W)
        let e : (Vec n ⧸ W) ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
          (Module.finBasis (ZMod 2) (Vec n ⧸ W)).equivFun
        have hcardQ : Fintype.card (Vec n ⧸ W) = 2 ^ d := by
          rw [Fintype.card_congr e.toEquiv]
          simp
        let bad : Finset (Vec n ⧸ W) := insert 0 (D.image (Submodule.mkQ W))
        have hbad_lt : bad.card < (Finset.univ : Finset (Vec n ⧸ W)).card := by
          have hpow : 2 ^ (q + 1) ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hgt
          have h1 : bad.card ≤ (D.image (Submodule.mkQ W)).card + 1 := Finset.card_insert_le _ _
          have h2 : (D.image (Submodule.mkQ W)).card ≤ D.card := Finset.card_image_le
          rw [Finset.card_univ, hcardQ]
          omega
        have hex : ∃ q0 : Vec n ⧸ W, q0 ∉ bad := by
          by_contra hall
          push Not at hall
          have hsub : (Finset.univ : Finset (Vec n ⧸ W)) ⊆ bad := fun x _ => hall x
          have hle_card := Finset.card_le_card hsub
          omega
        rcases hex with ⟨q0, hq0_not⟩
        have hq0_ne : q0 ≠ 0 := fun h => hq0_not (h ▸ Finset.mem_insert_self _ _)
        have hq0_notD : ∀ x ∈ D, Submodule.mkQ W x ≠ q0 := by
          intro x hxD heq
          apply hq0_not
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hxD, heq⟩)
        rcases Submodule.mkQ_surjective W q0 with ⟨v, hv⟩
        have hv_notW : v ∉ W := by
          intro hvW
          apply hq0_ne
          rw [← hv, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact hvW
        let W1 : Submodule (ZMod 2) (Vec n) := W ⊔ Submodule.span (ZMod 2) {v}
        have hW1D : ∀ x ∈ W1, x ∉ D := by
          intro x hxW1 hxD
          rcases Submodule.mem_sup.mp hxW1 with ⟨w, hwW, y, hySpan, rfl⟩
          rcases Submodule.mem_span_singleton.mp hySpan with ⟨c, rfl⟩
          have hc : c = 0 ∨ c = 1 := by
            fin_cases c
            · exact Or.inl rfl
            · exact Or.inr rfl
          rcases hc with rfl | rfl
          · simp only [zero_smul, add_zero] at hxD
            exact hWD w hwW hxD
          · simp only [one_smul] at hxD
            apply hq0_notD (w + v) hxD
            rw [map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr hwW,
              zero_add, hv]
        have hWlt : W < W1 := by
          refine lt_of_le_of_ne le_sup_left ?_
          intro heq
          apply hv_notW
          rw [heq]
          exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton v))
        have hrank_lt : Module.finrank (ZMod 2) W < Module.finrank (ZMod 2) W1 :=
          Submodule.finrank_lt_finrank_of_lt hWlt
        have hr := Submodule.finrank_quotient_add_finrank W
        rw [hfinV] at hr
        exact ih W1 hW1D (by omega)
  have hbot : ∀ w ∈ (⊥ : Submodule (ZMod 2) (Vec n)), w ∉ D := by
    intro w hw
    simp only [Submodule.mem_bot] at hw
    rw [hw]
    exact h0
  exact hstep n ⊥ hbot (by simp)

lemma threshold_sufficient (n names q : ℕ) (P N : Finset (Entry n names)) (p : Entry n names)
    (hpP : p ∈ P) (hpN : p ∉ N)
    (hcard : (N.filter (fun z => z.1 = p.1)).card + 1 < 2 ^ (q + 1)) :
    Adaptive n names q P N := by
  rw [adaptive_iff]
  let D : Finset (Vec n) := (N.filter (fun z => z.1 = p.1)).image (fun z => z.2 - p.2)
  have h0 : (0 : Vec n) ∉ D := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨z, hz, hsub⟩
    have hzN : z ∈ N := (Finset.mem_filter.mp hz).1
    have hz1 : z.1 = p.1 := (Finset.mem_filter.mp hz).2
    have hz2 : z.2 = p.2 := sub_eq_zero.mp hsub
    have hzp : z = p := Prod.ext hz1 hz2
    exact hpN (hzp ▸ hzN)
  have hDcard : D.card + 1 < 2 ^ (q + 1) := by
    have h1 : D.card ≤ (N.filter (fun z => z.1 = p.1)).card := Finset.card_image_le
    omega
  rcases exists_good_subspace D h0 hDcard with ⟨W, hWD, hrank⟩
  let d := Module.finrank (ZMod 2) (Vec n ⧸ W)
  let e : (Vec n ⧸ W) ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
    (Module.finBasis (ZMod 2) (Vec n ⧸ W)).equivFun
  let pad : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2) :=
    { toFun := fun f j => if h : j.val < d then f ⟨j.val, h⟩ else 0
      map_add' := by
        intro f g
        funext j
        by_cases h : j.val < d <;> simp [h]
      map_smul' := by
        intro c f
        funext j
        by_cases h : j.val < d <;> simp [h] }
  let Q : Vec n →ₗ[ZMod 2] (Fin q → ZMod 2) := (pad.comp e.toLinearMap).comp (Submodule.mkQ W)
  refine ⟨p, hpP, Q, ?_⟩
  intro z hzN hz1 hQeq
  have hQsub : Q (z.2 - p.2) = 0 := by
    rw [map_sub, hQeq, sub_self]
  have he0 : e (Submodule.mkQ W (z.2 - p.2)) = 0 := by
    funext i
    have hiq : i.val < q := lt_of_lt_of_le i.isLt hrank
    have h1 : Q (z.2 - p.2) ⟨i.val, hiq⟩ = 0 := congrFun hQsub ⟨i.val, hiq⟩
    simp only [Q, pad, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearEquiv.coe_coe, i.isLt, ↓reduceDIte, Fin.eta] at h1
    exact h1
  have hmk0 : Submodule.mkQ W (z.2 - p.2) = 0 := by
    apply e.injective
    rw [he0, map_zero]
  have hmemW : z.2 - p.2 ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hmk0
  have hmemD : z.2 - p.2 ∈ D :=
    Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzN, hz1⟩, rfl⟩
  exact hWD (z.2 - p.2) hmemW hmemD

lemma sharpness (n names q : ℕ) (hnames : 0 < names) (hqn : q < n) :
    ∃ P N : Finset (Entry n names), P.card = 1 ∧ Disjoint P N ∧
      N.card + 1 = 2 ^ (q + 1) ∧ ¬ Adaptive n names q P N := by
  let nm0 : Fin names := ⟨0, hnames⟩
  let emb : (Fin (q + 1) → ZMod 2) →ₗ[ZMod 2] Vec n :=
    { toFun := fun x i => if h : i.val < q + 1 then x ⟨i.val, h⟩ else 0
      map_add' := by
        intro x y
        funext i
        by_cases h : i.val < q + 1 <;> simp only [Pi.add_apply, h, ↓reduceDIte, add_zero]
      map_smul' := by
        intro c x
        funext i
        by_cases h : i.val < q + 1 <;>
          simp only [Pi.smul_apply, RingHom.id_apply, h, ↓reduceDIte, smul_zero] }
  have hemb_inj : Function.Injective emb := by
    intro x y hxy
    funext j
    have hjn : j.val < n := lt_of_lt_of_le j.isLt hqn
    have h1 := congrFun hxy ⟨j.val, hjn⟩
    simpa only [emb, LinearMap.coe_mk, AddHom.coe_mk, j.isLt, ↓reduceDIte, Fin.eta] using h1
  let P : Finset (Entry n names) := {(nm0, (0 : Vec n))}
  let N : Finset (Entry n names) :=
    ((Finset.univ : Finset (Fin (q + 1) → ZMod 2)).erase 0).image (fun x => (nm0, emb x))
  refine ⟨P, N, Finset.card_singleton _, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_singleton_left]
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨x, hx, hpair⟩
    have hx0 : x = 0 := hemb_inj (by rw [map_zero]; exact congrArg Prod.snd hpair)
    exact (Finset.mem_erase.mp hx).1 hx0
  · have hinj : Function.Injective (fun x : Fin (q + 1) → ZMod 2 => (nm0, emb x)) := by
      intro x y hxy
      exact hemb_inj (congrArg Prod.snd hxy)
    rw [Finset.card_image_of_injective _ hinj,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have hcard : Fintype.card (Fin (q + 1) → ZMod 2) = 2 ^ (q + 1) := by simp
    rw [hcard]
    have hpos : 1 ≤ 2 ^ (q + 1) := Nat.one_le_two_pow
    omega
  · intro had
    rw [adaptive_iff] at had
    rcases had with ⟨p, hpP, Q, hsep⟩
    have hpeq : p = (nm0, (0 : Vec n)) := Finset.mem_singleton.mp hpP
    subst hpeq
    have hlt : Fintype.card (Fin q → ZMod 2) < Fintype.card (Fin (q + 1) → ZMod 2) := by
      simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
      exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self q)
    rcases Fintype.exists_ne_map_eq_of_card_lt (Q.comp emb) hlt with ⟨x, y, hxy, heq⟩
    let u := x - y
    have hu0 : u ≠ 0 := sub_ne_zero.mpr hxy
    have huN : (nm0, emb u) ∈ N :=
      Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨hu0, Finset.mem_univ _⟩, rfl⟩
    have hQu : Q (emb u) = Q 0 := by
      simp only [u, map_sub, LinearMap.comp_apply] at heq ⊢
      rw [heq, sub_self, map_zero]
    exact hsep (nm0, emb u) huN rfl hQu

theorem main :
    (∀ (n names q : ℕ),
      let V := Fin n → ZMod 2
      let Entry := Fin names × V
      let adaptive := fun (P N : Finset Entry) =>
        ∃ (ask : (j : Fin q) → Fin names → (Fin j.val → ZMod 2) → (V →ₗ[ZMod 2] ZMod 2))
          (answers : Entry → Fin q → ZMod 2) (decode : Fin names → (Fin q → ZMod 2) → Bool),
          (∀ (z : Entry) (j : Fin q), answers z j =
            ask j z.1 (fun i => answers z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z.2) ∧
          (∃ p ∈ P, decode p.1 (answers p) = true) ∧
          ∀ z ∈ N, decode z.1 (answers z) = false
      (∀ P N : Finset Entry, adaptive P N ↔
        ∃ p ∈ P, ∃ Q : V →ₗ[ZMod 2] (Fin q → ZMod 2),
          ∀ z ∈ N, z.1 = p.1 → Q z.2 ≠ Q p.2) ∧
      (∀ (P N : Finset Entry) (p : Entry), p ∈ P → p ∉ N →
        (N.filter (fun z => z.1 = p.1)).card + 1 < 2 ^ (q + 1) → adaptive P N) ∧
      (0 < names → q < n →
        ∃ P N : Finset Entry, P.card = 1 ∧ Disjoint P N ∧
          N.card + 1 = 2 ^ (q + 1) ∧ ¬adaptive P N)) := by
  intro n names q
  exact ⟨adaptive_iff n names q, threshold_sufficient n names q, sharpness n names q⟩

end PEqualNP.Outside.L_lib_626_aux

theorem PEqualNP.Outside.L_lib_626 : (∀ (n names q : ℕ),
  let V := Fin n → ZMod 2
  let Entry := Fin names × V
  let adaptive := fun (P N : Finset Entry) =>
    ∃ (ask : (j : Fin q) → Fin names → (Fin j.val → ZMod 2) → (V →ₗ[ZMod 2] ZMod 2))
      (answers : Entry → Fin q → ZMod 2) (decode : Fin names → (Fin q → ZMod 2) → Bool),
      (∀ (z : Entry) (j : Fin q), answers z j =
        ask j z.1 (fun i => answers z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z.2) ∧
      (∃ p ∈ P, decode p.1 (answers p) = true) ∧
      ∀ z ∈ N, decode z.1 (answers z) = false
  (∀ P N : Finset Entry, adaptive P N ↔
    ∃ p ∈ P, ∃ Q : V →ₗ[ZMod 2] (Fin q → ZMod 2),
      ∀ z ∈ N, z.1 = p.1 → Q z.2 ≠ Q p.2) ∧
  (∀ (P N : Finset Entry) (p : Entry), p ∈ P → p ∉ N →
    (N.filter (fun z => z.1 = p.1)).card + 1 < 2 ^ (q + 1) → adaptive P N) ∧
  (0 < names → q < n →
    ∃ P N : Finset Entry, P.card = 1 ∧ Disjoint P N ∧
      N.card + 1 = 2 ^ (q + 1) ∧ ¬adaptive P N)) := by
  exact PEqualNP.Outside.L_lib_626_aux.main
