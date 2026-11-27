import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25598_aux

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

lemma b2z_eq_one_iff (b : Bool) : b2z b = 1 ↔ b = true := by
  cases b <;> decide

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma zmod2_pow_two (k : ℕ) : (2 : ZMod 2) ^ k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero, ite_false]
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_pow (Nat.succ_ne_zero k)]

lemma b2z_foldl_xor {α : Type*} (l : List α) (f : α → Bool) (init : Bool) :
    b2z ((l.map f).foldl xor init) = b2z init + (l.map (fun a => b2z (f a))).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.foldl_cons, List.sum_cons, ih, b2z_xor]
    ring

lemma b2z_foldl_xor_ofFn {m : ℕ} (f : Fin m → Bool) :
    b2z ((List.ofFn f).foldl xor false) = ∑ i : Fin m, b2z (f i) := by
  have h1 : List.ofFn f = (List.finRange m).map f := List.ofFn_eq_map
  rw [h1, b2z_foldl_xor]
  simp only [b2z, Bool.false_eq_true, ite_false, zero_add]
  have h2 : ((List.finRange m).map (fun a => b2z (f a))).sum = ∑ i : Fin m, b2z (f i) := by
    rw [← Fin.sum_univ_def]
  exact h2

lemma b2z_all_id {α : Type*} (l : List α) (f : α → Bool) :
    b2z ((l.map f).all id) = (l.map (fun a => b2z (f a))).prod := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, id_eq, List.prod_cons, b2z_and, ih]

lemma b2z_all_id_ofFn {m : ℕ} (f : Fin m → Bool) :
    b2z ((List.ofFn f).all id) = ∏ i : Fin m, b2z (f i) := by
  have h1 : List.ofFn f = (List.finRange m).map f := List.ofFn_eq_map
  rw [h1, b2z_all_id]
  have h2 : ((List.finRange m).map (fun a => b2z (f a))).prod = ∏ i : Fin m, b2z (f i) := by
    rw [← Fin.prod_univ_def]
  exact h2

def diffZ {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (d x : α) : ZMod 2 :=
  f x + f (x + d)

def foldDiffZ {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (l : List α) : α → ZMod 2 :=
  l.foldl diffZ f

lemma foldDiffZ_nil {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (x : α) :
    foldDiffZ f [] x = f x := rfl

lemma foldDiffZ_cons {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (d : α) (l : List α) (x : α) :
    foldDiffZ f (d :: l) x = foldDiffZ (diffZ f d) l x := rfl

lemma foldDiffZ_add {α : Type*} [AddCommMonoid α] (f g : α → ZMod 2) (l : List α) (x : α) :
    foldDiffZ (fun y => f y + g y) l x = foldDiffZ f l x + foldDiffZ g l x := by
  induction l generalizing f g x with
  | nil => rfl
  | cons d t ih =>
    simp only [foldDiffZ_cons]
    have hfg : diffZ (fun y => f y + g y) d = fun y => diffZ f d y + diffZ g d y := by
      ext y; simp only [diffZ]; ring
    rw [hfg, ih]

lemma foldDiffZ_zero {α : Type*} [AddCommMonoid α] (l : List α) (x : α) :
    foldDiffZ (fun _ => (0 : ZMod 2)) l x = 0 := by
  induction l generalizing x with
  | nil => rfl
  | cons d t ih =>
    simp only [foldDiffZ_cons]
    have h0 : diffZ (fun _ : α => (0 : ZMod 2)) d = fun _ => 0 := by
      ext y; simp only [diffZ, add_zero]
    rw [h0, ih]

lemma foldDiffZ_const_mul {α : Type*} [AddCommMonoid α] (c : ZMod 2) (f : α → ZMod 2)
    (l : List α) (x : α) :
    foldDiffZ (fun y => c * f y) l x = c * foldDiffZ f l x := by
  induction l generalizing f x with
  | nil => rfl
  | cons d t ih =>
    simp only [foldDiffZ_cons]
    have hcf : diffZ (fun y => c * f y) d = fun y => c * diffZ f d y := by
      ext y; simp only [diffZ]; ring
    rw [hcf, ih]

lemma foldDiffZ_sum {α β : Type*} [AddCommMonoid α] (s : Finset β) (f : β → α → ZMod 2)
    (l : List α) (x : α) :
    foldDiffZ (fun y => ∑ b ∈ s, f b y) l x = ∑ b ∈ s, foldDiffZ (f b) l x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact foldDiffZ_zero l x
  | insert a s ha ih =>
    have h1 : (fun y => ∑ b ∈ insert a s, f b y) = fun y => f a y + ∑ b ∈ s, f b y := by
      ext y; exact Finset.sum_insert ha
    rw [h1, foldDiffZ_add, ih, Finset.sum_insert ha]

lemma foldDiffZ_translate {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (a : α)
    (l : List α) (x : α) :
    foldDiffZ (fun y => f (y + a)) l x = foldDiffZ f l (x + a) := by
  induction l generalizing f x with
  | nil => rfl
  | cons d t ih =>
    simp only [foldDiffZ_cons]
    have ht : diffZ (fun y => f (y + a)) d = fun y => diffZ f d (y + a) := by
      ext y; simp only [diffZ, add_right_comm]
    rw [ht, ih]

lemma foldDiffZ_cons_split {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (d : α)
    (l : List α) (x : α) :
    foldDiffZ f (d :: l) x = foldDiffZ f l x + foldDiffZ f l (x + d) := by
  rw [foldDiffZ_cons]
  have h : diffZ f d = fun y => f y + f (y + d) := rfl
  rw [h, foldDiffZ_add, foldDiffZ_translate]

lemma foldDiffZ_ofFn_eq_sum {α : Type*} [AddCommMonoid α] {m : ℕ} (f : α → ZMod 2)
    (v : Fin m → α) (x : α) :
    foldDiffZ f (List.ofFn v) x = ∑ S : Finset (Fin m), f (x + ∑ i ∈ S, v i) := by
  induction m generalizing x with
  | zero =>
    simp only [List.ofFn_zero, foldDiffZ_nil]
    have hsub : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
      ext S; simp [Finset.eq_empty_of_isEmpty]
    rw [hsub, Finset.sum_singleton, Finset.sum_empty, add_zero]
  | succ m ih =>
    rw [List.ofFn_succ, foldDiffZ_cons_split, ih, ih]
    have hpart : (Finset.univ : Finset (Finset (Fin (m + 1)))) =
        Finset.univ.image (fun S : Finset (Fin m) => S.map ⟨Fin.succ, Fin.succ_injective m⟩) ∪
        Finset.univ.image (fun S : Finset (Fin m) => insert 0 (S.map ⟨Fin.succ, Fin.succ_injective m⟩)) := by
      ext T
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, true_iff]
      let S : Finset (Fin m) := Finset.univ.filter (fun i => i.succ ∈ T)
      have hmap : S.map ⟨Fin.succ, Fin.succ_injective m⟩ = T.erase 0 := by
        ext j
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk, Finset.mem_erase, S]
        refine Fin.cases ?_ ?_ j
        · simp
        · intro i
          constructor
          · rintro ⟨i', hi', hEq⟩
            have : i' = i := Fin.succ_injective m hEq
            subst this
            exact ⟨Fin.succ_ne_zero _, hi'⟩
          · rintro ⟨_, hi⟩
            exact ⟨i, hi, rfl⟩
      by_cases h0 : (0 : Fin (m + 1)) ∈ T
      · right; refine ⟨S, ?_⟩
        rw [hmap, Finset.insert_erase h0]
      · left; refine ⟨S, ?_⟩
        rw [hmap, Finset.erase_eq_of_notMem h0]
    have hdisj : Disjoint
        (Finset.univ.image (fun S : Finset (Fin m) => S.map ⟨Fin.succ, Fin.succ_injective m⟩))
        (Finset.univ.image (fun S : Finset (Fin m) => insert 0 (S.map ⟨Fin.succ, Fin.succ_injective m⟩))) := by
      rw [Finset.disjoint_left]
      intro T h1 h2
      rcases Finset.mem_image.mp h1 with ⟨S1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨S2, _, hEq⟩
      have h0in : (0 : Fin (m + 1)) ∈ S1.map ⟨Fin.succ, Fin.succ_injective m⟩ := by
        rw [← hEq]; exact Finset.mem_insert_self 0 _
      rcases Finset.mem_map.mp h0in with ⟨i, _, hi⟩
      exact Fin.succ_ne_zero i hi
    rw [hpart, Finset.sum_union hdisj]
    have hinj1 : Function.Injective (fun S : Finset (Fin m) => S.map ⟨Fin.succ, Fin.succ_injective m⟩) := by
      intro S1 S2 h
      ext i
      have hi := Finset.ext_iff.mp h i.succ
      simpa using hi
    have hinj2 : Function.Injective (fun S : Finset (Fin m) => insert 0 (S.map ⟨Fin.succ, Fin.succ_injective m⟩)) := by
      intro S1 S2 h
      ext i
      have hi := Finset.ext_iff.mp h i.succ
      simpa [Fin.succ_ne_zero] using hi
    rw [Finset.sum_image (fun a _ b _ h => hinj1 h), Finset.sum_image (fun a _ b _ h => hinj2 h)]
    congr 1
    · apply Finset.sum_congr rfl; intro S _
      rw [Finset.sum_map]; rfl
    · apply Finset.sum_congr rfl; intro S _
      have h0not : (0 : Fin (m + 1)) ∉ S.map ⟨Fin.succ, Fin.succ_injective m⟩ := by
        simp [Fin.succ_ne_zero]
      rw [Finset.sum_insert h0not, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk]
      rw [← add_assoc]

lemma foldDiffZ_comp_addHom {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    (φ : α → β) (hφ : ∀ a b, φ (a + b) = φ a + φ b) (f : β → ZMod 2)
    (l : List α) (x : α) :
    foldDiffZ (fun a => f (φ a)) l x = foldDiffZ f (l.map φ) (φ x) := by
  induction l generalizing f x with
  | nil => rfl
  | cons d t ih =>
    simp only [List.map_cons, foldDiffZ_cons]
    have hd : diffZ (fun a => f (φ a)) d = fun a => diffZ f (φ d) (φ a) := by
      ext a; simp only [diffZ, hφ]
    rw [hd, ih]

lemma foldDiffZ_comp_affine {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    (x0 : β) (φ : α → β) (hφ : ∀ a b, φ (a + b) = φ a + φ b) (f : β → ZMod 2)
    (l : List α) (x : α) :
    foldDiffZ (fun a => f (x0 + φ a)) l x = foldDiffZ f (l.map φ) (x0 + φ x) := by
  have h1 := foldDiffZ_comp_addHom φ hφ (fun b => f (x0 + b)) l x
  have h2 : (fun b => f (x0 + b)) = (fun b => f (b + x0)) := by ext b; rw [add_comm]
  rw [h1, h2, foldDiffZ_translate, add_comm]

def monom {ι : Type*} (S : Finset ι) (x : ι → ZMod 2) : ZMod 2 :=
  ∏ i ∈ S, x i

def ind {ι : Type*} [DecidableEq ι] (T : Finset ι) : ι → ZMod 2 :=
  fun i => if i ∈ T then 1 else 0

lemma eq_ind_supp {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ZMod 2) :
    x = ind (Finset.univ.filter (fun i => x i = 1)) := by
  ext i
  simp only [ind, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases zmod2_cases (x i) with h | h <;> simp [h]

lemma monom_ind {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    monom S (ind T) = if S ⊆ T then 1 else 0 := by
  by_cases hST : S ⊆ T
  · simp only [hST, ite_true, monom, ind]
    apply Finset.prod_eq_one
    intro i hi
    simp only [hST hi, ite_true]
  · simp only [hST, ite_false, monom, ind]
    rw [Finset.not_subset] at hST
    rcases hST with ⟨i, hiS, hiT⟩
    exact Finset.prod_eq_zero hiS (by simp [hiT])

def anf {ι : Type*} [DecidableEq ι] (f : (ι → ZMod 2) → ZMod 2) (S : Finset ι) : ZMod 2 :=
  ∑ T ∈ S.powerset, f (ind T)

lemma anf_add {ι : Type*} [DecidableEq ι] (f g : (ι → ZMod 2) → ZMod 2) (S : Finset ι) :
    anf (fun x => f x + g x) S = anf f S + anf g S := by
  unfold anf
  exact Finset.sum_add_distrib

lemma sum_powerset_between {ι : Type*} [DecidableEq ι] (U X : Finset ι) (hUX : U ⊆ X) :
    (∑ _S ∈ X.powerset.filter (fun S => U ⊆ S), (1 : ZMod 2)) = if U = X then 1 else 0 := by
  have hbij : (X.powerset.filter (fun S => U ⊆ S)).card = (X \ U).powerset.card := by
    refine Finset.card_bij (fun S _ => S \ U) ?_ ?_ ?_
    · intro S hS
      rcases Finset.mem_filter.mp hS with ⟨hSX, _⟩
      exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff (Finset.mem_powerset.mp hSX) le_rfl)
    · intro S1 hS1 S2 hS2 hEq
      have hU1 := (Finset.mem_filter.mp hS1).2
      have hU2 := (Finset.mem_filter.mp hS2).2
      rw [← Finset.sdiff_union_of_subset hU1, ← Finset.sdiff_union_of_subset hU2, hEq]
    · intro R hR
      have hRXU : R ⊆ X \ U := Finset.mem_powerset.mp hR
      refine ⟨R ∪ U, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.subset_union_right⟩, ?_⟩
      · exact Finset.union_subset (hRXU.trans Finset.sdiff_subset) hUX
      · rw [Finset.union_sdiff_cancel_right]
        exact Finset.disjoint_of_subset_left hRXU disjoint_sdiff_self_left
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hbij, Finset.card_powerset]
  have h2 : ((2 ^ (X \ U).card : ℕ) : ZMod 2) = (2 : ZMod 2) ^ (X \ U).card := by push_cast; rfl
  rw [h2, zmod2_pow_two]
  have heq : (X \ U).card = 0 ↔ U = X := by
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h => Finset.Subset.antisymm hUX h, fun h => h ▸ le_rfl⟩
  by_cases h : U = X
  · simp [h]
  · have hne : (X \ U).card ≠ 0 := mt heq.mp h
    simp [h, hne]

lemma anf_eval {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ZMod 2) → ZMod 2)
    (x : ι → ZMod 2) :
    f x = ∑ S : Finset ι, anf f S * monom S x := by
  let X := Finset.univ.filter (fun i => x i = 1)
  have hx : x = ind X := eq_ind_supp x
  rw [hx]
  have h1 : (∑ S : Finset ι, anf f S * monom S (ind X)) = ∑ S ∈ X.powerset, anf f S := by
    simp only [monom_ind, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    congr 1; ext S; simp [Finset.mem_powerset]
  rw [h1]
  unfold anf
  have hswap : (∑ S ∈ X.powerset, ∑ T ∈ S.powerset, f (ind T)) =
      ∑ T ∈ X.powerset, f (ind T) * ∑ S ∈ X.powerset.filter (fun S => T ⊆ S), (1 : ZMod 2) := by
    calc ∑ S ∈ X.powerset, ∑ T ∈ S.powerset, f (ind T)
        = ∑ S ∈ X.powerset, ∑ T ∈ X.powerset, (if T ⊆ S then f (ind T) else 0) := by
          apply Finset.sum_congr rfl; intro S hS
          rw [← Finset.sum_filter]
          congr 1; ext T
          simp only [Finset.mem_powerset, Finset.mem_filter]
          exact ⟨fun hTS => ⟨hTS.trans (Finset.mem_powerset.mp hS), hTS⟩, fun h => h.2⟩
      _ = ∑ T ∈ X.powerset, ∑ S ∈ X.powerset, (if T ⊆ S then f (ind T) else 0) := Finset.sum_comm
      _ = ∑ T ∈ X.powerset, f (ind T) * ∑ S ∈ X.powerset.filter (fun S => T ⊆ S), (1 : ZMod 2) := by
          apply Finset.sum_congr rfl; intro T _
          rw [← Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro S _; ring
  rw [hswap]
  have hcollapse : (∑ T ∈ X.powerset, f (ind T) * ∑ S ∈ X.powerset.filter (fun S => T ⊆ S), (1 : ZMod 2)) =
      ∑ T ∈ X.powerset, if T = X then f (ind T) else 0 := by
    apply Finset.sum_congr rfl; intro T hT
    rw [sum_powerset_between T X (Finset.mem_powerset.mp hT)]
    by_cases hTX : T = X <;> simp [hTX]
  rw [hcollapse, Finset.sum_ite_eq']
  simp

lemma anf_unique {ι : Type*} [Fintype ι] [DecidableEq ι] (c : Finset ι → ZMod 2) (S : Finset ι) :
    anf (fun x => ∑ U : Finset ι, c U * monom U x) S = c S := by
  unfold anf
  have h1 : (∑ T ∈ S.powerset, ∑ U : Finset ι, c U * monom U (ind T)) =
      ∑ T ∈ S.powerset, ∑ U ∈ T.powerset, c U := by
    apply Finset.sum_congr rfl; intro T _
    simp only [monom_ind, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    congr 1; ext U; simp [Finset.mem_powerset]
  rw [h1]
  have hswap : (∑ T ∈ S.powerset, ∑ U ∈ T.powerset, c U) =
      ∑ U ∈ S.powerset, c U * ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (1 : ZMod 2) := by
    calc ∑ T ∈ S.powerset, ∑ U ∈ T.powerset, c U
        = ∑ T ∈ S.powerset, ∑ U ∈ S.powerset, (if U ⊆ T then c U else 0) := by
          apply Finset.sum_congr rfl; intro T hT
          rw [← Finset.sum_filter]
          congr 1; ext U
          simp only [Finset.mem_powerset, Finset.mem_filter]
          exact ⟨fun hUT => ⟨hUT.trans (Finset.mem_powerset.mp hT), hUT⟩, fun h => h.2⟩
      _ = ∑ U ∈ S.powerset, ∑ T ∈ S.powerset, (if U ⊆ T then c U else 0) := Finset.sum_comm
      _ = ∑ U ∈ S.powerset, c U * ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (1 : ZMod 2) := by
          apply Finset.sum_congr rfl; intro U _
          rw [← Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro T _; ring
  rw [hswap]
  have hcollapse : (∑ U ∈ S.powerset, c U * ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (1 : ZMod 2)) =
      ∑ U ∈ S.powerset, if U = S then c U else 0 := by
    apply Finset.sum_congr rfl; intro U hU
    rw [sum_powerset_between U S (Finset.mem_powerset.mp hU)]
    by_cases hUS : U = S <;> simp [hUS]
  rw [hcollapse, Finset.sum_ite_eq']
  simp

lemma anf_eq_zero_of_foldDiffZ_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (f : (ι → ZMod 2) → ZMod 2)
    (hf : ∀ (v : Fin r → (ι → ZMod 2)) (x : ι → ZMod 2), foldDiffZ f (List.ofFn v) x = 0) :
    ∀ T : Finset ι, r ≤ T.card → anf f T = 0 := by
  intro T hTr
  induction hn : T.card using Nat.strong_induction_on generalizing T with
  | ind n ih =>
    subst hn
    rcases Finset.exists_subset_card_eq hTr with ⟨A, hAT, hAcard⟩
    let eA : Fin r ≃ A := (Finset.equivFinOfCardEq hAcard).symm
    let s : Fin r → ι := fun t => (eA t).1
    have hs_inj : Function.Injective s := fun t1 t2 h => eA.injective (Subtype.ext h)
    let v : Fin r → (ι → ZMod 2) := fun t => ind {s t}
    have hv_zero := hf v (ind (T \ A))
    rw [foldDiffZ_ofFn_eq_sum] at hv_zero
    have hsum_vec : ∀ U : Finset (Fin r),
        ind (T \ A) + ∑ t ∈ U, v t = ind ((T \ A) ∪ U.image s) := by
      intro U
      ext i
      simp only [Pi.add_apply, Finset.sum_apply, ind, v, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_image, Finset.mem_singleton]
      have hUsum : (∑ t ∈ U, (if i = s t then (1 : ZMod 2) else 0)) =
          if ∃ t ∈ U, s t = i then 1 else 0 := by
        by_cases h : ∃ t ∈ U, s t = i
        · simp only [h, ite_true]
          rcases h with ⟨t0, ht0U, ht0Eq⟩
          rw [Finset.sum_eq_single t0]
          · simp [ht0Eq]
          · intro t _ hne
            have : i ≠ s t := fun heq => hne (hs_inj (heq.symm.trans ht0Eq.symm))
            simp [this]
          · intro hnot; exact absurd ht0U hnot
        · simp only [h, ite_false]
          apply Finset.sum_eq_zero; intro t ht
          have : i ≠ s t := fun heq => h ⟨t, ht, heq.symm⟩
          simp [this]
      rw [hUsum]
      by_cases hiTA : i ∈ T ∧ i ∉ A
      · have hnotU : ¬ ∃ t ∈ U, s t = i := by
          rintro ⟨t, _, rfl⟩
          exact hiTA.2 (eA t).2
        simp [hiTA, hnotU]
      · by_cases hU : ∃ t ∈ U, s t = i
        · simp [hiTA, hU]
        · simp [hiTA, hU]
    have hbij : (∑ U : Finset (Fin r), f (ind (T \ A) + ∑ t ∈ U, v t)) =
        ∑ Y ∈ T.powerset.filter (fun Y => T \ A ⊆ Y), f (ind Y) := by
      simp_rw [hsum_vec]
      refine Finset.sum_bij (fun U _ => (T \ A) ∪ U.image s) ?_ ?_ ?_ ?_
      · intro U _
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.subset_union_left⟩
        refine Finset.union_subset Finset.sdiff_subset ?_
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨t, _, rfl⟩
        exact hAT (eA t).2
      · intro U1 _ U2 _ hEq
        ext t
        have hm := Finset.ext_iff.mp hEq (s t)
        have hnotTA : s t ∉ T \ A := by
          simp only [Finset.mem_sdiff, not_and, not_not]
          intro _; exact (eA t).2
        simp only [Finset.mem_union, hnotTA, false_or, Finset.mem_image] at hm
        constructor
        · intro ht
          rcases hm.mp ⟨t, ht, rfl⟩ with ⟨t', ht', heq⟩
          exact hs_inj heq ▸ ht'
        · intro ht
          rcases hm.mpr ⟨t, ht, rfl⟩ with ⟨t', ht', heq⟩
          exact hs_inj heq ▸ ht'
      · intro Y hY
        rcases Finset.mem_filter.mp hY with ⟨hYT, hTAY⟩
        have hYT' : Y ⊆ T := Finset.mem_powerset.mp hYT
        refine ⟨Finset.univ.filter (fun t => s t ∈ Y), Finset.mem_univ _, ?_⟩
        ext i
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · rintro (⟨hiT, hiA⟩ | ⟨t, htY, rfl⟩)
          · exact hTAY (Finset.mem_sdiff.mpr ⟨hiT, hiA⟩)
          · exact htY
        · intro hiY
          by_cases hiA : i ∈ A
          · right
            refine ⟨eA.symm ⟨i, hiA⟩, ?_, ?_⟩
            · have : s (eA.symm ⟨i, hiA⟩) = i := by simp [s]
              rw [this]; exact hiY
            · simp [s]
          · left; exact ⟨hYT' hiY, hiA⟩
      · intro U _; rfl
    rw [hbij] at hv_zero
    have hexpand : (∑ Y ∈ T.powerset.filter (fun Y => T \ A ⊆ Y), f (ind Y)) =
        ∑ M ∈ T.powerset.filter (fun M => A ⊆ M), anf f M := by
      have h1 : ∀ Y ∈ T.powerset.filter (fun Y => T \ A ⊆ Y),
          f (ind Y) = ∑ M ∈ T.powerset, if M ⊆ Y then anf f M else 0 := by
        intro Y hY
        have hYT : Y ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hY).1
        rw [anf_eval f (ind Y)]
        simp only [monom_ind, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
        congr 1; ext M
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
        exact ⟨fun hMY => ⟨hMY.trans hYT, hMY⟩, fun h => h.2⟩
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      have h2 : ∀ M ∈ T.powerset,
          (∑ Y ∈ T.powerset.filter (fun Y => T \ A ⊆ Y), if M ⊆ Y then anf f M else 0) =
          if A ⊆ M then anf f M else 0 := by
        intro M hM
        have hMT : M ⊆ T := Finset.mem_powerset.mp hM
        have hfilt : (T.powerset.filter (fun Y => T \ A ⊆ Y)).filter (fun Y => M ⊆ Y) =
            T.powerset.filter (fun Y => (T \ A) ∪ M ⊆ Y) := by
          ext Y; simp only [Finset.mem_filter, Finset.union_subset_iff]; tauto
        rw [← Finset.sum_filter, hfilt]
        have hpull : (∑ Y ∈ T.powerset.filter (fun Y => (T \ A) ∪ M ⊆ Y), anf f M) =
            anf f M * ∑ Y ∈ T.powerset.filter (fun Y => (T \ A) ∪ M ⊆ Y), (1 : ZMod 2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
        rw [hpull, sum_powerset_between ((T \ A) ∪ M) T (Finset.union_subset Finset.sdiff_subset hMT)]
        have heq : (T \ A) ∪ M = T ↔ A ⊆ M := by
          constructor
          · intro h i hiA
            have hiT : i ∈ T := hAT hiA
            rw [← h] at hiT
            rcases Finset.mem_union.mp hiT with h1 | h2
            · exact absurd hiA (Finset.mem_sdiff.mp h1).2
            · exact h2
          · intro hAM
            ext i
            simp only [Finset.mem_union, Finset.mem_sdiff]
            constructor
            · rintro (⟨hiT, _⟩ | hiM)
              · exact hiT
              · exact hMT hiM
            · intro hiT
              by_cases hiA : i ∈ A
              · right; exact hAM hiA
              · left; exact ⟨hiT, hiA⟩
        by_cases hAM : A ⊆ M
        · simp [hAM, heq.mpr hAM]
        · have hne : (T \ A) ∪ M ≠ T := mt heq.mp hAM
          simp [hAM, hne]
      rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]
    rw [hexpand] at hv_zero
    have hTmem : T ∈ T.powerset.filter (fun M => A ⊆ M) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr le_rfl, hAT⟩
    rw [← Finset.add_sum_erase _ _ hTmem] at hv_zero
    have hrest : ∑ M ∈ (T.powerset.filter (fun M => A ⊆ M)).erase T, anf f M = 0 := by
      apply Finset.sum_eq_zero; intro M hM
      have hne : M ≠ T := (Finset.mem_erase.mp hM).1
      rcases Finset.mem_filter.mp (Finset.mem_erase.mp hM).2 with ⟨hMT, hAM⟩
      have hMsub : M ⊂ T := ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hMT, hne⟩
      have hMlt : M.card < T.card := Finset.card_lt_card hMsub
      have hMr : r ≤ M.card := hAcard ▸ Finset.card_le_card hAM
      exact ih M.card hMlt M hMr rfl
    rw [hrest, add_zero] at hv_zero
    exact hv_zero

lemma diffZ_monom {ι : Type*} [DecidableEq ι] (S : Finset ι) (d x : ι → ZMod 2) :
    diffZ (monom S) d x =
      ∑ T ∈ S.powerset.erase S, (∏ i ∈ S \ T, d i) * monom T x := by
  unfold diffZ monom
  simp only [Pi.add_apply]
  have hprod : (∏ i ∈ S, (x i + d i)) =
      ∑ T ∈ S.powerset, (∏ i ∈ T, x i) * (∏ i ∈ S \ T, d i) := by
    rw [Finset.prod_add]
  rw [hprod, ← Finset.add_sum_erase _ _ (Finset.mem_powerset.mpr le_rfl)]
  have hself : (∏ i ∈ S, x i) * (∏ i ∈ S \ S, d i) = ∏ i ∈ S, x i := by simp
  rw [hself]
  have hcancel : (∏ i ∈ S, x i) + ((∏ i ∈ S, x i) +
      ∑ T ∈ S.powerset.erase S, (∏ i ∈ T, x i) * (∏ i ∈ S \ T, d i)) =
      ∑ T ∈ S.powerset.erase S, (∏ i ∈ T, x i) * (∏ i ∈ S \ T, d i) := by
    have h2 : (∏ i ∈ S, x i) + (∏ i ∈ S, x i) = (2 : ZMod 2) * (∏ i ∈ S, x i) := by ring
    have hz : (2 : ZMod 2) = 0 := by decide
    rw [← add_assoc, h2, hz, zero_mul, zero_add]
  rw [hcancel]
  apply Finset.sum_congr rfl; intro T _; ring

lemma foldDiffZ_monom_eq_zero {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (l : List (ι → ZMod 2)) (hcard : S.card < l.length) (x : ι → ZMod 2) :
    foldDiffZ (monom S) l x = 0 := by
  induction l generalizing S x with
  | nil => simp at hcard
  | cons d t ih =>
    rw [foldDiffZ_cons]
    have hdiff : diffZ (monom S) d = fun y => ∑ T ∈ S.powerset.erase S, (∏ i ∈ S \ T, d i) * monom T y := by
      ext y; exact diffZ_monom S d y
    rw [hdiff, foldDiffZ_sum]
    apply Finset.sum_eq_zero; intro T hT
    rw [foldDiffZ_const_mul]
    have hTsub : T ⊂ S := ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp hT).2, (Finset.mem_erase.mp hT).1⟩
    have hTlt : T.card < t.length := by
      have h1 := Finset.card_lt_card hTsub
      simp only [List.length_cons] at hcard
      omega
    rw [ih T hTlt x, mul_zero]

lemma foldDiffZ_monom_const {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (l : List (ι → ZMod 2)) (hcard : S.card = l.length) (x y : ι → ZMod 2) :
    foldDiffZ (monom S) l x = foldDiffZ (monom S) l y := by
  induction l generalizing S x y with
  | nil =>
    simp only [List.length_nil, Finset.card_eq_zero] at hcard
    subst hcard
    rfl
  | cons d t ih =>
    rw [foldDiffZ_cons, foldDiffZ_cons]
    have hdiff : diffZ (monom S) d = fun z => ∑ T ∈ S.powerset.erase S, (∏ i ∈ S \ T, d i) * monom T z := by
      ext z; exact diffZ_monom S d z
    rw [hdiff, foldDiffZ_sum, foldDiffZ_sum]
    apply Finset.sum_congr rfl; intro T hT
    rw [foldDiffZ_const_mul, foldDiffZ_const_mul]
    have hTsub : T ⊂ S := ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp hT).2, (Finset.mem_erase.mp hT).1⟩
    have hTle : T.card ≤ t.length := by
      have h1 := Finset.card_lt_card hTsub
      simp only [List.length_cons] at hcard
      omega
    rcases lt_or_eq_of_le hTle with hlt | heq
    · rw [foldDiffZ_monom_eq_zero T t hlt x, foldDiffZ_monom_eq_zero T t hlt y]
    · rw [ih T heq x y]

def zSign (a : ZMod 2) : ℤ := if a = 1 then -1 else 1

lemma zSign_add (a b : ZMod 2) : zSign (a + b) = zSign a * zSign b := by
  fin_cases a <;> fin_cases b <;> decide

lemma zSign_sum {α : Type*} (s : Finset α) (g : α → ZMod 2) :
    zSign (∑ a ∈ s, g a) = ∏ a ∈ s, zSign (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zSign]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, zSign_add, ih]

lemma card_filter_ones {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Finset ι) :
    ((Finset.univ : Finset (ι → ZMod 2)).filter (fun x => ∀ i ∈ U, x i = 1)).card =
      2 ^ (Fintype.card ι - U.card) := by
  let e : {x : ι → ZMod 2 // ∀ i ∈ U, x i = 1} ≃ ({i : ι // i ∉ U} → ZMod 2) :=
    { toFun := fun x i => x.1 i.1
      invFun := fun y => ⟨fun i => if h : i ∈ U then 1 else y ⟨i, h⟩, fun i hi => by simp [hi]⟩
      left_inv := fun x => by
        ext i
        by_cases h : i ∈ U
        · simp [h, x.2 i h]
        · simp [h]
      right_inv := fun y => by
        ext i
        simp [i.2] }
  have h1 : ((Finset.univ : Finset (ι → ZMod 2)).filter (fun x => ∀ i ∈ U, x i = 1)).card =
      Fintype.card {x : ι → ZMod 2 // ∀ i ∈ U, x i = 1} := by
    rw [Fintype.card_subtype]
  rw [h1, Fintype.card_congr e, Fintype.card_fun, ZMod.card]
  have hcompl : Fintype.card {i : ι // i ∉ U} = Fintype.card ι - U.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hcompl]

lemma signed_sum_anf {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ZMod 2) → ZMod 2) :
    let supp := Finset.univ.filter (fun S : Finset ι => anf f S = 1)
    (∑ x : ι → ZMod 2, zSign (f x)) =
      ∑ A ∈ supp.powerset, (-2 : ℤ) ^ A.card * (2 : ℤ) ^ (Fintype.card ι - (A.biUnion id).card) := by
  intro supp
  have hfx : ∀ x : ι → ZMod 2, f x = ∑ S ∈ supp, monom S x := by
    intro x
    rw [anf_eval f x]
    have h0 : ∀ S : Finset ι, anf f S * monom S x = if anf f S = 1 then monom S x else 0 := by
      intro S
      rcases zmod2_cases (anf f S) with h | h <;> simp [h]
    simp_rw [h0, ← Finset.sum_filter]
    rfl
  have hterm : ∀ x : ι → ZMod 2, zSign (f x) =
      ∑ A ∈ supp.powerset, (-2 : ℤ) ^ A.card *
        (if ∀ i ∈ A.biUnion id, x i = 1 then (1 : ℤ) else 0) := by
    intro x
    rw [hfx x, zSign_sum]
    have hfactor : ∀ S ∈ supp, zSign (monom S x) =
        (if monom S x = 1 then (-2 : ℤ) else 0) + 1 := by
      intro S _
      unfold zSign
      by_cases h : monom S x = 1 <;> simp [h]
    rw [Finset.prod_congr rfl hfactor, Finset.prod_add]
    apply Finset.sum_congr rfl; intro A _
    simp only [Finset.prod_const_one, mul_one]
    have hprod_eq : (∏ S ∈ A, if monom S x = 1 then (-2 : ℤ) else 0) =
        (-2 : ℤ) ^ A.card * (if ∀ i ∈ A.biUnion id, x i = 1 then (1 : ℤ) else 0) := by
      have hall : (∀ S ∈ A, monom S x = 1) ↔ (∀ i ∈ A.biUnion id, x i = 1) := by
        constructor
        · intro h i hi
          rcases Finset.mem_biUnion.mp hi with ⟨S, hSA, hiS⟩
          have hm := h S hSA
          rcases zmod2_cases (x i) with h0 | h1
          · exfalso
            have : monom S x = 0 := Finset.prod_eq_zero hiS h0
            rw [this] at hm
            exact absurd hm (by decide)
          · exact h1
        · intro h S hSA
          unfold monom
          apply Finset.prod_eq_one; intro i hiS
          exact h i (Finset.mem_biUnion.mpr ⟨S, hSA, hiS⟩)
      by_cases hA : ∀ S ∈ A, monom S x = 1
      · have hU := hall.mp hA
        have hite : (if ∀ i ∈ A.biUnion id, x i = 1 then (1 : ℤ) else 0) = 1 := by
          split_ifs
          rfl
        rw [hite, mul_one]
        calc ∏ S ∈ A, (if monom S x = 1 then (-2 : ℤ) else 0)
            = ∏ _S ∈ A, (-2 : ℤ) := Finset.prod_congr rfl (fun S hS => by simp [hA S hS])
          _ = (-2 : ℤ) ^ A.card := Finset.prod_const (-2 : ℤ)
      · have hU : ¬ ∀ i ∈ A.biUnion id, x i = 1 := mt hall.mpr hA
        have hite : (if ∀ i ∈ A.biUnion id, x i = 1 then (1 : ℤ) else 0) = 0 := by
          split_ifs
          rfl
        rw [hite, mul_zero]
        push Not at hA
        rcases hA with ⟨S, hSA, hSne⟩
        exact Finset.prod_eq_zero hSA (by simp [hSne])
    exact hprod_eq
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro A _
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_filter_ones]
  push_cast; rfl

lemma pow_two_dvd_term (p a b : ℕ) (h : p + 1 ≤ a + b) :
    (2 : ℤ) ^ (p + 1) ∣ (-2 : ℤ) ^ a * (2 : ℤ) ^ b := by
  have heq : (-2 : ℤ) ^ a * (2 : ℤ) ^ b = (-1 : ℤ) ^ a * (2 : ℤ) ^ (a + b) := by
    have : (-2 : ℤ) = (-1 : ℤ) * 2 := by ring
    rw [this, mul_pow, mul_assoc, ← pow_add]
  rw [heq]
  have hdvd : (2 : ℤ) ^ (p + 1) ∣ (2 : ℤ) ^ (a + b) := pow_dvd_pow (2 : ℤ) h
  exact dvd_mul_of_dvd_right hdvd _

lemma signed_sum_dvd_of_deg_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (p r : ℕ)
    (hr : 2 ≤ r) (f : (ι → ZMod 2) → ZMod 2)
    (hdeg : ∀ S : Finset ι, r ≤ S.card → anf f S = 0)
    (hdim : p * (r - 1) < Fintype.card ι) :
    (2 : ℤ) ^ (p + 1) ∣ ∑ x : ι → ZMod 2, zSign (f x) := by
  rw [signed_sum_anf f]
  apply Finset.dvd_sum
  intro A hA
  apply pow_two_dvd_term
  have hsub : ∀ S ∈ A, S.card ≤ r - 1 := by
    intro S hSA
    have hSsupp := Finset.mem_powerset.mp hA hSA
    have h1 : anf f S = 1 := (Finset.mem_filter.mp hSsupp).2
    by_contra hge
    push Not at hge
    have hSr : r ≤ S.card := by omega
    rw [hdeg S hSr] at h1
    exact absurd h1 (by decide)
  have hu_le_n : (A.biUnion id).card ≤ Fintype.card ι := Finset.card_le_univ _
  have hu_le_tr : (A.biUnion id).card ≤ A.card * (r - 1) := by
    calc (A.biUnion id).card
        ≤ ∑ S ∈ A, S.card := Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ A, (r - 1) := Finset.sum_le_sum hsub
      _ = A.card * (r - 1) := by simp
  by_cases htp : p + 1 ≤ A.card
  · omega
  · have hle : A.card ≤ p := by omega
    have hmul : A.card * (r - 2) ≤ p * (r - 2) := Nat.mul_le_mul_right (r - 2) hle
    have h1 : A.card * (r - 1) = A.card + A.card * (r - 2) := by
      have : r - 1 = 1 + (r - 2) := by omega
      rw [this, mul_add, mul_one]
    have h2 : p * (r - 1) = p + p * (r - 2) := by
      have : r - 1 = 1 + (r - 2) := by omega
      rw [this, mul_add, mul_one]
    omega

end PEqualNP.Outside.L_meta_25598_aux

theorem PEqualNP.Outside.L_meta_25598 :
    ∀ (p r : ℕ), 0 < p → 2 ≤ r →
      let W := Fin p → Fin r → Bool
      let add := fun (x y : W) (row : Fin p) (col : Fin r) => xor (x row col) (y row col)
      let diff := fun (f : W → Bool) (direction point : W) =>
        xor (f point) (f (add point direction))
      let top := fun (f : W → Bool) (v : Fin r → W) => (List.ofFn v).foldl diff f
      let blocks := fun (word : W) =>
        (List.ofFn (fun block : Fin p => (List.ofFn (word block)).all id)).foldl xor false
      ∀ (lower : W → Bool), (∀ v x, top lower v x = false) →
        let observed := fun (input : W) => xor (blocks input) (lower input)
        let signed := Finset.univ.sum (fun sample : W => if observed sample then (-1 : ℤ) else 1)
        let linear := fun (n : ℕ) (q : W → Fin n → Bool) =>
          ∀ x y i, q (add x y) i = xor (q x i) (q y i)
        let drops := fun (n : ℕ) (q : W → Fin n → Bool) (base : W) =>
          ∀ (v : Fin r → W) (x : W), q x = q base →
            (∀ t i, q (v t) i = false) → top observed v x = false
        Int.ModEq ((2 : ℤ) ^ (p + 1)) signed ((2 : ℤ) ^ p) ∧
        (∀ c query, linear c query → ∀ base, drops c query base → p ≤ c) ∧
        (∃ query, linear p query ∧ ∀ base, drops p query base) := by
  intro p r hp hr W add diff top blocks lower hlower observed signed linear drops
  let ι := Fin p × Fin r
  let V := ι → ZMod 2
  let eW : W ≃ V :=
    { toFun := fun x ⟨b, c⟩ => PEqualNP.Outside.L_meta_25598_aux.b2z (x b c)
      invFun := fun v b c => decide (v (b, c) = 1)
      left_inv := fun x => by
        ext b c
        cases h : x b c <;> simp [h, PEqualNP.Outside.L_meta_25598_aux.b2z]
      right_inv := fun v => by
        ext ⟨b, c⟩
        rcases PEqualNP.Outside.L_meta_25598_aux.zmod2_cases (v (b, c)) with h | h <;>
          simp [h, PEqualNP.Outside.L_meta_25598_aux.b2z] }
  have heW_add : ∀ x y : W, eW (add x y) = eW x + eW y := by
    intro x y; ext ⟨b, c⟩
    exact PEqualNP.Outside.L_meta_25598_aux.b2z_xor (x b c) (y b c)
  have heW_foldl : ∀ (f : W → Bool) (l : List W) (x : W),
      PEqualNP.Outside.L_meta_25598_aux.b2z (l.foldl diff f x) =
        PEqualNP.Outside.L_meta_25598_aux.foldDiffZ
          (fun v => PEqualNP.Outside.L_meta_25598_aux.b2z (f (eW.symm v)))
          (l.map eW) (eW x) := by
    intro f l
    induction l generalizing f with
    | nil =>
      intro x; simp [PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_nil]
    | cons d t ih =>
      intro x
      simp only [List.foldl_cons, List.map_cons, PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_cons]
      rw [ih (diff f d) x]
      congr 1
      ext v
      simp only [diff, PEqualNP.Outside.L_meta_25598_aux.diffZ,
        PEqualNP.Outside.L_meta_25598_aux.b2z_xor]
      congr 3
      apply eW.injective
      rw [heW_add, eW.apply_symm_apply, eW.apply_symm_apply]
  let rowSet : Fin p → Finset ι := fun b => Finset.univ.image (fun c : Fin r => (b, c))
  have hrow_card : ∀ b : Fin p, (rowSet b).card = r := by
    intro b
    rw [Finset.card_image_of_injective _ (fun c1 c2 h => (Prod.mk.inj h).2)]
    simp
  have hrow_inj : Function.Injective rowSet := by
    intro b1 b2 h
    have hmem : (b1, (⟨0, by omega⟩ : Fin r)) ∈ rowSet b2 := by
      rw [← h]; exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
    rcases Finset.mem_image.mp hmem with ⟨c, _, hc⟩
    exact (Prod.mk.inj hc).1.symm
  let blocksZ : V → ZMod 2 := fun v => ∑ b : Fin p, PEqualNP.Outside.L_meta_25598_aux.monom (rowSet b) v
  have hblocksZ : ∀ x : W, PEqualNP.Outside.L_meta_25598_aux.b2z (blocks x) = blocksZ (eW x) := by
    intro x
    dsimp only [blocks, blocksZ]
    rw [PEqualNP.Outside.L_meta_25598_aux.b2z_foldl_xor_ofFn]
    apply Finset.sum_congr rfl; intro b _
    rw [PEqualNP.Outside.L_meta_25598_aux.b2z_all_id_ofFn]
    unfold PEqualNP.Outside.L_meta_25598_aux.monom
    rw [Finset.prod_image (fun c1 _ c2 _ h => (Prod.mk.inj h).2)]
    rfl
  let lowerZ : V → ZMod 2 := fun v => PEqualNP.Outside.L_meta_25598_aux.b2z (lower (eW.symm v))
  let obsZ : V → ZMod 2 := fun v => blocksZ v + lowerZ v
  have hobsZ : ∀ x : W, PEqualNP.Outside.L_meta_25598_aux.b2z (observed x) = obsZ (eW x) := by
    intro x
    dsimp only [observed, obsZ, lowerZ]
    rw [PEqualNP.Outside.L_meta_25598_aux.b2z_xor, hblocksZ, eW.symm_apply_apply]
  have hlower_diff : ∀ (v : Fin r → V) (x : V),
      PEqualNP.Outside.L_meta_25598_aux.foldDiffZ lowerZ (List.ofFn v) x = 0 := by
    intro v x
    have hl := hlower (fun t => eW.symm (v t)) (eW.symm x)
    have hbz : PEqualNP.Outside.L_meta_25598_aux.b2z (top lower (fun t => eW.symm (v t)) (eW.symm x)) = 0 := by
      rw [hl]; rfl
    rw [heW_foldl] at hbz
    have hmap : (List.ofFn (fun t => eW.symm (v t))).map eW = List.ofFn v := by
      rw [List.map_ofFn]
      congr 1; funext t; exact eW.apply_symm_apply (v t)
    rw [hmap, eW.apply_symm_apply] at hbz
    exact hbz
  have hlower_anf : ∀ S : Finset ι, r ≤ S.card →
      PEqualNP.Outside.L_meta_25598_aux.anf lowerZ S = 0 :=
    PEqualNP.Outside.L_meta_25598_aux.anf_eq_zero_of_foldDiffZ_zero r lowerZ hlower_diff
  have hblocks_anf : ∀ S : Finset ι,
      PEqualNP.Outside.L_meta_25598_aux.anf blocksZ S = if ∃ b : Fin p, S = rowSet b then 1 else 0 := by
    intro S
    have hrew : blocksZ = fun v => ∑ U : Finset ι,
        (if ∃ b : Fin p, U = rowSet b then (1 : ZMod 2) else 0) *
          PEqualNP.Outside.L_meta_25598_aux.monom U v := by
      ext v
      dsimp only [blocksZ]
      simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
      refine Finset.sum_bij (fun b _ => rowSet b) ?_ ?_ ?_ ?_
      · intro b _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b, rfl⟩⟩
      · intro b1 _ b2 _ h; exact hrow_inj h
      · intro U hU
        rcases (Finset.mem_filter.mp hU).2 with ⟨b, rfl⟩
        exact ⟨b, Finset.mem_univ _, rfl⟩
      · intro b _; rfl
    rw [hrew, PEqualNP.Outside.L_meta_25598_aux.anf_unique]
  have hobs_anf : ∀ S : Finset ι,
      PEqualNP.Outside.L_meta_25598_aux.anf obsZ S =
        (if ∃ b : Fin p, S = rowSet b then 1 else 0) +
          PEqualNP.Outside.L_meta_25598_aux.anf lowerZ S := by
    intro S
    rw [PEqualNP.Outside.L_meta_25598_aux.anf_add, hblocks_anf]
  have hsigned_eq : signed = ∑ v : V, PEqualNP.Outside.L_meta_25598_aux.zSign (obsZ v) := by
    dsimp only [signed]
    have hterm : ∀ x : W, (if observed x then (-1 : ℤ) else 1) =
        PEqualNP.Outside.L_meta_25598_aux.zSign (obsZ (eW x)) := by
      intro x
      rw [← hobsZ x]
      unfold PEqualNP.Outside.L_meta_25598_aux.zSign
      cases observed x <;> decide
    simp_rw [hterm]
    exact Fintype.sum_equiv eW _ _ (fun _ => rfl)
  have hgoal1 : Int.ModEq ((2 : ℤ) ^ (p + 1)) signed ((2 : ℤ) ^ p) := by
    rw [hsigned_eq, PEqualNP.Outside.L_meta_25598_aux.signed_sum_anf obsZ]
    set supp := Finset.univ.filter (fun S : Finset ι => PEqualNP.Outside.L_meta_25598_aux.anf obsZ S = 1)
    let A0 : Finset (Finset ι) := Finset.univ.image rowSet
    have hA0_mem : A0 ∈ supp.powerset := by
      rw [Finset.mem_powerset]
      intro S hS
      rcases Finset.mem_image.mp hS with ⟨b, _, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hobs_anf, hlower_anf (rowSet b) (by rw [hrow_card])]
      simp
    have hA0_card : A0.card = p := by
      rw [Finset.card_image_of_injective _ hrow_inj]; simp
    have hA0_union : A0.biUnion id = Finset.univ := by
      ext ⟨b, c⟩
      simp only [Finset.mem_biUnion, id_eq, Finset.mem_image, Finset.mem_univ, true_and, iff_true, A0]
      exact ⟨rowSet b, ⟨b, rfl⟩, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
    have hcard_ι : Fintype.card ι = p * r := by simp [ι]
    rw [← Finset.add_sum_erase _ _ hA0_mem]
    have hterm0 : (-2 : ℤ) ^ A0.card * (2 : ℤ) ^ (Fintype.card ι - (A0.biUnion id).card) = (-2 : ℤ) ^ p := by
      rw [hA0_card, hA0_union, Finset.card_univ, Nat.sub_self, pow_zero, mul_one]
    rw [hterm0]
    have hrest_dvd : (2 : ℤ) ^ (p + 1) ∣
        ∑ A ∈ supp.powerset.erase A0,
          (-2 : ℤ) ^ A.card * (2 : ℤ) ^ (Fintype.card ι - (A.biUnion id).card) := by
      apply Finset.dvd_sum
      intro A hA
      have hAne : A ≠ A0 := (Finset.mem_erase.mp hA).1
      have hAsupp : A ⊆ supp := Finset.mem_powerset.mp (Finset.mem_erase.mp hA).2
      apply PEqualNP.Outside.L_meta_25598_aux.pow_two_dvd_term
      have hSle : ∀ S ∈ A, S.card ≤ r := by
        intro S hSA
        have h1 : PEqualNP.Outside.L_meta_25598_aux.anf obsZ S = 1 :=
          (Finset.mem_filter.mp (hAsupp hSA)).2
        by_contra hgt
        push Not at hgt
        have hnotrow : ¬ ∃ b : Fin p, S = rowSet b := by
          rintro ⟨b, rfl⟩; rw [hrow_card] at hgt; omega
        rw [hobs_anf, hlower_anf S (by omega)] at h1
        simp [hnotrow] at h1
      have hu_le : (A.biUnion id).card ≤ Fintype.card ι := Finset.card_le_univ _
      have hu_le_sum : (A.biUnion id).card ≤ ∑ S ∈ A, S.card := Finset.card_biUnion_le
      have hsum_le : ∑ S ∈ A, S.card ≤ A.card * r := by
        calc ∑ S ∈ A, S.card ≤ ∑ _S ∈ A, r := Finset.sum_le_sum hSle
          _ = A.card * r := by simp
      rw [hcard_ι] at hu_le ⊢
      by_cases hgt : p + 1 ≤ A.card
      · omega
      · by_cases hlt : A.card < p
        · have hmul : (p - A.card) * 2 ≤ (p - A.card) * r := Nat.mul_le_mul_left _ hr
          have hsub : p * r - A.card * r = (p - A.card) * r := (Nat.sub_mul p A.card r).symm
          omega
        · have heq : A.card = p := by omega
          by_contra hnot
          have hu_eq : (A.biUnion id).card = p * r := by omega
          have hsum_eq : ∑ S ∈ A, S.card = ∑ _S ∈ A, r := by
            have h1 : ∑ _S ∈ A, r = p * r := by simp [heq]
            have h2 : A.card * r = p * r := by rw [heq]
            omega
          have hall_r : ∀ S ∈ A, S.card = r := by
            intro S hSA
            by_contra hne_r
            have hltS : S.card < r := lt_of_le_of_ne (hSle S hSA) hne_r
            have hltSum : ∑ T ∈ A, T.card < ∑ _T ∈ A, r :=
              Finset.sum_lt_sum hSle ⟨S, hSA, hltS⟩
            omega
          have hsubA0 : A ⊆ A0 := by
            intro S hSA
            have hSr := hall_r S hSA
            have h1 : PEqualNP.Outside.L_meta_25598_aux.anf obsZ S = 1 :=
              (Finset.mem_filter.mp (hAsupp hSA)).2
            rw [hobs_anf, hlower_anf S (by omega)] at h1
            simp only [add_zero] at h1
            by_cases hrow : ∃ b : Fin p, S = rowSet b
            · rcases hrow with ⟨b, rfl⟩
              exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
            · simp [hrow] at h1
          have hEqA : A = A0 := Finset.eq_of_subset_of_card_le hsubA0 (by rw [heq, hA0_card])
          exact hAne hEqA
    rw [Int.modEq_iff_dvd]
    have hdiff_pow : (2 : ℤ) ^ (p + 1) ∣ (2 : ℤ) ^ p - (-2 : ℤ) ^ p := by
      have hfac : (2 : ℤ) ^ p - (-2 : ℤ) ^ p = (1 - (-1 : ℤ) ^ p) * (2 : ℤ) ^ p := by
        have : (-2 : ℤ) = (-1 : ℤ) * 2 := by ring
        rw [this, mul_pow]; ring
      rw [hfac, pow_succ]
      rcases Nat.even_or_odd p with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have h1 : (-1 : ℤ) ^ (k + k) = 1 := by
          rw [show k + k = 2 * k by omega, pow_mul]; norm_num
        rw [h1]; simp
      · have h1 : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
          rw [pow_succ, pow_mul]; norm_num
        rw [h1]
        refine ⟨1, ?_⟩; ring
    have hcomb : (2 : ℤ) ^ p - ((-2 : ℤ) ^ p +
        ∑ A ∈ supp.powerset.erase A0,
          (-2 : ℤ) ^ A.card * (2 : ℤ) ^ (Fintype.card ι - (A.biUnion id).card)) =
        ((2 : ℤ) ^ p - (-2 : ℤ) ^ p) -
        ∑ A ∈ supp.powerset.erase A0,
          (-2 : ℤ) ^ A.card * (2 : ℤ) ^ (Fintype.card ι - (A.biUnion id).card) := by ring
    rw [hcomb]
    exact dvd_sub hdiff_pow hrest_dvd
  refine ⟨hgoal1, ?_, ?_⟩
  · intro c query hlin base hdrops
    by_contra hlt
    push Not at hlt
    let Q : V →ₗ[ZMod 2] (Fin c → ZMod 2) :=
      { toFun := fun v i => PEqualNP.Outside.L_meta_25598_aux.b2z (query (eW.symm v) i)
        map_add' := fun v1 v2 => by
          ext i
          have hsum : eW.symm (v1 + v2) = add (eW.symm v1) (eW.symm v2) := by
            apply eW.injective
            rw [heW_add, eW.apply_symm_apply, eW.apply_symm_apply, eW.apply_symm_apply]
          rw [hsum, hlin, PEqualNP.Outside.L_meta_25598_aux.b2z_xor]
          rfl
        map_smul' := fun a v => by
          ext i
          rcases PEqualNP.Outside.L_meta_25598_aux.zmod2_cases a with rfl | rfl
          · simp only [zero_smul, RingHom.id_apply, Pi.zero_apply]
            have hz : eW.symm (0 : V) = add (eW.symm (0 : V)) (eW.symm (0 : V)) := by
              apply eW.injective
              rw [heW_add, eW.apply_symm_apply, add_zero]
            have hq0 := congrArg (fun w => PEqualNP.Outside.L_meta_25598_aux.b2z (query w i)) hz
            rw [hlin, PEqualNP.Outside.L_meta_25598_aux.b2z_xor] at hq0
            rcases PEqualNP.Outside.L_meta_25598_aux.zmod2_cases
              (PEqualNP.Outside.L_meta_25598_aux.b2z (query (eW.symm 0) i)) with h | h
            · exact h
            · rw [h] at hq0; exact absurd hq0 (by decide)
          · simp }
    let K : Submodule (ZMod 2) V := LinearMap.ker Q
    let n : ℕ := Module.finrank (ZMod 2) K
    have hdim_n : p * (r - 1) < n := by
      have hrn := LinearMap.finrank_range_add_finrank_ker Q
      have hV : Module.finrank (ZMod 2) V = p * r := by
        simp [V, ι]
      have hrange : Module.finrank (ZMod 2) (LinearMap.range Q) ≤ c := by
        calc Module.finrank (ZMod 2) (LinearMap.range Q)
            ≤ Module.finrank (ZMod 2) (Fin c → ZMod 2) := Submodule.finrank_le _
          _ = c := by simp
      have hmul : p * (r - 1) + p = p * r := by
        have : r = (r - 1) + 1 := by omega
        conv_rhs => rw [this, mul_add, mul_one]
      dsimp only [n, K]
      omega
    have hobs_diff_ker : ∀ (v : Fin r → V) (x : V), (∀ t, v t ∈ K) →
        PEqualNP.Outside.L_meta_25598_aux.foldDiffZ obsZ (List.ofFn v) x = 0 := by
      intro v x hvK
      have hobs_split : ∀ y : V, PEqualNP.Outside.L_meta_25598_aux.foldDiffZ obsZ (List.ofFn v) y =
          PEqualNP.Outside.L_meta_25598_aux.foldDiffZ blocksZ (List.ofFn v) y := by
        intro y
        dsimp only [obsZ]
        rw [PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_add, hlower_diff, add_zero]
      have hblocks_const : PEqualNP.Outside.L_meta_25598_aux.foldDiffZ blocksZ (List.ofFn v) x =
          PEqualNP.Outside.L_meta_25598_aux.foldDiffZ blocksZ (List.ofFn v) (eW base) := by
        dsimp only [blocksZ]
        rw [PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_sum,
          PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_sum]
        apply Finset.sum_congr rfl; intro b _
        apply PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_monom_const
        rw [hrow_card, List.length_ofFn]
      rw [hobs_split x, hblocks_const, ← hobs_split (eW base)]
      have hvq : ∀ t i, query (eW.symm (v t)) i = false := by
        intro t i
        have hQt : Q (v t) = 0 := LinearMap.mem_ker.mp (hvK t)
        have hti := congrFun hQt i
        exact PEqualNP.Outside.L_meta_25598_aux.b2z_inj hti
      have hd := hdrops (fun t => eW.symm (v t)) base rfl hvq
      have hbz : PEqualNP.Outside.L_meta_25598_aux.b2z
          (top observed (fun t => eW.symm (v t)) base) = 0 := by
        rw [hd]; rfl
      rw [heW_foldl] at hbz
      have hmap : (List.ofFn (fun t => eW.symm (v t))).map eW = List.ofFn v := by
        rw [List.map_ofFn]; congr 1; funext t; exact eW.apply_symm_apply (v t)
      have hobs_fn : (fun u => PEqualNP.Outside.L_meta_25598_aux.b2z (observed (eW.symm u))) = obsZ := by
        ext u; rw [hobsZ, eW.apply_symm_apply]
      rw [hmap, hobs_fn] at hbz
      exact hbz
    have hpart : (∑ v : V, PEqualNP.Outside.L_meta_25598_aux.zSign (obsZ v)) =
        ∑ y : Fin c → ZMod 2, ∑ v ∈ Finset.univ.filter (fun v : V => Q v = y),
          PEqualNP.Outside.L_meta_25598_aux.zSign (obsZ v) := by
      rw [Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _)]
    have hdvd_signed : (2 : ℤ) ^ (p + 1) ∣ signed := by
      rw [hsigned_eq, hpart]
      apply Finset.dvd_sum
      intro y _
      by_cases hne : (Finset.univ.filter (fun v : V => Q v = y)).Nonempty
      · rcases hne with ⟨x0, hx0⟩
        have hQx0 : Q x0 = y := (Finset.mem_filter.mp hx0).2
        let B : Module.Basis (Fin n) (ZMod 2) K := Module.finBasis (ZMod 2) K
        let φ : (Fin n → ZMod 2) → V := fun z => ∑ i : Fin n, z i • (B i : V)
        have hφ_add : ∀ z1 z2, φ (z1 + z2) = φ z1 + φ z2 := by
          intro z1 z2; dsimp only [φ]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _
          simp only [Pi.add_apply, add_smul]
        have hφ_mem : ∀ z, φ z ∈ K := fun z =>
          Submodule.sum_mem K (fun i _ => Submodule.smul_mem K (z i) (B i).2)
        have hφ_inj : Function.Injective φ := by
          intro z1 z2 hEq
          have hK : (∑ i : Fin n, z1 i • B i) = ∑ i : Fin n, z2 i • B i := by
            apply Subtype.ext
            simpa [φ] using hEq
          have hlin_eq := B.equivFun.symm.injective (by
            simpa [Module.Basis.equivFun_symm_apply] using hK)
          exact hlin_eq
        have hφ_surj : ∀ v ∈ K, ∃ z, φ z = v := by
          intro v hvK
          refine ⟨B.equivFun ⟨v, hvK⟩, ?_⟩
          have hsum : (∑ i : Fin n, (B.equivFun ⟨v, hvK⟩) i • B i) = ⟨v, hvK⟩ := by
            simp [Module.Basis.equivFun_apply]
          have hcoe : (↑(∑ i : Fin n, (B.equivFun ⟨v, hvK⟩) i • B i) : V) = φ (B.equivFun ⟨v, hvK⟩) := by
            simp only [φ, Submodule.coe_sum, SetLike.val_smul]
          rw [← hcoe, hsum]
        have hfib : (∑ v ∈ Finset.univ.filter (fun v : V => Q v = y),
            PEqualNP.Outside.L_meta_25598_aux.zSign (obsZ v)) =
            ∑ z : Fin n → ZMod 2, PEqualNP.Outside.L_meta_25598_aux.zSign (obsZ (x0 + φ z)) := by
          symm
          refine Finset.sum_bij (fun z _ => x0 + φ z) ?_ ?_ ?_ ?_
          · intro z _
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rw [map_add, hQx0, LinearMap.mem_ker.mp (hφ_mem z), add_zero]
          · intro z1 _ z2 _ hEq
            exact hφ_inj (add_left_cancel hEq)
          · intro v hv
            have hQv : Q v = y := (Finset.mem_filter.mp hv).2
            have hvx0 : v - x0 ∈ K := by
              rw [LinearMap.mem_ker, map_sub, hQv, hQx0, sub_self]
            rcases hφ_surj (v - x0) hvx0 with ⟨z, hz⟩
            exact ⟨z, Finset.mem_univ _, by rw [hz]; abel⟩
          · intro z _; rfl
        rw [hfib]
        apply PEqualNP.Outside.L_meta_25598_aux.signed_sum_dvd_of_deg_lt p r hr
          (fun z => obsZ (x0 + φ z)) _ (by simpa using hdim_n)
        apply PEqualNP.Outside.L_meta_25598_aux.anf_eq_zero_of_foldDiffZ_zero
        intro u z
        rw [PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_comp_affine x0 φ hφ_add obsZ (List.ofFn u) z,
          List.map_ofFn]
        exact hobs_diff_ker (fun t => φ (u t)) (x0 + φ z) (fun t => hφ_mem (u t))
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
        exact dvd_zero _
    rw [Int.modEq_iff_dvd] at hgoal1
    have hdvd_pow : (2 : ℤ) ^ (p + 1) ∣ (2 : ℤ) ^ p := by
      have : (2 : ℤ) ^ p = ((2 : ℤ) ^ p - signed) + signed := by ring
      rw [this]
      exact dvd_add hgoal1 hdvd_signed
    have hle : (2 : ℤ) ^ (p + 1) ≤ (2 : ℤ) ^ p := Int.le_of_dvd (by positivity) hdvd_pow
    have hlt_pow : (2 : ℤ) ^ p < (2 : ℤ) ^ (p + 1) := by
      rw [pow_succ]; linarith [show (0 : ℤ) < (2 : ℤ) ^ p by positivity]
    omega
  · refine ⟨fun x b => x b ⟨0, by omega⟩, ?_, ?_⟩
    · intro x y b; rfl
    · intro base v x _ hv
      apply PEqualNP.Outside.L_meta_25598_aux.b2z_inj
      rw [heW_foldl]
      have hobs_fn : (fun u => PEqualNP.Outside.L_meta_25598_aux.b2z (observed (eW.symm u))) = obsZ := by
        ext u; rw [hobsZ, eW.apply_symm_apply]
      rw [hobs_fn, List.map_ofFn]
      dsimp only [obsZ]
      rw [PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_add, hlower_diff, add_zero]
      dsimp only [blocksZ]
      rw [PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_sum]
      apply Finset.sum_eq_zero; intro b _
      rw [PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_ofFn_eq_sum]
      let j0 : ι := (b, ⟨0, by omega⟩)
      have hj0 : j0 ∈ rowSet b := Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
      have hterm_fac : ∀ S : Finset (Fin r),
          PEqualNP.Outside.L_meta_25598_aux.monom (rowSet b) (eW x + ∑ t ∈ S, eW (v t)) =
            eW x j0 * PEqualNP.Outside.L_meta_25598_aux.monom ((rowSet b).erase j0)
              (eW x + ∑ t ∈ S, eW (v t)) := by
        intro S
        unfold PEqualNP.Outside.L_meta_25598_aux.monom
        rw [← Finset.mul_prod_erase _ _ hj0]
        congr 1
        change eW x j0 + (∑ t ∈ S, eW (v t)) j0 = eW x j0
        rw [Finset.sum_apply]
        have hzero : (∑ t ∈ S, eW (v t) j0) = 0 := by
          apply Finset.sum_eq_zero; intro t _
          have hvt := hv t b
          simp only [eW, Equiv.coe_fn_mk, j0, hvt]
          rfl
        rw [hzero, add_zero]
      simp only [Function.comp_apply]
      rw [Finset.sum_congr rfl (fun S _ => hterm_fac S)]
      rw [← Finset.mul_sum, ← PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_ofFn_eq_sum]
      have hcard_lt : ((rowSet b).erase j0).card < (List.ofFn (fun t => eW (v t))).length := by
        rw [Finset.card_erase_of_mem hj0, hrow_card, List.length_ofFn]
        omega
      rw [PEqualNP.Outside.L_meta_25598_aux.foldDiffZ_monom_eq_zero _ _ hcard_lt, mul_zero]
