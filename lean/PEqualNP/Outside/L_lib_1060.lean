import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1060

open Classical

abbrev F := ZMod 2

theorem F_cases (z : F) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem sum_F {M : Type*} [AddCommMonoid M] (g : F → M) : ∑ z : F, g z = g 0 + g 1 := by
  rw [show (Finset.univ : Finset F) = {0, 1} from by decide]
  rw [Finset.sum_pair (by decide)]

noncomputable def wt {ι : Type*} [Fintype ι] (p : ι → F) : ℕ :=
  (Finset.univ.filter (fun i => p i ≠ 0)).card

theorem pow_wt {ι : Type*} [Fintype ι] (x : ℚ) (p : ι → F) :
    x ^ wt p = ∏ i, (if p i = 0 then 1 else x) := by
  unfold wt
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

theorem sum_pow_wt {ι : Type*} [Fintype ι] (x : ℚ) :
    ∑ u : ι → F, x ^ wt u = (1 + x) ^ Fintype.card ι := by
  simp only [pow_wt]
  rw [← Fintype.prod_sum (fun _ z => if z = 0 then (1 : ℚ) else x)]
  have h : ∀ i : ι, (∑ z : F, if z = 0 then (1 : ℚ) else x) = 1 + x := by
    intro _; rw [sum_F]; norm_num
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ]

theorem wt_zero {ι : Type*} [Fintype ι] : wt (0 : ι → F) = 0 := by
  simp [wt]

theorem infoSet {ι : Type*} [Fintype ι] (d : ℕ) :
    ∀ P : Submodule F (ι → F), Module.finrank F P = d →
      ∃ I : Finset ι, I.card ≤ d ∧ ∀ p ∈ P, (∀ i ∈ I, p i = 0) → p = 0 := by
  induction d with
  | zero =>
    intro P hP
    rw [Submodule.finrank_eq_zero] at hP
    refine ⟨∅, by simp, fun p hp _ => ?_⟩
    rw [hP] at hp
    exact (Submodule.mem_bot F).mp hp
  | succ d ih =>
    intro P hP
    have hne : P ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hP
      omega
    obtain ⟨p0, hp0, hp0ne⟩ := (Submodule.ne_bot_iff P).mp hne
    obtain ⟨i0, hi0⟩ : ∃ i0, p0 i0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hp0ne (funext h)
    let f : P →ₗ[F] F := (LinearMap.proj i0).comp P.subtype
    have hrange : Module.finrank F (LinearMap.range f) = 1 := by
      apply le_antisymm
      · calc Module.finrank F (LinearMap.range f) ≤ Module.finrank F F :=
              Submodule.finrank_le _
          _ = 1 := Module.finrank_self F
      · rw [Nat.one_le_iff_ne_zero]
        intro h0
        rw [Submodule.finrank_eq_zero] at h0
        have : f ⟨p0, hp0⟩ ∈ LinearMap.range f := LinearMap.mem_range_self f _
        rw [h0, Submodule.mem_bot] at this
        exact hi0 this
    have hker : Module.finrank F (LinearMap.ker f) = d := by
      have := LinearMap.finrank_range_add_finrank_ker f
      omega
    set P0 := (LinearMap.ker f).map P.subtype with hP0
    have hP0d : Module.finrank F P0 = d := by
      rw [hP0, Submodule.finrank_map_subtype_eq, hker]
    obtain ⟨I0, hI0, hinj⟩ := ih P0 hP0d
    refine ⟨insert i0 I0, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
    intro p hp hvan
    have hpi0 : p i0 = 0 := hvan i0 (Finset.mem_insert_self _ _)
    have hpP0 : p ∈ P0 := by
      rw [hP0, Submodule.mem_map]
      refine ⟨⟨p, hp⟩, ?_, rfl⟩
      rw [LinearMap.mem_ker]
      exact hpi0
    exact hinj p hpP0 (fun i hi => hvan i (Finset.mem_insert_of_mem hi))

noncomputable def B (d : ℕ) : ℚ := (5/8) * (5/4)^d + (3/8) * (3/4)^d

theorem B_succ_gt (k : ℕ) : B k < B (k+1) := by
  unfold B
  have h1 : (3/4 : ℚ)^k ≤ (5/4)^k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h2 : (0 : ℚ) < (3/4)^k := by positivity
  rw [pow_succ, pow_succ]
  nlinarith

theorem B_strict : StrictMono B := strictMono_nat_of_lt_succ B_succ_gt

theorem B_step (d : ℕ) : (1/4) * (5/4 : ℚ)^(d+1) + (3/4) * B d = B (d+1) := by
  unfold B; ring

theorem B_zero : B 0 = 1 := by unfold B; norm_num

theorem wt_split {ι : Type} [Fintype ι] (I : Finset ι) (v : ι → F) :
    wt v = wt (fun i : I => v i) + (Finset.univ.filter (fun i => i ∉ I ∧ v i ≠ 0)).card := by
  unfold wt
  have h1 : (Finset.univ.filter (fun i : I => v i ≠ 0)).card =
      (Finset.univ.filter (fun i => i ∈ I ∧ v i ≠ 0)).card := by
    apply Finset.card_bij (fun i _ => i.1)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨i.2, hi⟩
    · intro i _ j _ h; exact Subtype.ext h
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨⟨i, hi.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi.2, rfl⟩
  rw [h1, ← Finset.card_union_of_disjoint]
  · congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2.1 h1.1

theorem F_eq_of_add (a b : F) (h : a + b = 0) : a = b := by
  have := eq_neg_of_add_eq_zero_left h
  rwa [CharTwo.neg_eq] at this

theorem card_SP {ι : Type} [Fintype ι] (P : Submodule F (ι → F)) :
    (Finset.univ.filter (fun v => v ∈ P)).card = 2 ^ Module.finrank F P := by
  have h := Module.card_eq_pow_finrank (K := F) (V := P)
  rw [ZMod.card] at h
  rw [← h]
  exact (Fintype.card_subtype (fun v => v ∈ P)).symm.trans (Fintype.card_congr (Equiv.refl _))

theorem wt_single {ι : Type} [Fintype ι] (k : ι) :
    wt (fun i => if i = k then (1 : F) else 0) = 1 := by
  unfold wt
  rw [Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  by_cases h : i = k
  · subst h; simp
  · simp [h]

theorem wt_le_card {ι : Type} [Fintype ι] (v : ι → F) : wt v ≤ Fintype.card ι := by
  unfold wt; exact Finset.card_le_univ _

theorem mainQ (d : ℕ) : ∀ (ι : Type) [Fintype ι] (P : Submodule F (ι → F)) (c : (ι → F) → ℚ),
    Module.finrank F P = d → d < Fintype.card ι → (∀ p ∈ P, wt p ≠ 1) → (∀ p, c p ≤ 4) →
    (∀ p, wt p ≤ d + 2 → c p = 1) →
    (∑ v ∈ Finset.univ.filter (fun v => v ∈ P), (1/4 : ℚ) ^ (wt v) * c v) ≤ B d ∧
    ((∑ v ∈ Finset.univ.filter (fun v => v ∈ P), (1/4 : ℚ) ^ (wt v) * c v) = B d →
      ∃ T : Finset ι, T.card = d + 1 ∧ ∀ v, v ∈ P ↔ (∀ i ∉ T, v i = 0) ∧ ∑ i, v i = 0) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro ι _ P c hP hdι hno1 hc4 hcl
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have hbot : P = ⊥ := Submodule.finrank_eq_zero.mp hP
    have hSP : Finset.univ.filter (fun v => v ∈ P) = {0} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hbot,
        Submodule.mem_bot]
    rw [hSP, Finset.sum_singleton, wt_zero, pow_zero, one_mul,
      hcl 0 (by rw [wt_zero]; omega), B_zero]
    refine ⟨le_refl _, fun _ => ?_⟩
    obtain ⟨i0⟩ : Nonempty ι := Fintype.card_pos_iff.mp hdι
    refine ⟨{i0}, by simp, fun v => ?_⟩
    rw [hbot, Submodule.mem_bot]
    constructor
    · rintro rfl; simp
    · rintro ⟨h1, h2⟩
      have hv0 : v i0 = 0 := by
        rw [Finset.sum_eq_single i0 (fun i _ hi => h1 i (by simpa using hi)) (by simp)] at h2
        exact h2
      funext i
      by_cases hi : i = i0
      · rw [hi, hv0]; rfl
      · exact h1 i (by simpa using hi)
  · obtain ⟨I, hIle, hinj⟩ := infoSet d P hP
    set SP := Finset.univ.filter (fun v => v ∈ P) with hSPdef
    let ρ : (ι → F) → (I → F) := fun v i => v i
    have hmemSP : ∀ v, v ∈ SP ↔ v ∈ P := by
      intro v; simp only [SP, Finset.mem_filter, Finset.mem_univ, true_and]
    have hρinj : Set.InjOn ρ SP := by
      intro v hv w hw hvw
      have hv' := (hmemSP v).mp hv
      have hw' := (hmemSP w).mp hw
      have h0 := hinj (v - w) (P.sub_mem hv' hw') (fun i hi => by
        have := congrFun hvw ⟨i, hi⟩
        simp only [ρ] at this
        simp [this])
      exact sub_eq_zero.mp h0
    have hcardSP : SP.card = 2 ^ d := by rw [← hP]; exact card_SP P
    have huniv : (Finset.univ : Finset (I → F)).card = 2 ^ I.card := by
      rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe]
    have himgc : (SP.image ρ).card = 2 ^ d := by
      rw [Finset.card_image_of_injOn hρinj, hcardSP]
    have hI : I.card = d := by
      have hle : (SP.image ρ).card ≤ (Finset.univ : Finset (I → F)).card := Finset.card_le_univ _
      rw [himgc, huniv] at hle
      exact le_antisymm hIle ((Nat.pow_le_pow_iff_right (by norm_num)).mp hle)
    have himg : SP.image ρ = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [huniv, himgc, hI]
    have hsurj : ∀ u : I → F, ∃ v ∈ SP, ρ v = u := by
      intro u
      have : u ∈ SP.image ρ := by rw [himg]; exact Finset.mem_univ u
      simpa using this
    have hcardI : Fintype.card I = d := by rw [Fintype.card_coe, hI]

    set L := SP.filter (fun v => ∀ i ∉ I, v i = 0) with hLdef
    let Z : Submodule F (ι → F) := { carrier := {v | ∀ i ∉ I, v i = 0}, add_mem' := by intro a b ha hb i hi; simp only [Set.mem_setOf_eq] at ha hb; simp [ha i hi, hb i hi], zero_mem' := by intro i _; rfl, smul_mem' := by intro s a ha i hi; simp only [Set.mem_setOf_eq] at ha; simp [ha i hi] }
    let ρL : (ι → F) →ₗ[F] (I → F) := LinearMap.funLeft F F (Subtype.val : I → ι)
    set K := (P ⊓ Z).map ρL with hKdef
    have hK : ∀ u, u ∈ K ↔ ∃ v ∈ L, ρ v = u := by
      intro u
      rw [hKdef, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Submodule.mem_inf] at hy
        refine ⟨y, ?_, rfl⟩
        simp only [L, Finset.mem_filter, hmemSP]
        exact ⟨hy.1, hy.2⟩
      · rintro ⟨v, hv, rfl⟩
        simp only [L, Finset.mem_filter, hmemSP] at hv
        exact ⟨v, Submodule.mem_inf.mpr ⟨hv.1, hv.2⟩, rfl⟩
    have hLsub : ∀ v ∈ L, v ∈ SP ∧ ∀ i ∉ I, v i = 0 := by
      intro v hv; simpa [L] using hv

    set r := fun v : ι → F => (Finset.univ.filter (fun i => i ∉ I ∧ v i ≠ 0)).card with hrdef
    have hwt : ∀ v, wt v = wt (ρ v) + r v := fun v => wt_split I v
    have hwtρ : ∀ v, wt (ρ v) ≤ d := fun v => (wt_le_card _).trans hcardI.le
    have hr0 : ∀ v, (∀ i ∉ I, v i = 0) ↔ r v = 0 := by
      intro v
      simp only [r, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies,
        not_and, not_not]
    set X := fun v : ι → F => (1/4 : ℚ) ^ (wt (ρ v)) with hXdef
    have hXpos : ∀ v, 0 < X v := fun v => by positivity
    have hterm : ∀ v, (1/4 : ℚ) ^ (wt v) * c v ≤
        (if (∀ i ∉ I, v i = 0) then X v else (1/4) * X v) := by
      intro v
      split_ifs with hL
      · have hrv := (hr0 v).mp hL
        have hw : wt v = wt (ρ v) := by rw [hwt, hrv, add_zero]
        rw [hcl v (by rw [hw]; have := hwtρ v; omega), mul_one, hw]
      · have hrv : r v ≠ 0 := fun h => hL ((hr0 v).mpr h)
        by_cases hlight : wt v ≤ d + 2
        · rw [hcl v hlight, mul_one, hwt]
          calc (1/4 : ℚ) ^ (wt (ρ v) + r v) ≤ (1/4) ^ (wt (ρ v) + 1) :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = (1/4) * X v := by rw [pow_succ]; simp only [X]; ring
        · have hr3 : 3 ≤ r v := by have := hwt v; have := hwtρ v; omega
          calc (1/4 : ℚ) ^ (wt v) * c v ≤ (1/4) ^ (wt v) * 4 :=
                mul_le_mul_of_nonneg_left (hc4 v) (by positivity)
            _ ≤ (1/4) ^ (wt (ρ v) + 3) * 4 := by
                rw [hwt]
                apply mul_le_mul_of_nonneg_right _ (by norm_num)
                exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ ≤ (1/4) * X v := by
                simp only [X]; rw [pow_add]
                have := hXpos v
                simp only [X] at this
                nlinarith
    have hstrict : ∀ v, ¬ (∀ i ∉ I, v i = 0) → r v ≠ 1 →
        (1/4 : ℚ) ^ (wt v) * c v < (1/4) * X v := by
      intro v hL hr1
      have hrv : r v ≠ 0 := fun h => hL ((hr0 v).mpr h)
      by_cases hlight : wt v ≤ d + 2
      · rw [hcl v hlight, mul_one, hwt]
        calc (1/4 : ℚ) ^ (wt (ρ v) + r v) < (1/4) ^ (wt (ρ v) + 1) :=
              pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
          _ = (1/4) * X v := by rw [pow_succ]; simp only [X]; ring
      · have hr3 : 3 ≤ r v := by have := hwt v; have := hwtρ v; omega
        calc (1/4 : ℚ) ^ (wt v) * c v ≤ (1/4) ^ (wt v) * 4 :=
              mul_le_mul_of_nonneg_left (hc4 v) (by positivity)
          _ ≤ (1/4) ^ (wt (ρ v) + 3) * 4 := by
              rw [hwt]
              apply mul_le_mul_of_nonneg_right _ (by norm_num)
              exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ < (1/4) * X v := by
              simp only [X]; rw [pow_add]
              have := hXpos v
              simp only [X] at this
              nlinarith

    have hsumX : ∑ v ∈ SP, X v = (5/4 : ℚ) ^ d := by
      have h1 : ∑ v ∈ SP, X v = ∑ u ∈ SP.image ρ, (1/4 : ℚ) ^ (wt u) :=
        (Finset.sum_image (f := fun u : I → F => (1/4 : ℚ) ^ (wt u))
          (fun a ha b hb h => hρinj ha hb h)).symm
      rw [h1, himg]
      have h2 := sum_pow_wt (ι := I) (1/4 : ℚ)
      rw [hcardI] at h2
      rw [show (5/4 : ℚ) = 1 + 1/4 by norm_num, ← h2]
      exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
    have hsumL : ∑ v ∈ L, X v =
        ∑ u ∈ Finset.univ.filter (fun u => u ∈ K), (1/4 : ℚ) ^ (wt u) * 1 := by
      apply Finset.sum_nbij ρ
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hK _).mpr ⟨v, hv, rfl⟩
      · exact hρinj.mono (fun v hv => (hLsub v hv).1)
      · intro u hu
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu
        obtain ⟨v, hv, hvu⟩ := (hK u).mp hu
        exact ⟨v, hv, hvu⟩
      · intro v _; simp [X]

    have hKno1 : ∀ u ∈ K, wt u ≠ 1 := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := (hK u).mp hu
      have hvL := hLsub v hv
      have : wt v = wt (ρ v) := by rw [hwt, (hr0 v).mp hvL.2, add_zero]
      rw [← this]
      exact hno1 v ((hmemSP v).mp hvL.1)
    obtain ⟨k0, hk0⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
    set κ := Module.finrank F K with hκdef
    have hκ : κ < d := by
      have hle : κ ≤ d := by
        rw [hκdef, ← hcardI, ← Module.finrank_fintype_fun_eq_card (R := F)]
        exact Submodule.finrank_le K
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        have htop : K = ⊤ := by
          apply Submodule.eq_top_of_finrank_eq
          rw [← hκdef, h, Module.finrank_fintype_fun_eq_card, hcardI]
        have hmem := Submodule.eq_top_iff'.mp htop (fun i : I => if i = ⟨k0, hk0⟩ then (1 : F) else 0)
        exact hKno1 _ hmem (by convert wt_single (⟨k0, hk0⟩ : I))
    have hκI : κ < Fintype.card I := by rw [hcardI]; exact hκ
    obtain ⟨hKle, hKeq⟩ := ih κ hκ I K (fun _ => 1) hκdef.symm hκI hKno1
      (fun _ => by norm_num) (fun _ _ => rfl)
    have hKle' : ∑ u ∈ Finset.univ.filter (fun u => u ∈ K), (1/4 : ℚ) ^ (wt u) * 1 ≤ B κ := by
      convert hKle using 2
      ext u; simp
    have hKeq' : ∑ u ∈ Finset.univ.filter (fun u => u ∈ K), (1/4 : ℚ) ^ (wt u) * 1 = B κ →
        ∃ T : Finset I, T.card = κ + 1 ∧ ∀ v, v ∈ K ↔ (∀ i ∉ T, v i = 0) ∧ ∑ i, v i = 0 := by
      intro h
      apply hKeq
      convert h using 2
      ext u; simp
    have hBκ : B κ ≤ B (d - 1) := B_strict.monotone (by omega)
    have hBd : (1/4) * (5/4 : ℚ) ^ d + (3/4) * B (d - 1) = B d := by
      have := B_step (d - 1)
      rwa [Nat.sub_add_cancel hdpos] at this
    have hite : ∑ v ∈ SP, (if (∀ i ∉ I, v i = 0) then X v else (1/4) * X v) =
        (1/4) * ∑ v ∈ SP, X v + (3/4) * ∑ v ∈ L, X v := by
      rw [Finset.sum_ite, ← Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not SP
        (fun v => ∀ i ∉ I, v i = 0)]
      ring
    have hle1 := Finset.sum_le_sum (fun v (_ : v ∈ SP) => hterm v)
    refine ⟨?_, ?_⟩
    · rw [hite, hsumX, hsumL] at hle1
      linarith
    · intro heq
      have hle1' := hle1
      rw [hite, hsumX, hsumL] at hle1'
      have hSK : ∑ u ∈ Finset.univ.filter (fun u => u ∈ K), (1/4 : ℚ) ^ (wt u) * 1
          = B (d - 1) := by linarith
      have hκeq : κ = d - 1 := by
        by_contra hne
        have : B κ < B (d - 1) := B_strict (by omega)
        linarith
      obtain ⟨T', hT'card, hT'⟩ := hKeq' (by rw [hSK, hκeq])
      have hT'univ : T' = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [hT'card, hcardI, hκeq]; omega
      have hKpar : ∀ u : I → F, u ∈ K ↔ ∑ i, u i = 0 := by
        intro u; rw [hT', hT'univ]; simp
      have htermeq := (Finset.sum_eq_sum_iff_of_le (fun v (_ : v ∈ SP) => hterm v)).mp
        (le_antisymm hle1 (by rw [hite, hsumX, hsumL, heq]; linarith))
      have hr1 : ∀ v ∈ SP, ¬ (∀ i ∉ I, v i = 0) → r v = 1 := by
        intro v hv hnot
        by_contra hne
        have h1 := hstrict v hnot hne
        rw [htermeq v hv, if_neg hnot] at h1
        exact lt_irrefl _ h1
      let u0 : I → F := fun i => if i = ⟨k0, hk0⟩ then (1 : F) else 0
      have hu0 : ∑ i, u0 i = 1 := by simp only [u0]; rw [Finset.sum_ite_eq']; simp
      obtain ⟨v0, hv0SP, hv0ρ⟩ := hsurj u0
      have hv0notL : ¬ (∀ i ∉ I, v0 i = 0) := by
        intro h
        have : u0 ∈ K := (hK u0).mpr ⟨v0, by rw [hLdef]; exact Finset.mem_filter.mpr ⟨hv0SP, h⟩, hv0ρ⟩
        rw [hKpar, hu0] at this
        exact one_ne_zero this
      obtain ⟨ℓ0, hℓ0⟩ := Finset.card_eq_one.mp (hr1 v0 hv0SP hv0notL)
      have hℓ0mem : ℓ0 ∉ I ∧ v0 ℓ0 ≠ 0 := by
        have := Finset.mem_singleton_self ℓ0
        rw [← hℓ0] at this
        simpa using this
      have hv0off : ∀ ℓ ∉ I, ℓ ≠ ℓ0 → v0 ℓ = 0 := by
        intro ℓ hℓ hne
        by_contra h
        have : ℓ ∈ Finset.univ.filter (fun i => i ∉ I ∧ v0 i ≠ 0) := by simp [hℓ, h]
        rw [hℓ0] at this
        exact hne (Finset.mem_singleton.mp this)
      have hv0ℓ0 : v0 ℓ0 = 1 := (F_cases _).resolve_left hℓ0mem.2
      have hv0P := (hmemSP v0).mp hv0SP
      have hsumv0 : ∑ i : I, v0 i = 1 := by
        rw [← hu0, ← hv0ρ]
      have hclaim : ∀ v ∈ P, (∀ ℓ ∉ I, ℓ ≠ ℓ0 → v ℓ = 0) ∧ v ℓ0 = ∑ i : I, v i := by
        intro v hv
        rcases F_cases (∑ i : I, v i) with hs | hs
        · have hK' : ρ v ∈ K := (hKpar _).mpr hs
          obtain ⟨w, hwL, hwρ⟩ := (hK _).mp hK'
          have hw := hLsub w hwL
          have hwv : w = v := hρinj hw.1 ((hmemSP v).mpr hv) hwρ
          rw [hwv] at hw
          exact ⟨fun ℓ hℓ _ => hw.2 ℓ hℓ, by rw [hw.2 ℓ0 hℓ0mem.1, hs]⟩
        · have hvv0 : v + v0 ∈ P := P.add_mem hv hv0P
          have hsum : ∑ i, ρ (v + v0) i = 0 := by
            simp only [ρ, Pi.add_apply, Finset.sum_add_distrib, hs, hsumv0]
            exact CharTwo.add_self_eq_zero 1
          obtain ⟨w, hwL, hwρ⟩ := (hK _).mp ((hKpar _).mpr hsum)
          have hw := hLsub w hwL
          have hwv : w = v + v0 := hρinj hw.1 ((hmemSP _).mpr hvv0) hwρ
          rw [hwv] at hw
          have hoff : ∀ ℓ ∉ I, v ℓ = v0 ℓ := fun ℓ hℓ => F_eq_of_add _ _ (hw.2 ℓ hℓ)
          exact ⟨fun ℓ hℓ hne => by rw [hoff ℓ hℓ, hv0off ℓ hℓ hne],
            by rw [hoff ℓ0 hℓ0mem.1, hv0ℓ0, hs]⟩
      have hsplit : ∀ v : ι → F, (∀ ℓ ∉ I, ℓ ≠ ℓ0 → v ℓ = 0) →
          ∑ i, v i = ∑ i : I, v i + v ℓ0 := by
        intro v hv
        rw [← Finset.sum_add_sum_compl I v, Finset.sum_coe_sort I v]
        congr 1
        rw [Finset.sum_eq_single_of_mem ℓ0 (by simpa using hℓ0mem.1)]
        intro ℓ hℓ hne
        exact hv ℓ (by simpa using hℓ) hne
      refine ⟨insert ℓ0 I, by rw [Finset.card_insert_of_notMem hℓ0mem.1, hI], fun v => ?_⟩
      constructor
      · intro hv
        obtain ⟨h1, h2⟩ := hclaim v hv
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [Finset.mem_insert, not_or] at hi
          exact h1 i hi.2 hi.1
        · rw [hsplit v h1, h2]
          exact CharTwo.add_self_eq_zero _
      · rintro ⟨h1, h2⟩
        have h1' : ∀ ℓ ∉ I, ℓ ≠ ℓ0 → v ℓ = 0 := fun ℓ hℓ hne =>
          h1 ℓ (by rw [Finset.mem_insert, not_or]; exact ⟨hne, hℓ⟩)
        obtain ⟨w, hwSP, hwρ⟩ := hsurj (ρ v)
        have hwP := (hmemSP w).mp hwSP
        obtain ⟨hw1, hw2⟩ := hclaim w hwP
        have hIeq : ∀ i : I, w i = v i := fun i => congrFun hwρ i
        have hsumeq : ∑ i : I, w i = ∑ i : I, v i := Finset.sum_congr rfl (fun i _ => hIeq i)
        have hvℓ0 : v ℓ0 = ∑ i : I, v i := by
          rw [hsplit v h1'] at h2
          exact (F_eq_of_add _ _ (by rw [add_comm]; exact h2))
        have hwv : w = v := by
          funext i
          by_cases hi : i ∈ I
          · exact hIeq ⟨i, hi⟩
          · by_cases hil : i = ℓ0
            · rw [hil, hw2, hsumeq, hvℓ0]
            · rw [hw1 i hi hil, h1' i hi hil]
        rw [← hwv]
        exact hwP

def chi (z : F) : ℚ := if z = 0 then 1 else -1

theorem one_add_one_F : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1

theorem chi_add (a b : F) : chi (a + b) = chi a * chi b := by
  rcases F_cases a with rfl | rfl <;> rcases F_cases b with rfl | rfl
  · simp [chi]
  · simp [chi]
  · simp [chi]
  · rw [one_add_one_F]; simp [chi]

theorem chi_sum {ι : Type} (s : Finset ι) (v : ι → F) :
    chi (∑ i ∈ s, v i) = ∏ i ∈ s, chi (v i) := by
  induction s using Finset.induction_on with
  | empty => simp [chi]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

theorem ind_chi (z : F) : (if z = 0 then (1 : ℚ) else 0) = (1 + chi z) / 2 := by
  rcases F_cases z with rfl | rfl <;> simp [chi]

theorem chi_sq (z : F) : chi z * chi z = 1 := by
  rcases F_cases z with rfl | rfl <;> simp [chi]

theorem prod_h {ι : Type} [Fintype ι] (T : Finset ι) (x : ℚ) (v : ι → F) :
    ∏ i, (if v i = 0 then 1 else if i ∈ T then x else 0) =
      if (∀ i ∉ T, v i = 0) then x ^ (wt v) else 0 := by
  split_ifs with h
  · rw [pow_wt]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hv : v i = 0
    · simp [hv]
    · have hi : i ∈ T := by by_contra hi; exact hv (h i hi)
      simp [hv, hi]
  · push_neg at h
    obtain ⟨i, hi, hv⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hv, hi])

theorem even_sum {ι : Type} [Fintype ι] (T : Finset ι) (x : ℚ) :
    ∑ v ∈ Finset.univ.filter (fun v : ι → F => (∀ i ∉ T, v i = 0) ∧ ∑ i, v i = 0),
      x ^ (wt v) = ((1 + x) ^ T.card + (1 - x) ^ T.card) / 2 := by
  rw [Finset.sum_filter]
  have hpt : ∀ v : ι → F, (if (∀ i ∉ T, v i = 0) ∧ ∑ i, v i = 0 then x ^ (wt v) else 0) =
      (1/2) * ∏ i, (if v i = 0 then 1 else if i ∈ T then x else 0) +
      (1/2) * ∏ i, ((if v i = 0 then 1 else if i ∈ T then x else 0) * chi (v i)) := by
    intro v
    rw [Finset.prod_mul_distrib, ← chi_sum, prod_h]
    have := ind_chi (∑ i, v i)
    by_cases h1 : ∀ i ∉ T, v i = 0
    · by_cases h2 : ∑ i, v i = 0
      · rw [if_pos ⟨h1, h2⟩, if_pos h1]; rw [if_pos h2] at this
        have hc : chi (∑ i, v i) = 1 := by linarith
        rw [hc]; ring
      · rw [if_neg (fun h => h2 h.2), if_pos h1]; rw [if_neg h2] at this
        have hc : chi (∑ i, v i) = -1 := by linarith
        rw [hc]; ring
    · rw [if_neg (fun h => h1 h.1), if_neg h1]; ring
  rw [Finset.sum_congr rfl (fun v _ => hpt v), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun i z => if z = 0 then (1 : ℚ) else if i ∈ T then x else 0),
    ← Fintype.prod_sum (fun i z => (if z = 0 then (1 : ℚ) else if i ∈ T then x else 0) * chi z)]
  have e1 : ∀ i, (∑ z : F, (if z = 0 then (1 : ℚ) else if i ∈ T then x else 0)) =
      if i ∈ T then 1 + x else 1 := by
    intro i; rw [sum_F]; by_cases hi : i ∈ T <;> simp [hi]
  have e2 : ∀ i, (∑ z : F, (if z = 0 then (1 : ℚ) else if i ∈ T then x else 0) * chi z) =
      if i ∈ T then 1 - x else 1 := by
    intro i; rw [sum_F]; by_cases hi : i ∈ T <;> simp [hi, chi] <;> ring
  rw [Finset.prod_congr rfl (fun i _ => e1 i), Finset.prod_congr rfl (fun i _ => e2 i),
    Finset.prod_ite_mem, Finset.prod_ite_mem]
  simp only [Finset.univ_inter, Finset.prod_const]
  ring

theorem char_count {ι : Type} [Fintype ι] [DecidableEq ι] (S A : Finset ι) :
    ∑ y : ι → F, (∏ i, (if i ∈ S then (if y i = 0 then (1 : ℚ) else 0) else 1)) *
      ∏ i, (if i ∈ A then chi (y i) else 1) =
      if A ⊆ S then 2 ^ (Fintype.card ι - S.card) else 0 := by
  rw [show (fun y : ι → F => (∏ i, (if i ∈ S then (if y i = 0 then (1 : ℚ) else 0) else 1)) *
      ∏ i, (if i ∈ A then chi (y i) else 1)) = fun y => ∏ i,
      ((if i ∈ S then (if y i = 0 then (1 : ℚ) else 0) else 1) *
        (if i ∈ A then chi (y i) else 1)) from funext fun y => (Finset.prod_mul_distrib).symm]
  rw [← Fintype.prod_sum (fun i z => (if i ∈ S then (if z = 0 then (1 : ℚ) else 0) else 1) *
        (if i ∈ A then chi z else 1))]
  have e : ∀ i, (∑ z : F, (if i ∈ S then (if z = 0 then (1 : ℚ) else 0) else 1) *
        (if i ∈ A then chi z else 1)) =
      if i ∈ S then 1 else if i ∈ A then 0 else 2 := by
    intro i; rw [sum_F]
    by_cases hS : i ∈ S <;> by_cases hA : i ∈ A <;> simp [hS, hA, chi] <;> norm_num
  rw [Finset.prod_congr rfl (fun i _ => e i)]
  split_ifs with hAS
  · rw [Finset.prod_congr rfl (fun i _ => show (if i ∈ S then (1 : ℚ) else if i ∈ A then 0 else 2)
        = if i ∈ S then 1 else 2 from by
          by_cases hS : i ∈ S
          · simp [hS]
          · have : i ∉ A := fun h => hS (hAS h)
            simp [hS, this])]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    simp
  · rw [Finset.not_subset] at hAS
    obtain ⟨i, hiA, hiS⟩ := hAS
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hiS, hiA])

section Concrete

variable (t : ℕ)

def R0 : Finset (Fin (3 * t)) := Finset.univ.filter (fun i => i.val % 3 = 0 ∨ i.val % 3 = 2)
def R1 : Finset (Fin (3 * t)) := Finset.univ.filter (fun i => i.val % 3 = 1 ∨ i.val % 3 = 2)
def R2 : Finset (Fin (3 * t)) := Finset.univ.filter (fun i => i.val % 3 = 0 ∨ i.val % 3 = 1)

def codeF (y : Fin (3 * t) → F) : Prop := ∑ i ∈ R0 t, y i = 0 ∧ ∑ i ∈ R1 t, y i = 0

noncomputable def cntS (S : Finset (Fin (3 * t))) : ℕ :=
  (Finset.univ.filter (fun y : Fin (3 * t) → F => codeF t y ∧ ∀ i ∈ S, y i = 0)).card

noncomputable def cval (S : Finset (Fin (3 * t))) : ℚ :=
  1 + (if R0 t ⊆ S then 1 else 0) + (if R1 t ⊆ S then 1 else 0) + (if R2 t ⊆ S then 1 else 0)

theorem cval_le (S : Finset (Fin (3 * t))) : cval t S ≤ 4 := by
  unfold cval; split_ifs <;> norm_num

theorem prod_ind {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (y : ι → F) :
    ∏ i, (if i ∈ S then (if y i = 0 then (1 : ℚ) else 0) else 1) =
      if ∀ i ∈ S, y i = 0 then 1 else 0 := by
  split_ifs with h
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : i ∈ S
    · simp [hi, h i hi]
    · simp [hi]
  · push_neg at h
    obtain ⟨i, hi, hy⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hy])

theorem prod_chi_mem {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (y : ι → F) :
    ∏ i, (if i ∈ A then chi (y i) else 1) = chi (∑ i ∈ A, y i) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter, chi_sum]

theorem cnt_formula (S : Finset (Fin (3 * t))) :
    4 * (cntS t S : ℚ) = 2 ^ (3 * t - S.card) * cval t S := by
  unfold cntS
  rw [Finset.card_filter]
  push_cast
  set Q := fun (A : Finset (Fin (3 * t))) (y : Fin (3 * t) → F) =>
    ∏ i, (if i ∈ A then chi (y i) else 1) with hQ
  set PS := fun (y : Fin (3 * t) → F) =>
    ∏ i, (if i ∈ S then (if y i = 0 then (1 : ℚ) else 0) else 1) with hPS
  have hQ2 : ∀ y, Q (R2 t) y = Q (R0 t) y * Q (R1 t) y := by
    intro y
    simp only [hQ]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [R0, R1, R2, Finset.mem_filter, Finset.mem_univ, true_and]
    have h3 : i.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have := chi_sq (y i)
    rcases (by omega : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2) with h | h | h <;>
      simp [h, this]
  have hpt : ∀ y : Fin (3 * t) → F, (if codeF t y ∧ ∀ i ∈ S, y i = 0 then (1 : ℚ) else 0) =
      (1/4) * (PS y * Q ∅ y + PS y * Q (R0 t) y + PS y * Q (R1 t) y + PS y * Q (R2 t) y) := by
    intro y
    have hQe : Q ∅ y = 1 := by simp [hQ]
    rw [hQ2, hQe]
    simp only [hPS, hQ]
    rw [prod_ind, prod_chi_mem, prod_chi_mem]
    unfold codeF
    have hc : ∀ z : F, chi z = if z = 0 then 1 else -1 := fun z => rfl
    rw [hc, hc]
    by_cases hS : ∀ i ∈ S, y i = 0
    · have hS' : (∀ i ∈ S, y i = 0) = True := eq_true hS
      by_cases a : ∑ i ∈ R0 t, y i = 0 <;>
        by_cases b : ∑ i ∈ R1 t, y i = 0 <;> simp only [hS', a, b] <;> simp <;> norm_num
    · have hS' : (∀ i ∈ S, y i = 0) = False := eq_false hS
      simp only [hS']
      simp
  rw [Finset.sum_congr rfl (fun y _ => hpt y), ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, hPS, hQ]
  rw [char_count, char_count, char_count, char_count]
  simp only [Fintype.card_fin, Finset.empty_subset, if_true]
  unfold cval
  split_ifs <;> ring

end Concrete

section Glue

variable {t : ℕ}

theorem card_R0 : 2 * t ≤ (R0 t).card := by
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (2 * t)))) (t := R0 t)
    (fun m => (⟨3 * (m.val / 2) + 2 * (m.val % 2), by omega⟩ : Fin (3 * t)))
    (by intro m _; simp only [R0, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq]; omega)
    (by intro a _ b _ hab; simp only [Fin.mk.injEq] at hab; ext; omega)
  simpa using h

theorem card_R1 : 2 * t ≤ (R1 t).card := by
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (2 * t)))) (t := R1 t)
    (fun m => (⟨3 * (m.val / 2) + 1 + (m.val % 2), by omega⟩ : Fin (3 * t)))
    (by intro m _; simp only [R1, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq]; omega)
    (by intro a _ b _ hab; simp only [Fin.mk.injEq] at hab; ext; omega)
  simpa using h

theorem card_R2 : 2 * t ≤ (R2 t).card := by
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (2 * t)))) (t := R2 t)
    (fun m => (⟨3 * (m.val / 2) + (m.val % 2), by omega⟩ : Fin (3 * t)))
    (by intro m _; simp only [R2, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq]; omega)
    (by intro a _ b _ hab; simp only [Fin.mk.injEq] at hab; ext; omega)
  simpa using h

theorem cval_one {S : Finset (Fin (3 * t))} (hS : S.card < 2 * t) : cval t S = 1 := by
  unfold cval
  have h0 : ¬ R0 t ⊆ S := fun h => by have := Finset.card_le_card h; have := card_R0 (t := t); omega
  have h1 : ¬ R1 t ⊆ S := fun h => by have := Finset.card_le_card h; have := card_R1 (t := t); omega
  have h2 : ¬ R2 t ⊆ S := fun h => by have := Finset.card_le_card h; have := card_R2 (t := t); omega
  simp [h0, h1, h2]

def sh (ht : 0 < t) (i : Fin (3 * t)) : Fin (3 * t) :=
  ⟨(i.val + 1) % (3 * t), Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩

theorem sh_val (ht : 0 < t) (i : Fin (3 * t)) :
    (sh ht i).val = if i.val + 1 < 3 * t then i.val + 1 else 0 := by
  unfold sh
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : i.val + 1 = 3 * t := by have := i.isLt; omega
    simp only [this, Nat.mod_self]

theorem sh_inj (ht : 0 < t) : Function.Injective (sh ht) := by
  intro a b h
  have h' := congrArg Fin.val h
  rw [sh_val, sh_val] at h'
  ext
  have := a.isLt; have := b.isLt
  split_ifs at h' <;> omega

def Nb (ht : 0 < t) (p : Fin (3 * t) → F) : Finset (Fin (3 * t)) :=
  Finset.univ.filter (fun i => p i ≠ 0 ∨ p (sh ht i) ≠ 0)

theorem card_Nb (ht : 0 < t) (p : Fin (3 * t) → F) (hs : ∀ i, ¬ (p i ≠ 0 ∧ p (sh ht i) ≠ 0)) :
    (Nb ht p).card = 2 * wt p := by
  have hsplit : Nb ht p = Finset.univ.filter (fun i => p i ≠ 0) ∪
      Finset.univ.filter (fun i => p (sh ht i) ≠ 0) := by
    ext i; simp [Nb]
  have hpre : (Finset.univ.filter (fun i => p (sh ht i) ≠ 0)).card = wt p := by
    unfold wt
    apply Finset.card_bij (fun i _ => sh ht i)
    · intro i hi; simpa using hi
    · intro a _ b _ h; exact sh_inj ht h
    · intro k hk
      obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.mp (sh_inj ht)) k
      exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hi]; simpa using hk, hi⟩
  rw [hsplit, Finset.card_union_of_disjoint, hpre]
  · unfold wt; ring
  · rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hs i ⟨h1, h2⟩

theorem no_wt_one {p : Fin (3 * t) → F} (hc : codeF t p) : wt p ≠ 1 := by
  intro h1
  unfold wt at h1
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h1
  have hpk : p k ≠ 0 := by
    have := Finset.mem_singleton_self k; rw [← hk] at this; simpa using this
  have hoff : ∀ i, i ≠ k → p i = 0 := by
    intro i hi; by_contra h
    have : i ∈ Finset.univ.filter (fun i => p i ≠ 0) := by simp [h]
    rw [hk] at this; exact hi (Finset.mem_singleton.mp this)
  have hp1 : p k = 1 := (F_cases _).resolve_left hpk
  have hsum : ∀ R : Finset (Fin (3 * t)), k ∈ R → ∑ i ∈ R, p i = 1 := by
    intro R hR
    rw [Finset.sum_eq_single k (fun i _ hi => hoff i hi) (fun h => absurd hR h), hp1]
  obtain ⟨h0, h1'⟩ := hc
  have h3 : k.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : k.val % 3 = 0 ∨ k.val % 3 = 1 ∨ k.val % 3 = 2) with h | h | h
  · have := hsum (R0 t) (by simp [R0, h]); rw [this] at h0; exact one_ne_zero h0
  · have := hsum (R1 t) (by simp [R1, h]); rw [this] at h1'; exact one_ne_zero h1'
  · have := hsum (R0 t) (by simp [R0, h]); rw [this] at h0; exact one_ne_zero h0

end Glue

theorem B_mul (j : ℕ) : B j * 8 ^ (j + 1) = ((5 : ℚ) ^ (j + 1) + 3 ^ (j + 1)) * 2 ^ j := by
  unfold B
  rw [show (8 : ℚ) ^ (j + 1) = 8 * (4 ^ j * 2 ^ j) by rw [pow_succ, ← mul_pow]; norm_num; ring]
  rw [div_pow, div_pow]
  field_simp
  ring

theorem B_even (j : ℕ) : ((1 + 1/4 : ℚ) ^ (j + 1) + (1 - 1/4) ^ (j + 1)) / 2 = B j := by
  unfold B; norm_num; ring

theorem sum_pair_ind {ι : Type} [Fintype ι] [DecidableEq ι] (R : Finset ι) (i i0 : ι) (hne : i ≠ i0) :
    ∑ k ∈ R, (if k = i ∨ k = i0 then (1 : F) else 0) =
      (if i ∈ R then 1 else 0) + (if i0 ∈ R then 1 else 0) := by
  have hpt : ∀ k, (if k = i ∨ k = i0 then (1 : F) else 0) =
      (if k = i then 1 else 0) + (if k = i0 then 1 else 0) := by
    intro k
    by_cases h1 : k = i
    · subst h1; simp [hne]
    · by_cases h2 : k = i0
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']

theorem F_ind_add {a b : Prop} [Decidable a] [Decidable b]
    (h : (if a then (1 : F) else 0) + (if b then 1 else 0) = 0) : (a ↔ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [ha, hb, if_true, if_false] at h ⊢
  · exact absurd (h.symm.trans (zero_add 1)) zero_ne_one
  · exact absurd (h.symm.trans (add_zero 1)) zero_ne_one

theorem final (t : ℕ) (ht : 0 < t) (j : ℕ) (hj1 : 1 ≤ j) (hjt : j + 3 ≤ t)
    (P : Submodule F (Fin (3 * t) → F)) (hP : Module.finrank F P = j)
    (hcode : ∀ x ∈ P, codeF t x) (hsep : ∀ p ∈ P, ∀ i, ¬ (p i ≠ 0 ∧ p (sh ht i) ≠ 0)) :
    (8 ^ (j + 1) * ∑ p ∈ Finset.univ.filter (fun p => p ∈ P), cntS t (Nb ht p) ≤
      (5 ^ (j + 1) + 3 ^ (j + 1)) * (2 ^ j * cntS t ∅)) ∧
    (8 ^ (j + 1) * ∑ p ∈ Finset.univ.filter (fun p => p ∈ P), cntS t (Nb ht p) =
      (5 ^ (j + 1) + 3 ^ (j + 1)) * (2 ^ j * cntS t ∅) ↔
      ∃ (T : Finset (Fin (3 * t))) (e : Fin 3), T.card = j + 1 ∧
        (∀ i ∈ T, i.val % 3 = e.val) ∧ ∀ x : Fin (3 * t) → F,
          x ∈ P ↔ (∀ i, i ∉ T → x i = 0) ∧ (∑ i, x i) = 0) := by
  have hno1 : ∀ p ∈ P, wt p ≠ 1 := fun p hp => no_wt_one (hcode p hp)
  have hcardNb : ∀ p ∈ P, (Nb ht p).card = 2 * wt p := fun p hp => card_Nb ht p (hsep p hp)
  set cf : (Fin (3 * t) → F) → ℚ := fun p => if p ∈ P then cval t (Nb ht p) else 1 with hcf
  have hcf4 : ∀ p, cf p ≤ 4 := by
    intro p; simp only [hcf]; split_ifs
    · exact cval_le t _
    · norm_num
  have hcfl : ∀ p, wt p ≤ j + 2 → cf p = 1 := by
    intro p hw; simp only [hcf]; split_ifs with hp
    · exact cval_one (by rw [hcardNb p hp]; omega)
    · rfl
  obtain ⟨hle, heq⟩ := mainQ j (Fin (3 * t)) P cf hP (by rw [Fintype.card_fin]; omega) hno1 hcf4 hcfl
  set S := ∑ v ∈ Finset.univ.filter (fun v => v ∈ P), (1/4 : ℚ) ^ (wt v) * cf v with hSdef
  have hle' : S ≤ B j := by
    refine (le_of_eq ?_).trans hle
    exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
  have heq' : S = B j → ∃ T : Finset (Fin (3 * t)), T.card = j + 1 ∧
      ∀ v, v ∈ P ↔ (∀ i ∉ T, v i = 0) ∧ ∑ i, v i = 0 := by
    intro h
    obtain ⟨T, hT1, hT2⟩ := heq (by rw [← h, hSdef]; try exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl))
    exact ⟨T, hT1, fun v => by rw [hT2 v]⟩

  have hcnt0 : (cntS t ∅ : ℚ) = 2 ^ (3 * t - 2) := by
    have h := cnt_formula t ∅
    rw [cval_one (by simp; omega), Finset.card_empty, Nat.sub_zero, mul_one] at h
    have h2 : (2 : ℚ) ^ (3 * t) = 4 * 2 ^ (3 * t - 2) := by
      rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    linarith
  have hcntp : ∀ p ∈ P, (cntS t (Nb ht p) : ℚ) = 2 ^ (3 * t - 2) * ((1/4 : ℚ) ^ (wt p) * cf p) := by
    intro p hp
    have h := cnt_formula t (Nb ht p)
    have hle2 : 2 * wt p ≤ 3 * t := by
      rw [← hcardNb p hp]; exact (Finset.card_le_univ _).trans (by simp)
    rw [hcardNb p hp] at h
    have hcfp : cf p = cval t (Nb ht p) := by simp only [hcf, if_pos hp]
    rw [hcfp]
    have e1 : (2 : ℚ) ^ (3 * t - 2 * wt p) * 4 ^ (wt p) = 2 ^ (3 * t) := by
      rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega
    have e2 : (2 : ℚ) ^ (3 * t - 2) * 4 = 2 ^ (3 * t) := by
      rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have h4 : (0 : ℚ) < 4 ^ (wt p) := by positivity
    have key : 4 * ((cntS t (Nb ht p) : ℚ) * 4 ^ (wt p)) = 4 * (2 ^ (3 * t - 2) * cval t (Nb ht p)) := by
      calc 4 * ((cntS t (Nb ht p) : ℚ) * 4 ^ (wt p))
          = (4 * (cntS t (Nb ht p) : ℚ)) * 4 ^ (wt p) := by ring
        _ = 2 ^ (3 * t - 2 * wt p) * cval t (Nb ht p) * 4 ^ (wt p) := by rw [h]
        _ = (2 ^ (3 * t - 2 * wt p) * 4 ^ (wt p)) * cval t (Nb ht p) := by ring
        _ = (2 ^ (3 * t - 2) * 4) * cval t (Nb ht p) := by rw [e1, e2]
        _ = 4 * (2 ^ (3 * t - 2) * cval t (Nb ht p)) := by ring
    have key2 := mul_left_cancel₀ (by norm_num : (4 : ℚ) ≠ 0) key
    rw [one_div_pow]
    field_simp
    linarith [key2]
  have hhits : ((∑ p ∈ Finset.univ.filter (fun p => p ∈ P), cntS t (Nb ht p) : ℕ) : ℚ) =
      2 ^ (3 * t - 2) * S := by
    push_cast
    rw [hSdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hcntp p hp
  have hB := B_mul j
  have hpos : (0 : ℚ) < 2 ^ (3 * t - 2) := by positivity
  have h8 : (0 : ℚ) < 8 ^ (j + 1) := by positivity
  have hscore : ((8 ^ (j + 1) * ∑ p ∈ Finset.univ.filter (fun p => p ∈ P), cntS t (Nb ht p) : ℕ) : ℚ)
      = 8 ^ (j + 1) * (2 ^ (3 * t - 2) * S) := by
    rw [Nat.cast_mul, hhits]; push_cast; ring
  have hbound : (((5 ^ (j + 1) + 3 ^ (j + 1)) * (2 ^ j * cntS t ∅) : ℕ) : ℚ)
      = 8 ^ (j + 1) * (2 ^ (3 * t - 2) * B j) := by
    push_cast
    rw [hcnt0]
    rw [show (8 : ℚ) ^ (j + 1) * (2 ^ (3 * t - 2) * B j) = 2 ^ (3 * t - 2) * (B j * 8 ^ (j + 1)) by ring,
      hB]
    ring
  have hiffS : (8 ^ (j + 1) * ∑ p ∈ Finset.univ.filter (fun p => p ∈ P), cntS t (Nb ht p) =
      (5 ^ (j + 1) + 3 ^ (j + 1)) * (2 ^ j * cntS t ∅)) ↔ S = B j := by
    rw [← Nat.cast_inj (R := ℚ), hscore, hbound]
    constructor
    · intro h
      have := mul_left_cancel₀ (ne_of_gt h8) h
      exact mul_left_cancel₀ (ne_of_gt hpos) this
    · intro h; rw [h]
  refine ⟨?_, ?_⟩
  · have hQ : ((8 ^ (j + 1) * ∑ p ∈ Finset.univ.filter (fun p => p ∈ P), cntS t (Nb ht p) : ℕ) : ℚ)
        ≤ (((5 ^ (j + 1) + 3 ^ (j + 1)) * (2 ^ j * cntS t ∅) : ℕ) : ℚ) := by
      rw [hscore, hbound]
      apply mul_le_mul_of_nonneg_left _ h8.le
      exact mul_le_mul_of_nonneg_left hle' hpos.le
    exact_mod_cast hQ
  · rw [hiffS]
    constructor
    · intro hS
      obtain ⟨T, hTc, hT⟩ := heq' hS
      obtain ⟨i0, hi0⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
      refine ⟨T, ⟨i0.val % 3, Nat.mod_lt _ (by norm_num)⟩, hTc, ?_, hT⟩
      intro i hi
      show i.val % 3 = i0.val % 3
      by_cases hne : i = i0
      · rw [hne]
      · let w : Fin (3 * t) → F := fun k => if k = i ∨ k = i0 then 1 else 0
        have hw : w ∈ P := by
          rw [hT]
          refine ⟨fun k hk => ?_, ?_⟩
          · simp only [w]
            rw [if_neg]
            rintro (rfl | rfl)
            · exact hk hi
            · exact hk hi0
          · rw [sum_pair_ind Finset.univ i i0 hne]
            simp only [Finset.mem_univ, if_true]
            exact one_add_one_F
        obtain ⟨h0, h1⟩ := hcode w hw
        rw [sum_pair_ind _ i i0 hne] at h0 h1
        have e0 := F_ind_add h0
        have e1 := F_ind_add h1
        simp only [R0, R1, Finset.mem_filter, Finset.mem_univ, true_and] at e0 e1
        have := i.isLt; have := i0.isLt
        have h3 : i.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
        have h4 : i0.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
        omega
    · rintro ⟨T, e, hTc, _, hT⟩
      rw [hSdef]
      have hcf1 : ∀ v ∈ Finset.univ.filter (fun v => v ∈ P), (1/4 : ℚ) ^ (wt v) * cf v =
          (1/4 : ℚ) ^ (wt v) := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have hwt : wt v ≤ j + 2 := by
          have hsub : Finset.univ.filter (fun i => v i ≠ 0) ⊆ T := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            by_contra h
            exact hi (((hT v).mp hv).1 i h)
          have := Finset.card_le_card hsub
          unfold wt; omega
        rw [hcfl v hwt, mul_one]
      rw [Finset.sum_congr rfl hcf1]
      have hset : Finset.univ.filter (fun v => v ∈ P) = Finset.univ.filter
          (fun v : Fin (3 * t) → F => (∀ i ∉ T, v i = 0) ∧ ∑ i, v i = 0) := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hT v
      rw [hset]
      have hev := even_sum T (1/4 : ℚ)
      rw [hTc, B_even] at hev
      convert hev using 1
      exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)

end PEqualNP.Outside.L_lib_1060

theorem PEqualNP.Outside.L_lib_1060 : (∀ (t : ℕ) (ht : 0 < t) (j : ℕ), 1 ≤ j → j+3 ≤ t →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 3*t
  let W := Fin n → F
  let ix := fun i : ℕ => (⟨i % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin n)
  let code := fun (x : W) => ∀ e : Fin 2,
    (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0
  ∀ P : Submodule F W, Module.finrank F P = j → (∀ x ∈ P, code x) →
    let live := fun (i : Fin n) => ∃ x ∈ P, x i ≠ 0
    (∀ i, ¬ (live i ∧ live (ix (i.val+1)))) →
    let size := Nat.card P * Nat.card {y : W // code y}
    let hits := Nat.card {w : W × W // w.1 ∈ P ∧ code w.2 ∧ ∀ i : Fin n,
      w.1 i * w.2 i = 0 ∧ w.1 (ix (i.val+1)) * w.2 i = 0}
    let top := ∃ (T : Finset (Fin n)) (e : Fin 3), T.card = j+1 ∧
      (∀ i ∈ T, i.val % 3 = e.val) ∧ ∀ x : W,
        x ∈ P ↔ (∀ i, i ∉ T → x i = 0) ∧ (∑ i, x i) = 0
    let score := 8^(j+1)*hits
    let bound := (5^(j+1)+3^(j+1))*size
    score ≤ bound ∧ (score = bound ↔ top)) := by
  intro t ht j hj1 hjt F n W ix code P hP hcode live hsep size hits top score bound
  classical
  have hcodeF : ∀ x : Fin (3 * t) → ZMod 2, code x ↔ PEqualNP.Outside.L_lib_1060.codeF t x := by
    intro x
    simp only [code, PEqualNP.Outside.L_lib_1060.codeF, PEqualNP.Outside.L_lib_1060.R0,
      PEqualNP.Outside.L_lib_1060.R1, Fin.forall_fin_two, Finset.sum_filter]
    simp only [Fin.val_zero, Fin.val_one]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨by convert h0 using 4, by convert h1 using 4⟩
    · rintro ⟨h0, h1⟩
      exact ⟨by convert h0 using 4, by convert h1 using 4⟩
  have hsepP : ∀ p ∈ P, ∀ i, ¬ (p i ≠ 0 ∧ p (PEqualNP.Outside.L_lib_1060.sh ht i) ≠ 0) := by
    intro p hp i ⟨h1, h2⟩
    exact hsep i ⟨⟨p, hp, h1⟩, ⟨p, hp, h2⟩⟩
  obtain ⟨hA, hB⟩ := PEqualNP.Outside.L_lib_1060.final t ht j hj1 hjt P hP
    (fun x hx => (hcodeF x).mp (hcode x hx)) hsepP
  have hhits : hits = ∑ p ∈ Finset.univ.filter (fun p => p ∈ P),
      PEqualNP.Outside.L_lib_1060.cntS t (PEqualNP.Outside.L_lib_1060.Nb ht p) := by
    simp only [hits]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
      ← Finset.univ_product_univ, Finset.sum_product, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p ∈ P
    · rw [if_pos hp]
      unfold PEqualNP.Outside.L_lib_1060.cntS
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro y _
      apply if_congr _ rfl rfl
      rw [hcodeF]
      simp only [hp, true_and]
      apply and_congr_right
      intro _
      constructor
      · intro h i hi
        simp only [PEqualNP.Outside.L_lib_1060.Nb, Finset.mem_filter, Finset.mem_univ,
          true_and] at hi
        rcases hi with hi | hi
        · exact (mul_eq_zero.mp (h i).1).resolve_left hi
        · exact (mul_eq_zero.mp (h i).2).resolve_left hi
      · intro h i
        by_cases hi : i ∈ PEqualNP.Outside.L_lib_1060.Nb ht p
        · have := h i hi
          exact ⟨by rw [this, mul_zero], by rw [this, mul_zero]⟩
        · simp only [PEqualNP.Outside.L_lib_1060.Nb, Finset.mem_filter, Finset.mem_univ,
            true_and, not_or, not_not] at hi
          exact ⟨by rw [hi.1, zero_mul], by
            show p (PEqualNP.Outside.L_lib_1060.sh ht i) * y i = 0
            rw [hi.2, zero_mul]⟩
    · rw [if_neg hp]
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg]
      rintro ⟨h, _⟩
      exact hp h
  have hsize : size = 2 ^ j * PEqualNP.Outside.L_lib_1060.cntS t ∅ := by
    simp only [size]
    congr 1
    · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hP]
    · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      unfold PEqualNP.Outside.L_lib_1060.cntS
      congr 1
      ext y
      simp [hcodeF]
  simp only [score, bound]
  rw [hhits, hsize]
  exact ⟨hA, hB⟩
