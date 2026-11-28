import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_435_aux

open Module

abbrev F := ZMod 2

theorem two_zero : (2 : F) = 0 := rfl

theorem F_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem one_of_ne_zero {a : F} (h : a ≠ 0) : a = 1 := (F_cases a).resolve_left h

theorem F_add_self (a : F) : a + a = 0 := by
  rcases F_cases a with rfl | rfl <;> rfl

theorem eq_of_add_zero {a b : F} (h : a + b = 0) : a = b := by
  calc a = a + (b + b) := by rw [F_add_self, add_zero]
    _ = (a + b) + b := by rw [add_assoc]
    _ = b := by rw [h, zero_add]

section Gen
variable {V : Type} [AddCommGroup V] [Module F V]

theorem self_add (u : V) : u + u = 0 := by
  rw [← two_smul F u, two_zero, zero_smul]

theorem smul_cases (c : F) (u : V) : c • u = 0 ∨ c • u = u := by
  rcases F_cases c with rfl | rfl
  · left; exact zero_smul F u
  · right; exact one_smul F u

variable [FiniteDimensional F V]

theorem finrank_span_le (p : V) : finrank F (F ∙ p) ≤ 1 := by
  simpa using finrank_span_le_card ({p} : Set V)

theorem finrank_sup_span (S : Submodule F V) {v : V} (hv : v ∉ S) :
    finrank F (S ⊔ F ∙ v : Submodule F V) = finrank F S + 1 := by
  have h0 : S ⊓ (F ∙ v) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxv⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxv
    rcases smul_cases c v with h | h
    · rw [h]; exact Submodule.zero_mem _
    · rw [h] at hxS; exact absurd hxS hv
  have hv0 : v ≠ 0 := fun h => hv (h ▸ S.zero_mem)
  have := Submodule.finrank_sup_add_finrank_inf_eq S (F ∙ v)
  rw [h0, finrank_bot, finrank_span_singleton hv0] at this
  omega

theorem half_space (S P : Submodule F V) (h : ∀ u ∈ S, ∀ p ∈ S, u ∉ P → p ∉ P → u + p ∈ P) :
    finrank F S ≤ finrank F (P ⊓ S : Submodule F V) + 1 := by
  by_cases hle : S ≤ P
  · have : P ⊓ S = S := inf_eq_right.mpr hle
    rw [this]; omega
  · obtain ⟨p, hpS, hpP⟩ := Set.not_subset.1 hle
    have hsub : S ≤ (P ⊓ S) ⊔ F ∙ p := by
      intro u hu
      by_cases huP : u ∈ P
      · exact Submodule.mem_sup_left ⟨huP, hu⟩
      · have h1 : u + p ∈ P ⊓ S := ⟨h u hu p hpS huP hpP, S.add_mem hu hpS⟩
        have h2 : u = (u + p) + p := by rw [add_assoc, self_add, add_zero]
        rw [h2]
        exact Submodule.add_mem_sup h1 (Submodule.mem_span_singleton_self p)
    have h3 := Submodule.finrank_mono hsub
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ S) (F ∙ p)
    have h5 := finrank_span_le p
    omega

theorem exists_between (S S' : Submodule F V) (h : S ≤ S') :
    ∀ k, finrank F S + k ≤ finrank F S' →
      ∃ M : Submodule F V, S ≤ M ∧ M ≤ S' ∧ finrank F M = finrank F S + k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨S, le_rfl, h, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨M, h1, h2, h3⟩ := ih (by omega)
    have hlt : M < S' := by
      refine lt_of_le_of_ne h2 ?_
      rintro rfl; omega
    obtain ⟨v, hvS, hvM⟩ := SetLike.exists_of_lt hlt
    refine ⟨M ⊔ F ∙ v, le_trans h1 le_sup_left, sup_le h2 ?_, ?_⟩
    · rw [Submodule.span_le]; simpa using hvS
    · rw [finrank_sup_span M hvM, h3]; ring

theorem exists_map (S : Submodule F V) (k : ℕ) (h : finrank F V ≤ finrank F S + k) :
    ∃ φ : V →ₗ[F] (Fin k → F), LinearMap.ker φ ≤ S := by
  have hq := Submodule.finrank_quotient_add_finrank S
  set c := finrank F (V ⧸ S) with hc
  have hck : c ≤ k := by omega
  let b := Module.finBasis F (V ⧸ S)
  let emb : (Fin (finrank F (V ⧸ S)) → F) →ₗ[F] (Fin k → F) :=
    { toFun := fun x j => if hj : j.val < finrank F (V ⧸ S) then x ⟨j.val, hj⟩ else 0
      map_add' := by
        intro x y; funext j
        by_cases hj : j.val < finrank F (V ⧸ S) <;> simp [hj]
      map_smul' := by
        intro a x; funext j
        by_cases hj : j.val < finrank F (V ⧸ S) <;> simp [hj] }
  refine ⟨emb ∘ₗ b.equivFun.toLinearMap ∘ₗ S.mkQ, ?_⟩
  intro v hv
  rw [LinearMap.mem_ker] at hv
  have h1 : b.equivFun (S.mkQ v) = 0 := by
    funext i
    have := congrFun hv ⟨i.val, lt_of_lt_of_le i.2 hck⟩
    simpa [emb] using this
  have h2 : S.mkQ v = 0 := b.equivFun.injective (by rw [h1, map_zero])
  simpa using h2

end Gen

section Block
variable {V : Type} [AddCommGroup V] [Module F V]

def Bf (f : V → F) (u v : V) : F := f (u+v) + f u + f v + f 0

def Quad (f : V → F) : Prop := ∀ p u v : V, f (p+u+v) + f (p+u) + f (p+v) + f p = Bf f u v

variable {f : V → F}

omit [Module F V] in
theorem Bf_comm (u v : V) : Bf f u v = Bf f v u := by
  unfold Bf; rw [add_comm u v]; ring

omit [Module F V] in
theorem diff_eq (hf : Quad f) (p w : V) : f (p + w) + f p = Bf f p w + f w + f 0 := by
  have h := hf 0 p w
  simp only [zero_add] at h
  rw [← h]
  grind

omit [Module F V] in
theorem Bf_add_right (hf : Quad f) (u v v' : V) : Bf f u (v + v') = Bf f u v + Bf f u v' := by
  have h := hf v u v'
  have e1 : v + u + v' = u + (v + v') := by abel
  have e2 : v + u = u + v := by abel
  rw [e1, e2] at h
  unfold Bf at *
  grind

omit [Module F V] in
theorem Bf_add_left (hf : Quad f) (u u' v : V) : Bf f (u + u') v = Bf f u v + Bf f u' v := by
  rw [Bf_comm, Bf_add_right hf, Bf_comm u, Bf_comm u']

omit [Module F V] in
theorem Bf_zero_right (u : V) : Bf f u 0 = 0 := by
  unfold Bf; simp; grind

omit [Module F V] in
theorem Bf_zero_left (v : V) : Bf f 0 v = 0 := by
  rw [Bf_comm]; exact Bf_zero_right v

theorem Bf_self (u : V) : Bf f u u = 0 := by
  unfold Bf; rw [self_add]; grind

theorem Bf_smul_right (c : F) (u v : V) : Bf f u (c • v) = c • Bf f u v := by
  rcases F_cases c with rfl | rfl
  · rw [zero_smul, zero_smul, Bf_zero_right]
  · rw [one_smul, one_smul]

def bil (hf : Quad f) : LinearMap.BilinForm F V :=
  LinearMap.mk₂ F (Bf f) (fun u u' v => Bf_add_left hf u u' v)
    (fun c u v => by rw [Bf_comm, Bf_smul_right, Bf_comm])
    (fun u v v' => Bf_add_right hf u v v')
    (fun c u v => Bf_smul_right c u v)

theorem bil_apply (hf : Quad f) (u v : V) : bil hf u v = Bf f u v := rfl

def rad (hf : Quad f) : Submodule F V := LinearMap.ker (bil hf)

theorem mem_rad (hf : Quad f) (u : V) : u ∈ rad hf ↔ ∀ v, Bf f u v = 0 := by
  simp only [rad, LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply, bil_apply]

def per (f : V → F) : Submodule F V :=
  { carrier := {u | ∀ p, f (p + u) = f p}, add_mem' := by
      intro a b ha hb p
      simp only [Set.mem_setOf_eq] at *
      rw [← add_assoc, hb, ha]
    zero_mem' := by intro p; simp
    smul_mem' := by
      intro c u hu p
      rcases smul_cases c u with h | h
      · rw [h, add_zero]
      · rw [h]; exact hu p }

theorem mem_per (u : V) : u ∈ per f ↔ ∀ p, f (p + u) = f p := Iff.rfl

theorem per_le_rad (hf : Quad f) : per f ≤ rad hf := by
  intro u hu
  rw [mem_rad]
  intro v
  have h1 := hu v
  have h2 := hu 0
  rw [zero_add] at h2
  unfold Bf
  rw [add_comm u v, h1, h2]
  grind

theorem rad_per_iff (hf : Quad f) {u : V} (hu : u ∈ rad hf) : u ∈ per f ↔ f u + f 0 = 0 := by
  constructor
  · intro h
    have := h 0
    rw [zero_add] at this
    rw [this]; grind
  · intro h p
    have h1 := diff_eq hf p u
    rw [Bf_comm, (mem_rad hf u).1 hu p, zero_add, h] at h1
    exact eq_of_add_zero h1

variable [FiniteDimensional F V]

theorem rad_le_per (hf : Quad f) : finrank F (rad hf) ≤ finrank F (per f) + 1 := by
  have h := half_space (rad hf) (per f) (by
    intro u hu p hp huP hpP
    have hu1 := one_of_ne_zero (fun h => huP ((rad_per_iff hf hu).2 h))
    have hp1 := one_of_ne_zero (fun h => hpP ((rad_per_iff hf hp).2 h))
    rw [rad_per_iff hf ((rad hf).add_mem hu hp)]
    have hB := (mem_rad hf u).1 hu p
    unfold Bf at hB
    grind)
  have : per f ⊓ rad hf = per f := inf_eq_left.mpr (per_le_rad hf)
  rw [this] at h
  exact h

def Iso (f : V → F) (I : Submodule F V) : Prop := ∀ u ∈ I, ∀ v ∈ I, Bf f u v = 0

theorem orth_formula (hf : Quad f) (I : Submodule F V) (hI : rad hf ≤ I) :
    finrank F I + finrank F ((bil hf).orthogonal I) = finrank F V + finrank F (rad hf) := by
  have := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := bil hf) I
  have h2 : I ⊓ LinearMap.ker (bil hf) = rad hf := inf_eq_right.mpr hI
  rw [h2] at this
  exact this

theorem mem_orth (hf : Quad f) (I : Submodule F V) (m : V) :
    m ∈ (bil hf).orthogonal I ↔ ∀ u ∈ I, Bf f u m = 0 := Iff.rfl

theorem iso_le_orth (hf : Quad f) {I : Submodule F V} (h : Iso f I) :
    I ≤ (bil hf).orthogonal I := fun m hm u hu => h u hu m hm

theorem exists_iso (hf : Quad f) : ∀ s : ℕ,
    2 * (finrank F (rad hf) + s) ≤ finrank F V + finrank F (rad hf) →
    ∃ I : Submodule F V, rad hf ≤ I ∧ Iso f I ∧ finrank F I = finrank F (rad hf) + s := by
  intro s
  induction s with
  | zero =>
    intro _
    refine ⟨rad hf, le_rfl, ?_, rfl⟩
    intro u hu v _
    exact (mem_rad hf u).1 hu v
  | succ s ih =>
    intro hs
    obtain ⟨I, h1, h2, h3⟩ := ih (by omega)
    have hJ := orth_formula hf I h1
    have hle := iso_le_orth hf h2
    have hlt : I < (bil hf).orthogonal I := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      rw [← heq] at hJ
      omega
    obtain ⟨v, hvJ, hvI⟩ := SetLike.exists_of_lt hlt
    refine ⟨I ⊔ F ∙ v, le_trans h1 le_sup_left, ?_, ?_⟩
    · intro x hx y hy
      obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx2
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.1 hy2
      rw [← bil_apply hf]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, bil_apply]
      rw [h2 x1 hx1 y1 hy1, (mem_orth hf I v).1 hvJ x1 hx1, Bf_comm v y1,
        (mem_orth hf I v).1 hvJ y1 hy1, Bf_self]
      simp
    · rw [finrank_sup_span I hvI, h3]; ring

def SubProto (f : V → F) (α β : ℕ) : Prop :=
  ∃ K : Submodule F V, finrank F V ≤ finrank F K + α ∧ ∀ x0 : V, ∃ W : Submodule F V,
    W ≤ K ∧ finrank F K ≤ finrank F W + β ∧ ∀ w ∈ W, ∀ k ∈ K, f (x0 + k + w) = f (x0 + k)

def BlockProto (f : V → F) (α β : ℕ) : Prop :=
  ∃ (φ : V →ₗ[F] (Fin α → F)) (ψ : (Fin α → F) → V →ₗ[F] (Fin β → F))
    (o : (Fin α → F) → (Fin β → F) → F), ∀ v, o (φ v) (ψ (φ v) v) = f v

theorem block_of_sub {α β : ℕ} (h : SubProto f α β) : BlockProto f α β := by
  classical
  obtain ⟨K, hK, hW⟩ := h
  choose W hWK hWdim hWinv using hW
  obtain ⟨φ, hφ⟩ := exists_map K α hK
  obtain ⟨C, hC⟩ := K.exists_isCompl
  have hKC := Submodule.finrank_add_eq_of_isCompl hC
  let rep : (Fin α → F) → V := fun t => if h : ∃ v, φ v = t then Classical.choose h else 0
  have hrep : ∀ v, φ (rep (φ v)) = φ v := by
    intro v
    have h : ∃ v', φ v' = φ v := ⟨v, rfl⟩
    simp only [rep, dif_pos h]
    exact Classical.choose_spec h
  have hdimS : ∀ t, finrank F V ≤ finrank F (W (rep t) ⊔ C : Submodule F V) + β := by
    intro t
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (W (rep t)) C
    have h2 : W (rep t) ⊓ C = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : x ∈ K ⊓ C := ⟨hWK _ hx.1, hx.2⟩
      rw [hC.inf_eq_bot] at this
      exact this
    rw [h2, finrank_bot] at h1
    have h3 := hWdim (rep t)
    omega
  choose ψ hψ using fun t => exists_map (W (rep t) ⊔ C) β (hdimS t)
  have hkerψ : ∀ t, LinearMap.ker (ψ t) ⊓ K ≤ W (rep t) := by
    intro t
    calc LinearMap.ker (ψ t) ⊓ K ≤ (W (rep t) ⊔ C) ⊓ K := inf_le_inf_right K (hψ t)
      _ = W (rep t) ⊔ C ⊓ K := sup_inf_assoc_of_le C (hWK _)
      _ = W (rep t) := by rw [inf_comm, hC.inf_eq_bot, sup_bot_eq]
  let o : (Fin α → F) → (Fin β → F) → F := fun t s =>
    if h : ∃ v, φ v = t ∧ ψ t v = s then f (Classical.choose h) else 0
  refine ⟨φ, ψ, o, ?_⟩
  intro v
  have h : ∃ v', φ v' = φ v ∧ ψ (φ v) v' = ψ (φ v) v := ⟨v, rfl, rfl⟩
  simp only [o, dif_pos h]
  obtain ⟨hs1, hs2⟩ := Classical.choose_spec h
  set vs := Classical.choose h
  set x0 := rep (φ v)
  have hk : v - x0 ∈ K := hφ (by rw [LinearMap.mem_ker, map_sub, hrep, sub_self])
  have hw : vs - v ∈ LinearMap.ker (ψ (φ v)) ⊓ K := by
    refine ⟨LinearMap.mem_ker.2 ?_, ?_⟩
    · rw [map_sub, hs2, sub_self]
    · exact hφ (by rw [LinearMap.mem_ker, map_sub, hs1, sub_self])
  have := hWinv x0 (vs - v) (hkerψ _ hw) (v - x0) hk
  have e1 : x0 + (v - x0) + (vs - v) = vs := by abel
  have e2 : x0 + (v - x0) = v := by abel
  rw [e1, e2] at this
  exact this

theorem sub_plain {α β : ℕ} (h : finrank F V ≤ finrank F (per f) + α + β) : SubProto f α β := by
  obtain ⟨K, h1, _, h3⟩ := exists_between (per f) ⊤ le_top
    (min β (finrank F V - finrank F (per f))) (by
      rw [finrank_top]
      have := Submodule.finrank_le (per f)
      omega)
  refine ⟨K, by omega, fun x0 => ⟨per f, h1, by omega, ?_⟩⟩
  intro w hw k _
  exact hw (x0 + k)

theorem sub_split (hf : Quad f) {s α β : ℕ} (hs : 2 * s + finrank F (rad hf) ≤ finrank F V)
    (hsa : s ≤ α) (hb : 1 ≤ β) (hcost : finrank F V + 1 ≤ α + β + s + finrank F (rad hf)) :
    SubProto f α β := by
  obtain ⟨I, hI1, hI2, hI3⟩ := exists_iso hf s (by omega)
  have hJ := orth_formula hf I hI1
  have hIJ := iso_le_orth hf hI2
  obtain ⟨K, hK1, hK2, hK3⟩ := exists_between I ((bil hf).orthogonal I) hIJ
    (min (β - 1) (finrank F V - finrank F (rad hf) - 2 * s)) (by omega)
  refine ⟨K, by omega, fun x0 => ?_⟩
  let W : Submodule F V :=
    { carrier := {w | w ∈ I ∧ Bf f x0 w + f w + f 0 = 0}, add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨I.add_mem ha hb, ?_⟩
        have h1 := hI2 a ha b hb
        rw [Bf_add_right hf]
        unfold Bf at h1
        grind
      zero_mem' := ⟨I.zero_mem, by rw [Bf_zero_right]; grind⟩
      smul_mem' := by
        rintro c w ⟨hw, hw'⟩
        rcases smul_cases c w with h | h
        · rw [h]; exact ⟨I.zero_mem, by rw [Bf_zero_right]; grind⟩
        · rw [h]; exact ⟨hw, hw'⟩ }
  have hWI : W ≤ I := fun w hw => hw.1
  have hhalf := half_space I W (by
    intro u hu p hp huW hpW
    refine ⟨I.add_mem hu hp, ?_⟩
    have hu1 := one_of_ne_zero (fun h => huW ⟨hu, h⟩)
    have hp1 := one_of_ne_zero (fun h => hpW ⟨hp, h⟩)
    have h1 := hI2 u hu p hp
    rw [Bf_add_right hf]
    unfold Bf at h1
    grind)
  have hWI' : W ⊓ I = W := inf_eq_left.mpr hWI
  rw [hWI'] at hhalf
  refine ⟨W, le_trans hWI hK1, by omega, ?_⟩
  intro w hw k hk
  have h1 := diff_eq hf (x0 + k) w
  have h3 : Bf f w k = 0 := hK2 hk w hw.1
  rw [Bf_add_left hf, Bf_comm k w, h3] at h1
  have h2 := hw.2
  apply eq_of_add_zero
  rw [h1]
  grind

end Block
section Card
variable {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {f : V → F}

theorem log_card_sub (S : Submodule F V) : (Nat.card S).log2 = finrank F S := by
  rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_zmod, Nat.log2_two_pow]

theorem log_rad (hf : Quad f) :
    (Nat.card {u : V // ∀ v, Bf f u v = 0}).log2 = finrank F (rad hf) := by
  rw [← log_card_sub]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun u => (mem_rad hf u).symm))

theorem log_per :
    (Nat.card {u : V // ∀ p, f (p + u) = f p}).log2 = finrank F (per f) := by
  rw [← log_card_sub]
  rfl

end Card

section Prod
variable {r : ℕ} {V : Fin r → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]

def zb (j : ℕ) : Submodule F ((i : Fin r) → V i) :=
  { carrier := {w | ∀ i : Fin r, i.val < j → w i = 0}, add_mem' := by
      intro a b ha hb i hi
      rw [Pi.add_apply, ha i hi, hb i hi, add_zero]
    zero_mem' := by intro i _; rfl
    smul_mem' := by
      intro c w hw i hi
      rw [Pi.smul_apply, hw i hi, smul_zero] }

theorem zb_zero : zb (V := V) 0 = ⊤ :=
  eq_top_iff.2 (fun _ _ i hi => absurd hi (Nat.not_lt_zero _))

theorem zb_top : zb (V := V) r = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  funext i
  exact hw i i.2

def slice (Z : Submodule F ((i : Fin r) → V i)) (j : Fin r) : Submodule F (V j) :=
  (Z ⊓ zb j.val).map (LinearMap.proj j)

theorem mem_slice {Z : Submodule F ((i : Fin r) → V i)} {j : Fin r} {v : V j} :
    v ∈ slice Z j ↔ ∃ w ∈ Z, (∀ i : Fin r, i.val < j.val → w i = 0) ∧ w j = v := by
  constructor
  · rintro ⟨w, ⟨hwZ, hwz⟩, rfl⟩
    exact ⟨w, hwZ, hwz, rfl⟩
  · rintro ⟨w, hwZ, hwz, rfl⟩
    exact ⟨w, ⟨hwZ, hwz⟩, rfl⟩

theorem slice_mono {Z Z' : Submodule F ((i : Fin r) → V i)} (h : Z ≤ Z') (j : Fin r) :
    slice Z j ≤ slice Z' j :=
  Submodule.map_mono (inf_le_inf_right _ h)

def LocalRow (q : ((i : Fin r) → V i) → F) : Prop :=
  ∃ I : Finset (Fin r), I.card ≤ 1 ∧ ∀ x y : (i : Fin r) → V i, (∀ i ∈ I, x i = y i) → q x = q y

open Classical in
noncomputable def scatter {k : ℕ} {ι : Type} (emb : ι ↪ Fin k)
    (val : ι → ((i : Fin r) → V i) →ₗ[F] F) : ((i : Fin r) → V i) →ₗ[F] (Fin k → F) where
  toFun x j := if h : ∃ p, emb p = j then val (Classical.choose h) x else 0
  map_add' x y := by
    funext j
    by_cases h : ∃ p, emb p = j
    · simp only [dif_pos h, map_add, Pi.add_apply]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' c x := by
    funext j
    by_cases h : ∃ p, emb p = j
    · simp only [dif_pos h, map_smul, Pi.smul_apply, RingHom.id_apply]
    · simp only [dif_neg h, Pi.smul_apply, smul_zero, RingHom.id_apply]

theorem scatter_at {k : ℕ} {ι : Type} (emb : ι ↪ Fin k)
    (val : ι → ((i : Fin r) → V i) →ₗ[F] F) (x : (i : Fin r) → V i) (p : ι) :
    scatter emb val x (emb p) = val p x := by
  have h : ∃ p', emb p' = emb p := ⟨p, rfl⟩
  have hp : Classical.choose h = p := emb.injective (Classical.choose_spec h)
  simp only [scatter, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h, hp]

theorem scatter_local {k : ℕ} {ι : Type} (emb : ι ↪ Fin k)
    (val : ι → ((i : Fin r) → V i) →ₗ[F] F) (blk : ι → Fin r)
    (hv : ∀ p x y, x (blk p) = y (blk p) → val p x = val p y) (j : Fin k) :
    LocalRow (fun x => scatter emb val x j) := by
  by_cases h : ∃ p, emb p = j
  · refine ⟨{blk (Classical.choose h)}, by simp, fun x y hxy => ?_⟩
    simp only [scatter, LinearMap.coe_mk, AddHom.coe_mk]
    rw [dif_pos h, dif_pos h]
    exact hv _ x y (hxy _ (Finset.mem_singleton_self _))
  · refine ⟨∅, by simp, fun x y _ => ?_⟩
    simp only [scatter, LinearMap.coe_mk, AddHom.coe_mk]
    rw [dif_neg h, dif_neg h]

theorem glue (f : ∀ i, V i → F) (d e : ℕ) (α β : Fin r → ℕ) (hα : ∑ i, α i ≤ d)
    (hβ : ∑ i, β i ≤ e) (hb : ∀ i, BlockProto (f i) (α i) (β i)) :
    ∃ (first : ((i : Fin r) → V i) →ₗ[F] (Fin d → F))
      (second : (Fin d → F) → ((i : Fin r) → V i) →ₗ[F] (Fin e → F))
      (out : (Fin d → F) → (Fin e → F) → (Fin r → F)),
      ((∀ j : Fin d, LocalRow (fun x => first x j)) ∧
        ∀ t : Fin d → F, ∀ j : Fin e, LocalRow (fun x => second t x j)) ∧
      ∀ x : (i : Fin r) → V i, ∀ i : Fin r, out (first x) (second (first x) x) i = f i (x i) := by
  choose φ ψ o ho using hb
  have hc1 : Fintype.card (Σ i, Fin (α i)) ≤ d := by simpa using hα
  have hc2 : Fintype.card (Σ i, Fin (β i)) ≤ e := by simpa using hβ
  let e1 : (Σ i, Fin (α i)) ↪ Fin d := (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb hc1)
  let e2 : (Σ i, Fin (β i)) ↪ Fin e := (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb hc2)
  let tb : (i : Fin r) → (Fin d → F) → (Fin (α i) → F) := fun i t a => t (e1 ⟨i, a⟩)
  let sb : (i : Fin r) → (Fin e → F) → (Fin (β i) → F) := fun i s b => s (e2 ⟨i, b⟩)
  let v1 : (Σ i, Fin (α i)) → ((i : Fin r) → V i) →ₗ[F] F := fun p =>
    (LinearMap.proj p.2).comp ((φ p.1).comp (LinearMap.proj p.1))
  let v2 : (Fin d → F) → (Σ i, Fin (β i)) → ((i : Fin r) → V i) →ₗ[F] F := fun t p =>
    (LinearMap.proj p.2).comp ((ψ p.1 (tb p.1 t)).comp (LinearMap.proj p.1))
  refine ⟨scatter e1 v1, fun t => scatter e2 (v2 t), fun t s i => o i (tb i t) (sb i s),
    ⟨?_, ?_⟩, ?_⟩
  · intro j
    exact scatter_local e1 v1 (fun p => p.1) (fun p x y hxy => by simp [v1, hxy]) j
  · intro t j
    exact scatter_local e2 (v2 t) (fun p => p.1) (fun p x y hxy => by simp [v2, hxy]) j
  · intro x i
    have h1 : tb i (scatter e1 v1 x) = φ i (x i) := by
      funext a
      show scatter e1 v1 x (e1 ⟨i, a⟩) = _
      rw [scatter_at]; rfl
    have h2 : sb i (scatter e2 (v2 (scatter e1 v1 x)) x) =
        ψ i (tb i (scatter e1 v1 x)) (x i) := by
      funext b
      show scatter e2 (v2 (scatter e1 v1 x)) x (e2 ⟨i, b⟩) = _
      rw [scatter_at]; rfl
    show o i (tb i (scatter e1 v1 x)) (sb i (scatter e2 (v2 (scatter e1 v1 x)) x)) = f i (x i)
    rw [h2, h1]
    exact ho i (x i)

variable [∀ i, FiniteDimensional F (V i)]

theorem filt_step (Z : Submodule F ((i : Fin r) → V i)) (j : Fin r) :
    finrank F (Z ⊓ zb j.val : Submodule F _) =
      finrank F (slice Z j) + finrank F (Z ⊓ zb (j.val + 1) : Submodule F _) := by
  set S := Z ⊓ zb (V := V) j.val with hS
  let φ := (LinearMap.proj j : ((i : Fin r) → V i) →ₗ[F] V j).domRestrict S
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : LinearMap.range φ = slice Z j := by
    rw [LinearMap.range_domRestrict]; rfl
  have h3 : (LinearMap.ker φ).map S.subtype = Z ⊓ zb (j.val + 1) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2.1, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact y.2.2 i h
      · have hij : i = j := Fin.ext h
        rw [hij]
        exact hy
    · rintro ⟨hxZ, hx⟩
      exact ⟨⟨x, hxZ, fun i hi => hx i (Nat.lt_succ_of_lt hi)⟩, hx j (Nat.lt_succ_self _), rfl⟩
  have h4 := Submodule.finrank_map_subtype_eq S (LinearMap.ker φ)
  rw [h3] at h4
  rw [h2] at h1
  omega

theorem filt_sum (Z : Submodule F ((i : Fin r) → V i)) :
    finrank F Z = ∑ j : Fin r, finrank F (slice Z j) := by
  have key : ∀ k, k ≤ r → finrank F Z =
      (∑ j : Fin r, if j.val < k then finrank F (slice Z j) else 0) +
        finrank F (Z ⊓ zb k : Submodule F _) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [zb_zero, inf_top_eq]
      simp
    | succ k ih =>
      intro hk
      have hk' : k < r := hk
      rw [ih (le_of_lt hk'), filt_step Z ⟨k, hk'⟩]
      have hsplit : ∀ j : Fin r, (if j.val < k + 1 then finrank F (slice Z j) else 0) =
          (if j.val < k then finrank F (slice Z j) else 0) +
            (if j = ⟨k, hk'⟩ then finrank F (slice Z j) else 0) := by
        intro j
        by_cases h1 : j.val < k
        · have h2 : j.val < k + 1 := by omega
          have h3 : j ≠ ⟨k, hk'⟩ := by intro h; rw [h] at h1; simp at h1
          simp [h1, h2, h3]
        · by_cases h2 : j.val < k + 1
          · have h3 : j = ⟨k, hk'⟩ := Fin.ext (by simp; omega)
            simp [h1, h2, h3]
          · have h3 : j ≠ ⟨k, hk'⟩ := by intro h; rw [h] at h2; simp at h2
            simp [h1, h2, h3]
      rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
  have := key r le_rfl
  rw [zb_top, inf_bot_eq, finrank_bot, add_zero] at this
  rw [this]
  exact Finset.sum_congr rfl (fun j _ => by simp [j.2])

theorem finrank_inf_ker {k : ℕ} (K : Submodule F ((i : Fin r) → V i))
    (L : ((i : Fin r) → V i) →ₗ[F] (Fin k → F)) :
    finrank F K ≤ finrank F (K ⊓ LinearMap.ker L : Submodule F _) + k := by
  let ρ := L.domRestrict K
  have h1 := LinearMap.finrank_range_add_finrank_ker ρ
  have h2 : finrank F (LinearMap.range ρ) ≤ k := by
    have := Submodule.finrank_le (LinearMap.range ρ)
    simpa using this
  have h3 : (LinearMap.ker ρ).map K.subtype = K ⊓ LinearMap.ker L := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxK, hx⟩
      exact ⟨⟨x, hxK⟩, hx, rfl⟩
  have h4 := Submodule.finrank_map_subtype_eq K (LinearMap.ker ρ)
  rw [h3] at h4
  omega

theorem sum_mem_eq (T : Finset (Fin r)) (h : Fin r → ℕ) :
    ∑ i ∈ T, h i = ∑ i, if i ∈ T then h i else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem card_mem_eq (T : Finset (Fin r)) (p : Fin r → Prop) [DecidablePred p] :
    (T.filter p).card = ∑ i, if i ∈ T ∧ p i then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, sum_mem_eq]
  exact Finset.sum_congr rfl (fun i _ => by simp [Finset.mem_filter])

theorem lower_core (f : ∀ i, V i → F) (hf : ∀ i, Quad (f i))
    (K : Submodule F ((i : Fin r) → V i)) (e : ℕ)
    (HW : ∀ x0 : (i : Fin r) → V i, ∃ W : Submodule F ((i : Fin r) → V i), W ≤ K ∧
      finrank F K ≤ finrank F W + e ∧
      ∀ w ∈ W, ∀ k ∈ K, ∀ i, f i (x0 i + k i + w i) = f i (x0 i + k i)) :
    ∃ (T : Finset (Fin r)) (S : ℕ), T.card ≤ e ∧
      S + finrank F K ≤ finrank F ((i : Fin r) → V i) ∧
      S ≤ ∑ i ∈ T, (finrank F (V i) - finrank F (rad (hf i))) / 2 ∧
      ∑ i, (finrank F (V i) - finrank F (per (f i))) +
        (T.filter (fun i => finrank F (per (f i)) = finrank F (rad (hf i)))).card
        ≤ (finrank F ((i : Fin r) → V i) - finrank F K) + e + S := by
  classical
  let U : Submodule F ((i : Fin r) → V i) :=
    { carrier := {w | w ∈ K ∧ ∀ k ∈ K, ∀ i, Bf (f i) (k i) (w i) = 0}, add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨K.add_mem ha hb, fun k hk i => ?_⟩
        rw [Pi.add_apply, Bf_add_right (hf i), ha' k hk i, hb' k hk i, add_zero]
      zero_mem' := ⟨K.zero_mem, fun k _ i => Bf_zero_right _⟩
      smul_mem' := by
        rintro c w ⟨hw, hw'⟩
        refine ⟨K.smul_mem c hw, fun k hk i => ?_⟩
        rw [Pi.smul_apply, Bf_smul_right, hw' k hk i, smul_zero] }
  have hUK : U ≤ K := fun w hw => hw.1
  have hy : ∀ j, ∃ y : V j, ¬ (slice U j ≤ per (f j)) →
      ∃ p ∈ slice U j, Bf (f j) y p + f j p + f j 0 ≠ 0 := by
    intro j
    by_cases h : slice U j ≤ per (f j)
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨p, hpP, hpper⟩ := SetLike.not_le_iff_exists.1 h
      by_cases hq : f j p + f j 0 = 0
      · have hnrad : p ∉ rad (hf j) := fun hr => hpper ((rad_per_iff (hf j) hr).2 hq)
        rw [mem_rad] at hnrad
        obtain ⟨v, hv⟩ := not_forall.1 hnrad
        refine ⟨v, fun _ => ⟨p, hpP, ?_⟩⟩
        rw [add_assoc, hq, add_zero, Bf_comm]
        exact hv
      · exact ⟨0, fun _ => ⟨p, hpP, by rw [Bf_zero_left, zero_add]; exact hq⟩⟩
  choose y hyP using hy
  obtain ⟨W, hWK, hWdim, hWinv⟩ := HW y
  have hW2 : ∀ w ∈ W, ∀ i, Bf (f i) (y i) (w i) + f i (w i) + f i 0 = 0 := by
    intro w hw i
    have h := hWinv w hw 0 K.zero_mem i
    simp only [Pi.zero_apply, add_zero] at h
    have h2 := diff_eq (hf i) (y i) (w i)
    rw [h, F_add_self] at h2
    exact h2.symm
  have hWU : W ≤ U := by
    intro w hw
    refine ⟨hWK hw, fun k hk i => ?_⟩
    have h1 := hWinv w hw k hk i
    have h0 := hWinv w hw 0 K.zero_mem i
    simp only [Pi.zero_apply, add_zero] at h0
    have hq := hf i (y i) (k i) (w i)
    rw [h1, h0] at hq
    rw [← hq]
    grind
  have hsl : ∀ j, slice W j ≤ slice U j := fun j => slice_mono hWU j
  have hA : ∀ j, ¬ (slice U j ≤ per (f j)) →
      finrank F (slice W j) + 1 ≤ finrank F (slice U j) := by
    intro j hj
    obtain ⟨p, hpP, hp⟩ := hyP j hj
    have hpW : p ∉ slice W j := by
      intro hpW
      obtain ⟨w, hwW, _, rfl⟩ := mem_slice.1 hpW
      exact hp (hW2 w hwW j)
    have hlt : slice W j < slice U j := lt_of_le_of_ne (hsl j) (fun heq => hpW (heq ▸ hpP))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hIso : ∀ j, ∀ p ∈ slice U j, ∀ q ∈ slice U j, Bf (f j) p q = 0 := by
    intro j p hp q hq
    obtain ⟨u, huU, _, rfl⟩ := mem_slice.1 hp
    obtain ⟨u', hu'U, _, rfl⟩ := mem_slice.1 hq
    exact hu'U.2 u huU.1 j
  have hσ : ∀ j, 2 * (finrank F (slice U j) - finrank F (slice U j ⊓ rad (hf j) : Submodule F _))
      + finrank F (rad (hf j)) ≤ finrank F (V j) := by
    intro j
    have hQiso : Iso (f j) (slice U j ⊔ rad (hf j)) := by
      intro x hx z hz
      obtain ⟨p, hp, r1, hr1, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨q, hq, r2, hr2, rfl⟩ := Submodule.mem_sup.1 hz
      rw [Bf_add_left (hf j), Bf_add_right (hf j), Bf_add_right (hf j), hIso j p hp q hq,
        Bf_comm p r2, (mem_rad (hf j) r2).1 hr2, (mem_rad (hf j) r1).1 hr1,
        (mem_rad (hf j) r1).1 hr1]
      simp
    have h1 := orth_formula (hf j) (slice U j ⊔ rad (hf j)) le_sup_right
    have h2 := Submodule.finrank_mono (iso_le_orth (hf j) hQiso)
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (slice U j) (rad (hf j))
    have h4 := Submodule.finrank_mono (inf_le_left : slice U j ⊓ rad (hf j) ≤ slice U j)
    omega
  have hnotT : ∀ j, slice U j ≤ per (f j) →
      finrank F (slice U j ⊓ rad (hf j) : Submodule F _) = finrank F (slice U j) := by
    intro j hj
    rw [inf_eq_left.mpr (le_trans hj (per_le_rad (hf j)))]
  let R' : Submodule F ((i : Fin r) → V i) := Submodule.pi Set.univ (fun i => rad (hf i))
  let ΨX : ((i : Fin r) → V i) →ₗ[F] Module.Dual F ((i : Fin r) → V i) :=
    LinearMap.mk₂ F (fun w x => ∑ i, Bf (f i) (x i) (w i))
      (fun w w' x => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, Bf_add_right (hf i)]))
      (fun c w x => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [Pi.smul_apply, Bf_smul_right]))
      (fun w x x' => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, Bf_add_left (hf i)]))
      (fun c w x => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun i _ => by
          rw [Pi.smul_apply, Bf_comm, Bf_smul_right, Bf_comm]))
  let Ψ := ΨX.domRestrict U
  have hrange : LinearMap.range Ψ ≤ K.dualAnnihilator := by
    rintro _ ⟨u, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro k hk
    exact (Finset.sum_eq_zero (fun i _ => u.2.2 k hk i) :
      ∑ i, Bf (f i) (k i) ((u : (i : Fin r) → V i) i) = 0)
  have hker : (LinearMap.ker Ψ).map U.subtype ≤ U ⊓ R' := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u.2, ?_⟩
    show (u : (i : Fin r) → V i) ∈ R'
    rw [Submodule.mem_pi]
    intro i _
    rw [mem_rad]
    intro v
    have h1 := LinearMap.congr_fun (LinearMap.mem_ker.1 hu) (Pi.single i v)
    have h2 : (Ψ u) (Pi.single i v) = Bf (f i) v ((u : (i : Fin r) → V i) i) := by
      show ∑ i', Bf (f i') ((Pi.single i v : (i : Fin r) → V i) i') ((u : (i : Fin r) → V i) i') = _
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, Bf_zero_left]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [h2] at h1
    rw [Bf_comm]
    exact h1
  have hΨ1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have hΨ2 := Subspace.finrank_add_finrank_dualAnnihilator_eq K
  have hΨ3 := Submodule.finrank_mono hrange
  have hΨ4 := Submodule.finrank_mono hker
  have hΨ5 := Submodule.finrank_map_subtype_eq U (LinearMap.ker Ψ)
  have hslR : ∀ j, slice (U ⊓ R') j ≤ slice U j ⊓ rad (hf j) := by
    intro j v hv
    obtain ⟨w, ⟨hwU, hwR⟩, hz, rfl⟩ := mem_slice.1 hv
    exact ⟨mem_slice.2 ⟨w, hwU, hz, rfl⟩, hwR j (Set.mem_univ _)⟩
  have sW := filt_sum W
  have sU := filt_sum U
  have sUR := filt_sum (U ⊓ R')
  have sX : finrank F ((i : Fin r) → V i) = ∑ i, finrank F (V i) := Module.finrank_pi_fintype F
  have hKX := Submodule.finrank_le K
  have hUKd := Submodule.finrank_mono hUK
  obtain ⟨nW, hnW⟩ : ∃ h : Fin r → ℕ, ∀ j, h j = finrank F (slice W j) := ⟨_, fun _ => rfl⟩
  obtain ⟨nP, hnP⟩ : ∃ h : Fin r → ℕ, ∀ j, h j = finrank F (slice U j) := ⟨_, fun _ => rfl⟩
  obtain ⟨nR, hnR⟩ : ∃ h : Fin r → ℕ, ∀ j,
      h j = finrank F (slice U j ⊓ rad (hf j) : Submodule F _) := ⟨_, fun _ => rfl⟩
  obtain ⟨nUR, hnUR⟩ : ∃ h : Fin r → ℕ, ∀ j, h j = finrank F (slice (U ⊓ R') j) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨nV, hnV⟩ : ∃ h : Fin r → ℕ, ∀ j, h j = finrank F (V j) := ⟨_, fun _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ h : Fin r → ℕ, ∀ j, h j = finrank F (rad (hf j)) := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ h : Fin r → ℕ, ∀ j, h j = finrank F (per (f j)) := ⟨_, fun _ => rfl⟩
  let q := fun j => ¬ (slice U j ≤ per (f j))
  have fA : ∀ j, q j → nW j + 1 ≤ nP j := fun j hj => by rw [hnW, hnP]; exact hA j hj
  have fWP : ∀ j, nW j ≤ nP j := fun j => by rw [hnW, hnP]; exact Submodule.finrank_mono (hsl j)
  have fURR : ∀ j, nUR j ≤ nR j := fun j => by
    rw [hnUR, hnR]; exact Submodule.finrank_mono (hslR j)
  have fRP : ∀ j, nR j ≤ nP j := fun j => by rw [hnR, hnP]; exact Submodule.finrank_mono inf_le_left
  have fRa : ∀ j, nR j ≤ a j := fun j => by rw [hnR, ha]; exact Submodule.finrank_mono inf_le_right
  have fga : ∀ j, g j ≤ a j := fun j => by
    rw [hg, ha]; exact Submodule.finrank_mono (per_le_rad (hf j))
  have fag : ∀ j, a j ≤ g j + 1 := fun j => by rw [hg, ha]; exact rad_le_per (hf j)
  have fgV : ∀ j, g j ≤ nV j := fun j => by rw [hg, hnV]; exact Submodule.finrank_le _
  have fσ : ∀ j, 2 * (nP j - nR j) + a j ≤ nV j := fun j => by
    rw [hnP, hnR, ha, hnV]; exact hσ j
  have fWg : ∀ j, ¬ q j → nW j ≤ g j := fun j hj => by
    rw [hnW, hg]
    exact le_trans (Submodule.finrank_mono (hsl j)) (Submodule.finrank_mono (not_not.1 hj))
  have fRPeq : ∀ j, ¬ q j → nR j = nP j := fun j hj => by
    rw [hnR, hnP]; exact hnotT j (not_not.1 hj)
  have sW' : finrank F W = ∑ j, nW j := by
    rw [sW]; exact Finset.sum_congr rfl (fun j _ => (hnW j).symm)
  have sU' : finrank F U = ∑ j, nP j := by
    rw [sU]; exact Finset.sum_congr rfl (fun j _ => (hnP j).symm)
  have sUR' : finrank F (U ⊓ R' : Submodule F _) = ∑ j, nUR j := by
    rw [sUR]; exact Finset.sum_congr rfl (fun j _ => (hnUR j).symm)
  have sX' : finrank F ((i : Fin r) → V i) = ∑ j, nV j := by
    rw [sX]; exact Finset.sum_congr rfl (fun j _ => (hnV j).symm)
  let T := Finset.univ.filter q
  have hTmem : ∀ j, j ∈ T ↔ q j := fun j => by simp [T]
  refine ⟨T, ∑ j, (nP j - nR j), ?_, ?_, ?_, ?_⟩
  · -- T.card ≤ e
    have h1 : ∑ j, (nW j + if j ∈ T then 1 else 0) ≤ ∑ j, nP j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ T
      · rw [if_pos hj]; exact fA j ((hTmem j).1 hj)
      · rw [if_neg hj, add_zero]; exact fWP j
    rw [Finset.sum_add_distrib] at h1
    have h2 : T.card = ∑ j, if j ∈ T then 1 else 0 := by
      rw [Finset.card_eq_sum_ones, sum_mem_eq]
    omega
  · -- S + finrank K ≤ finrank X
    have h1 : ∑ j, ((nP j - nR j) + nUR j) ≤ ∑ j, nP j := by
      apply Finset.sum_le_sum
      intro j _
      have := fURR j; have := fRP j
      omega
    rw [Finset.sum_add_distrib] at h1
    omega
  · -- S ≤ Σ_T m
    have hm : ∀ j, (finrank F (V j) - finrank F (rad (hf j))) / 2 = (nV j - a j) / 2 := by
      intro j; rw [hnV, ha]
    rw [Finset.sum_congr rfl (fun j _ => hm j), sum_mem_eq T]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ T
    · rw [if_pos hj]
      have := fσ j
      omega
    · rw [if_neg hj, fRPeq j (fun h => hj ((hTmem j).2 h))]
      simp
  · -- main inequality
    have h1 : ∑ j, (nW j + if j ∈ T ∧ g j = a j then 1 else 0) ≤
        ∑ j, (g j + (nP j - nR j)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ T
      · have hA' := fA j ((hTmem j).1 hj)
        have := fRa j; have := fRP j; have := fag j; have := fga j
        by_cases hga : g j = a j
        · rw [if_pos ⟨hj, hga⟩]
          omega
        · rw [if_neg (fun h => hga h.2)]
          omega
      · rw [if_neg (fun h => hj h.1)]
        have := fWg j (fun h => hj ((hTmem j).2 h))
        omega
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h1
    have h2 : (T.filter (fun i => finrank F (per (f i)) = finrank F (rad (hf i)))).card =
        ∑ j, if j ∈ T ∧ g j = a j then 1 else 0 := by
      rw [card_mem_eq T]
      exact Finset.sum_congr rfl (fun j _ => by rw [hg, ha])
    have h3 : ∑ j, (nV j - g j) + ∑ j, g j = ∑ j, nV j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by have := fgV j; omega)
    have h4 : ∑ i, (finrank F (V i) - finrank F (per (f i))) = ∑ j, (nV j - g j) :=
      Finset.sum_congr rfl (fun j _ => by rw [hnV, hg])
    rw [h2, h4]
    omega

theorem exists_alloc (m : Fin r → ℕ) : ∀ (T : Finset (Fin r)) (c : ℕ), c ≤ ∑ i ∈ T, m i →
    ∃ s : Fin r → ℕ, (∀ i, s i ≤ m i) ∧ (∀ i, i ∉ T → s i = 0) ∧ ∑ i, s i = c := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro c hc
    simp at hc
    exact ⟨fun _ => 0, fun _ => Nat.zero_le _, fun _ _ => rfl, by simp [hc]⟩
  | @insert a T ha ih =>
    intro c hc
    rw [Finset.sum_insert ha] at hc
    obtain ⟨s, h1, h2, h3⟩ := ih (c - min c (m a)) (by omega)
    refine ⟨fun i => s i + if i = a then min c (m a) else 0, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      by_cases hi : i = a
      · rw [if_pos hi, hi, h2 a ha]; simp
      · rw [if_neg hi, add_zero]; exact h1 i
    · intro i hi
      dsimp only
      have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self _ _)
      have hiT : i ∉ T := fun h => hi (Finset.mem_insert_of_mem h)
      rw [if_neg hia, h2 i hiT]
    · rw [Finset.sum_add_distrib, h3, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      omega

theorem exists_split (Fl : Fin r → ℕ) : ∀ (S : Finset (Fin r)) (A B : ℕ),
    ∑ i ∈ S, Fl i ≤ A + B →
    ∃ F1 F2 : Fin r → ℕ, (∀ i, F1 i + F2 i = Fl i) ∧ ∑ i ∈ S, F1 i ≤ A ∧ ∑ i ∈ S, F2 i ≤ B := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro A B _
    exact ⟨Fl, fun _ => 0, fun _ => rfl, by simp, by simp⟩
  | @insert a S ha ih =>
    intro A B h
    rw [Finset.sum_insert ha] at h
    obtain ⟨F1, F2, h1, h2, h3⟩ :=
      ih (A - min (Fl a) A) (B - (Fl a - min (Fl a) A)) (by omega)
    refine ⟨fun i => if i = a then min (Fl a) A else F1 i,
      fun i => if i = a then Fl a - min (Fl a) A else F2 i, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      by_cases hi : i = a
      · rw [if_pos hi, if_pos hi, hi]; omega
      · rw [if_neg hi, if_neg hi]; exact h1 i
    · have e1 : ∑ i ∈ S, (if i = a then min (Fl a) A else F1 i) = ∑ i ∈ S, F1 i :=
        Finset.sum_congr rfl (fun i hi => if_neg (fun h : i = a => ha (h ▸ hi)))
      dsimp only
      rw [Finset.sum_insert ha, if_pos rfl, e1]
      omega
    · have e1 : ∑ i ∈ S, (if i = a then Fl a - min (Fl a) A else F2 i) = ∑ i ∈ S, F2 i :=
        Finset.sum_congr rfl (fun i hi => if_neg (fun h : i = a => ha (h ▸ hi)))
      dsimp only
      rw [Finset.sum_insert ha, if_pos rfl, e1]
      omega

theorem upper_core (f : ∀ i, V i → F) (hf : ∀ i, Quad (f i)) (d e : ℕ) (T : Finset (Fin r))
    (hT : T.card ≤ e)
    (hineq : ∑ i, (finrank F (V i) - finrank F (per (f i))) +
        (T.filter (fun i => finrank F (per (f i)) = finrank F (rad (hf i)))).card
        ≤ d + e + min d (∑ i ∈ T, (finrank F (V i) - finrank F (rad (hf i))) / 2)) :
    ∃ (first : ((i : Fin r) → V i) →ₗ[F] (Fin d → F))
      (second : (Fin d → F) → ((i : Fin r) → V i) →ₗ[F] (Fin e → F))
      (out : (Fin d → F) → (Fin e → F) → (Fin r → F)),
      ((∀ j : Fin d, LocalRow (fun x => first x j)) ∧
        ∀ t : Fin d → F, ∀ j : Fin e, LocalRow (fun x => second t x j)) ∧
      ∀ x : (i : Fin r) → V i, ∀ i : Fin r, out (first x) (second (first x) x) i = f i (x i) := by
  classical
  obtain ⟨n, hn⟩ : ∃ h : Fin r → ℕ, ∀ i, h i = finrank F (V i) := ⟨_, fun _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ h : Fin r → ℕ, ∀ i, h i = finrank F (rad (hf i)) := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ h : Fin r → ℕ, ∀ i, h i = finrank F (per (f i)) := ⟨_, fun _ => rfl⟩
  have hineq' : ∑ i, (n i - g i) + (∑ i, if i ∈ T ∧ g i = a i then 1 else 0)
      ≤ d + e + min d (∑ i ∈ T, (n i - a i) / 2) := by
    have e1 : ∑ i, (n i - g i) = ∑ i, (finrank F (V i) - finrank F (per (f i))) :=
      Finset.sum_congr rfl (fun i _ => by rw [hn, hg])
    have e2 : (∑ i, if i ∈ T ∧ g i = a i then 1 else 0) =
        (T.filter (fun i => finrank F (per (f i)) = finrank F (rad (hf i)))).card := by
      rw [card_mem_eq T]
      exact Finset.sum_congr rfl (fun i _ => by rw [hg, ha])
    have e3 : ∑ i ∈ T, (n i - a i) / 2 =
        ∑ i ∈ T, (finrank F (V i) - finrank F (rad (hf i))) / 2 :=
      Finset.sum_congr rfl (fun i _ => by rw [hn, ha])
    rw [e1, e2, e3]
    exact hineq
  obtain ⟨c, hc⟩ : ∃ c, c = min d (∑ i ∈ T, (n i - a i) / 2) := ⟨_, rfl⟩
  rw [← hc] at hineq'
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_alloc (fun i => (n i - a i) / 2) T c
    (by rw [hc]; exact min_le_right _ _)
  have hcd : c ≤ d := by rw [hc]; exact min_le_left _ _
  have hga : ∀ i, g i ≤ a i := fun i => by
    rw [hg, ha]; exact Submodule.finrank_mono (per_le_rad (hf i))
  have hag : ∀ i, a i ≤ g i + 1 := fun i => by rw [hg, ha]; exact rad_le_per (hf i)
  have han : ∀ i, a i ≤ n i := fun i => by rw [ha, hn]; exact Submodule.finrank_le _
  obtain ⟨L, hL⟩ : ∃ L : Fin r → ℕ, ∀ i, L i = n i - g i + (if i ∈ T ∧ g i = a i then 1 else 0) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Fl, hFldef⟩ : ∃ Fl : Fin r → ℕ, ∀ i,
      Fl i = if i ∈ T then L i - 2 * s i - 1 else n i - g i := ⟨_, fun _ => rfl⟩
  have hFl : ∀ i, Fl i + (2 * s i + if i ∈ T then 1 else 0) = L i := by
    intro i
    have h1 : s i ≤ (n i - a i) / 2 := hs1 i
    have h2 := hga i; have h3 := hag i; have h4 := han i
    rw [hFldef, hL]
    by_cases hi : i ∈ T
    · rw [if_pos hi, if_pos hi]
      by_cases hga' : g i = a i
      · rw [if_pos ⟨hi, hga'⟩]; omega
      · rw [if_neg (fun h => hga' h.2)]; omega
    · rw [if_neg hi, if_neg hi, hs2 i hi, if_neg (fun h => hi h.1)]
  have hsumL : ∑ i, L i = ∑ i, (n i - g i) + ∑ i, (if i ∈ T ∧ g i = a i then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hL i)
  have hsumFl : ∑ i, Fl i + (2 * c + T.card) = ∑ i, L i := by
    have h1 : ∑ i, (2 * s i + if i ∈ T then 1 else 0) = 2 * c + T.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs3, Finset.card_eq_sum_ones, sum_mem_eq T]
    rw [← h1, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hFl i)
  obtain ⟨F1, F2, hF, hF1, hF2⟩ := exists_split Fl Finset.univ (d - c) (e - T.card) (by
    omega)
  obtain ⟨α, hα⟩ : ∃ α : Fin r → ℕ, ∀ i, α i = s i + F1 i := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin r → ℕ, ∀ i, β i = (if i ∈ T then 1 else 0) + F2 i :=
    ⟨_, fun _ => rfl⟩
  have hαs : ∑ i, α i ≤ d := by
    rw [Finset.sum_congr rfl (fun i _ => hα i), Finset.sum_add_distrib, hs3]; omega
  have hβs : ∑ i, β i ≤ e := by
    rw [Finset.sum_congr rfl (fun i _ => hβ i), Finset.sum_add_distrib, ← sum_mem_eq T,
      ← Finset.card_eq_sum_ones]
    omega
  refine glue f d e α β hαs hβs (fun i => block_of_sub ?_)
  have h1 : s i ≤ (n i - a i) / 2 := hs1 i
  have h2 := hga i; have h3 := hag i; have h4 := han i; have h5 := hF i
  have h6 := hFl i
  have h7 := hα i; have h8 := hβ i; have h9 := hFldef i; have h10 := hL i
  by_cases hi : i ∈ T
  · rw [if_pos hi] at h6 h8 h9
    have hsa : s i ≤ α i := by omega
    have hb : 1 ≤ β i := by omega
    refine sub_split (hf i) (s := s i) (by rw [← ha, ← hn]; omega) hsa hb ?_
    rw [← ha, ← hn]
    by_cases hga' : g i = a i
    · rw [if_pos ⟨hi, hga'⟩] at h10
      omega
    · rw [if_neg (fun h => hga' h.2)] at h10
      omega
  · rw [if_neg hi] at h8 h9
    rw [hs2 i hi] at h7
    apply sub_plain
    rw [← hn, ← hg]
    omega

end Prod

theorem main (r : ℕ) (n : Fin r → ℕ) (f : (i : Fin r) → (Fin (n i) → F) → F)
    (hf : ∀ i, Quad (f i)) (a g m : Fin r → ℕ) (N : ℕ)
    (ha : ∀ i, a i = finrank F (rad (hf i))) (hg : ∀ i, g i = finrank F (per (f i)))
    (hm : ∀ i, m i = (n i - a i) / 2) (hN : N = ∑ i, (n i - g i)) (d e : ℕ) (onlyLocal : Bool) :
    (∃ (first : ((i : Fin r) → (Fin (n i) → F)) →ₗ[F] (Fin d → F))
       (second : (Fin d → F) → ((i : Fin r) → (Fin (n i) → F)) →ₗ[F] (Fin e → F))
       (out : (Fin d → F) → (Fin e → F) → (Fin r → F)),
       (onlyLocal = true → (∀ j : Fin d, LocalRow (fun x => first x j)) ∧
         ∀ t : Fin d → F, ∀ j : Fin e, LocalRow (fun x => second t x j)) ∧
       ∀ x : (i : Fin r) → (Fin (n i) → F), ∀ i : Fin r,
         out (first x) (second (first x) x) i = f i (x i)) ↔
    ∃ T : Finset (Fin r), T.card ≤ e ∧
      N + (T.filter (fun i => g i = a i)).card ≤ d + e + min d (∑ i ∈ T, m i) := by
  have hnV : ∀ i, finrank F (Fin (n i) → F) = n i := fun i => Module.finrank_fin_fun F
  have hfil : ∀ T : Finset (Fin r), T.filter (fun i => g i = a i) =
      T.filter (fun i => finrank F (per (f i)) = finrank F (rad (hf i))) :=
    fun T => Finset.filter_congr (fun i _ => by rw [ha, hg])
  have hsm : ∀ T : Finset (Fin r), ∑ i ∈ T, m i =
      ∑ i ∈ T, (finrank F (Fin (n i) → F) - finrank F (rad (hf i))) / 2 :=
    fun T => Finset.sum_congr rfl (fun i _ => by rw [hm, ha, hnV])
  have hN' : N = ∑ i, (finrank F (Fin (n i) → F) - finrank F (per (f i))) := by
    rw [hN]
    exact Finset.sum_congr rfl (fun i _ => by rw [hnV, hg])
  constructor
  · rintro ⟨first, second, out, -, hcor⟩
    let K := LinearMap.ker first
    have hKd : finrank F ((i : Fin r) → (Fin (n i) → F)) - finrank F K ≤ d := by
      have h1 : finrank F (LinearMap.range first) + finrank F K = _ :=
        LinearMap.finrank_range_add_finrank_ker first
      have h2 := Submodule.finrank_le (LinearMap.range first)
      rw [Module.finrank_fin_fun] at h2
      omega
    have HW : ∀ x0 : (i : Fin r) → (Fin (n i) → F), ∃ W : Submodule F _, W ≤ K ∧
        finrank F K ≤ finrank F W + e ∧
        ∀ w ∈ W, ∀ k ∈ K, ∀ i, f i (x0 i + k i + w i) = f i (x0 i + k i) := by
      intro x0
      refine ⟨K ⊓ LinearMap.ker (second (first x0)), inf_le_left,
        finrank_inf_ker K (second (first x0)), ?_⟩
      rintro w ⟨hwK, hwL⟩ k hk i
      have hk' : first k = 0 := hk
      have hwK' : first w = 0 := hwK
      have hwL' : second (first x0) w = 0 := hwL
      have e1 := hcor (x0 + k + w) i
      have e2 := hcor (x0 + k) i
      have h1 : first (x0 + k + w) = first x0 := by rw [map_add, map_add, hk', hwK', add_zero, add_zero]
      have h2 : first (x0 + k) = first x0 := by rw [map_add, hk', add_zero]
      rw [h1, map_add (second (first x0)), hwL', add_zero, ← h2] at e1
      rw [e1] at e2
      exact e2
    obtain ⟨T, S, h1, h2, h3, h4⟩ := lower_core f hf K e HW
    refine ⟨T, h1, ?_⟩
    rw [hfil, hsm, hN']
    omega
  · rintro ⟨T, hT, hineq⟩
    rw [hfil, hsm, hN'] at hineq
    obtain ⟨first, second, out, hloc, hcor⟩ := upper_core f hf d e T hT hineq
    exact ⟨first, second, out, fun _ => hloc, hcor⟩

end PEqualNP.Outside.L_pcx_435_aux

theorem PEqualNP.Outside.L_pcx_435 : ∀ (r : ℕ) (n : Fin r → ℕ),
  let F := ZMod 2
  let V := fun i : Fin r => Fin (n i) → F
  let X := (i : Fin r) → V i
  let Y := Fin r → F
  ∀ (f : (i : Fin r) → V i → F),
    let B := fun (i : Fin r) (u v : V i) => f i (u+v)+f i u+f i v+f i 0
    (∀ (i : Fin r) (p u v : V i),
      f i (p+u+v)+f i (p+u)+f i (p+v)+f i p = B i u v) →
    let a := fun i : Fin r => (Nat.card {u : V i // ∀ v : V i, B i u v = 0}).log2
    let g := fun i : Fin r => (Nat.card {u : V i // ∀ p : V i, f i (p+u) = f i p}).log2
    let m := fun i : Fin r => (n i-a i)/2
    let N := ∑ i : Fin r, (n i-g i)
    let localRow := fun (q : X → F) =>
      ∃ I : Finset (Fin r), I.card ≤ 1 ∧
        ∀ x y : X, (∀ i ∈ I, x i = y i) → q x = q y
    ∀ (d e : ℕ) (onlyLocal : Bool),
      (∃ (first : X →ₗ[F] (Fin d → F))
         (second : (Fin d → F) → X →ₗ[F] (Fin e → F))
         (out : (Fin d → F) → (Fin e → F) → Y),
         (onlyLocal = true →
           (∀ j : Fin d, localRow (fun x => first x j)) ∧
           ∀ t : Fin d → F, ∀ j : Fin e, localRow (fun x => second t x j)) ∧
         ∀ x : X, ∀ i : Fin r, out (first x) (second (first x) x) i = f i (x i)) ↔
      ∃ T : Finset (Fin r), T.card ≤ e ∧
        N + (T.filter (fun i => g i = a i)).card ≤ d+e+min d (∑ i ∈ T, m i) := by
  intro r n F V X Y f B hB a g m N localRow d e onlyLocal
  exact PEqualNP.Outside.L_pcx_435_aux.main r n f hB a g m N
    (fun i => PEqualNP.Outside.L_pcx_435_aux.log_rad (hB i))
    (fun i => PEqualNP.Outside.L_pcx_435_aux.log_per (f := f i))
    (fun _ => rfl) rfl d e onlyLocal
