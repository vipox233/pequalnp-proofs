import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29723


section L807

open PEqualNP.CircuitLowerBounds

abbrev m1_B (w : ℕ) := Fin w → ZMod 2
abbrev m1_W (n : ℕ) := Fin n → ZMod 2
abbrev m1_E (w : ℕ) := m1_B w × ZMod 2 × m1_B w
abbrev m1_V (n w : ℕ) := (m1_W n × m1_B w) × (ZMod 2 × m1_B w)

theorem m1_rn {K V V₂ : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V₂]
    [Module K V₂] [FiniteDimensional K V] (f : V →ₗ[K] V₂) (S : Submodule K V) :
    Module.finrank K ↥(S.map f) + Module.finrank K ↥(S ⊓ LinearMap.ker f) =
      Module.finrank K ↥S := by
  have h := LinearMap.finrank_range_add_finrank_ker (f ∘ₗ S.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at h
  rw [← Submodule.finrank_map_subtype_eq S (Submodule.comap S.subtype (LinearMap.ker f)),
    Submodule.map_comap_subtype] at h
  exact h

theorem m1_inj {K V V₂ : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V₂]
    [Module K V₂] (f : V →ₗ[K] V₂) (hf : Function.Injective f) (S : Submodule K V) :
    Module.finrank K ↥(S.map f) = Module.finrank K ↥S :=
  (Submodule.equivMapOfInjective f hf S).finrank_eq.symm

noncomputable def m1_stepR {w : ℕ} (R : Submodule (ZMod 2) (Fin w → ZMod 2))
    (L : Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))) :
    Submodule (ZMod 2) (Fin w → ZMod 2) :=
  (L ⊓ R.comap (LinearMap.fst (ZMod 2) (m1_B w) (ZMod 2 × m1_B w))).map
    ((LinearMap.snd (ZMod 2) (ZMod 2) (m1_B w)) ∘ₗ
      (LinearMap.snd (ZMod 2) (m1_B w) (ZMod 2 × m1_B w)))

theorem m1_mem_stepR {w : ℕ} {R : Submodule (ZMod 2) (Fin w → ZMod 2)}
    {L : Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))}
    {b' : Fin w → ZMod 2} :
    b' ∈ m1_stepR R L ↔ ∃ b ∈ R, ∃ c : ZMod 2, (b, c, b') ∈ L := by
  unfold m1_stepR
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨⟨b, c, b''⟩, ⟨hL, hR⟩, rfl⟩
    exact ⟨b, hR, c, hL⟩
  · rintro ⟨b, hR, c, hL⟩
    exact ⟨(b, c, b'), ⟨hL, hR⟩, rfl⟩

noncomputable def m1_stepR0 {w : ℕ} (R0 : Submodule (ZMod 2) (Fin w → ZMod 2))
    (L : Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))) :
    Submodule (ZMod 2) (Fin w → ZMod 2) :=
  (L ⊓ R0.comap (LinearMap.fst (ZMod 2) (m1_B w) (ZMod 2 × m1_B w)) ⊓
      LinearMap.ker ((LinearMap.fst (ZMod 2) (ZMod 2) (m1_B w)) ∘ₗ
        (LinearMap.snd (ZMod 2) (m1_B w) (ZMod 2 × m1_B w)))).map
    ((LinearMap.snd (ZMod 2) (ZMod 2) (m1_B w)) ∘ₗ
      (LinearMap.snd (ZMod 2) (m1_B w) (ZMod 2 × m1_B w)))

theorem m1_mem_stepR0 {w : ℕ} {R0 : Submodule (ZMod 2) (Fin w → ZMod 2)}
    {L : Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))}
    {b' : Fin w → ZMod 2} :
    b' ∈ m1_stepR0 R0 L ↔ ∃ b ∈ R0, (b, (0 : ZMod 2), b') ∈ L := by
  unfold m1_stepR0
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨⟨b, c, b''⟩, ⟨⟨hL, hR⟩, hc⟩, rfl⟩
    have hc' : c = 0 := hc
    subst hc'
    exact ⟨b, hR, hL⟩
  · rintro ⟨b, hR, hL⟩
    exact ⟨(b, 0, b'), ⟨⟨hL, hR⟩, rfl⟩, rfl⟩

noncomputable def m1_stepSc {w : ℕ} (R R0 : Submodule (ZMod 2) (Fin w → ZMod 2)) (sc : ℕ)
    (L : Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))) : ℕ :=
  sc + Module.finrank (ZMod 2)
      ↥(L ⊓ R.comap (LinearMap.fst (ZMod 2) (m1_B w) (ZMod 2 × m1_B w)))
    - Module.finrank (ZMod 2) ↥R
    - Module.finrank (ZMod 2)
      ↥(R0 ⊓ L.comap (LinearMap.inl (ZMod 2) (m1_B w) (ZMod 2 × m1_B w)))

noncomputable def m1_phi (n w : ℕ) (t : Fin n) : m1_V n w →ₗ[ZMod 2] (m1_W n × m1_B w) where
  toFun p := (p.1.1 + p.2.1 • Pi.single t 1, p.2.2)
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.snd_add, add_smul]
      abel
    · rfl
  map_smul' c p := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add, smul_eq_mul, mul_smul]
    · rfl

def m1_psi (n w : ℕ) : m1_V n w →ₗ[ZMod 2] m1_E w where
  toFun p := (p.1.2, p.2.1, p.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def m1_S {n w : ℕ} (U : Submodule (ZMod 2) (m1_W n × m1_B w))
    (L : Submodule (ZMod 2) (m1_E w)) : Submodule (ZMod 2) (m1_V n w) :=
  U.comap (LinearMap.fst (ZMod 2) (m1_W n × m1_B w) (ZMod 2 × m1_B w)) ⊓ L.comap (m1_psi n w)

theorem m1_mem_S {n w : ℕ} {U : Submodule (ZMod 2) (m1_W n × m1_B w)}
    {L : Submodule (ZMod 2) (m1_E w)} {p : m1_V n w} :
    p ∈ m1_S U L ↔ p.1 ∈ U ∧ (p.1.2, p.2.1, p.2.2) ∈ L := Iff.rfl

noncomputable def m1_ext {n w : ℕ} (U : Submodule (ZMod 2) (m1_W n × m1_B w))
    (L : Submodule (ZMod 2) (m1_E w)) (t : Fin n) : Submodule (ZMod 2) (m1_W n × m1_B w) :=
  (m1_S U L).map (m1_phi n w t)

theorem m1_mem_ext {n w : ℕ} {U : Submodule (ZMod 2) (m1_W n × m1_B w)}
    {L : Submodule (ZMod 2) (m1_E w)} {t : Fin n} {x' : m1_W n} {b' : m1_B w} :
    (x', b') ∈ m1_ext U L t ↔
      ∃ x b c, (x, b) ∈ U ∧ (b, c, b') ∈ L ∧ x' = x + c • Pi.single t 1 := by
  unfold m1_ext
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨⟨⟨x, b⟩, ⟨c, b''⟩⟩, hS, heq⟩
    rw [m1_mem_S] at hS
    have h1 : x + c • Pi.single t 1 = x' := congrArg Prod.fst heq
    have h2 : b'' = b' := congrArg Prod.snd heq
    subst h2
    exact ⟨x, b, c, hS.1, hS.2, h1.symm⟩
  · rintro ⟨x, b, c, hU, hL, rfl⟩
    exact ⟨((x, b), (c, b')), m1_mem_S.mpr ⟨hU, hL⟩, rfl⟩

theorem m1_single_cancel {n : ℕ} (t : Fin n) (x : m1_W n) (c : ZMod 2) (hx : x t = 0)
    (h : x + c • Pi.single t 1 = 0) : c = 0 ∧ x = 0 := by
  have ht := congrFun h t
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hx, zero_add,
    Pi.zero_apply] at ht
  subst ht
  simpa using h

theorem m1_ext_dim {n w : ℕ} (U : Submodule (ZMod 2) (m1_W n × m1_B w))
    (L : Submodule (ZMod 2) (m1_E w)) (t : Fin n) (hU : ∀ p ∈ U, p.1 t = 0) :
    Module.finrank (ZMod 2) ↥(m1_ext U L t) +
        Module.finrank (ZMod 2) ↥(U.map (LinearMap.snd (ZMod 2) (m1_W n) (m1_B w))) +
        Module.finrank (ZMod 2)
          ↥(U.comap (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w)) ⊓
            L.comap (LinearMap.inl (ZMod 2) (m1_B w) (ZMod 2 × m1_B w))) =
      Module.finrank (ZMod 2) ↥U +
        Module.finrank (ZMod 2)
          ↥(L ⊓ (U.map (LinearMap.snd (ZMod 2) (m1_W n) (m1_B w))).comap
            (LinearMap.fst (ZMod 2) (m1_B w) (ZMod 2 × m1_B w))) := by
  have h1 := m1_rn (m1_phi n w t) (m1_S U L)
  have h2 := m1_rn (m1_psi n w) (m1_S U L)
  have h3 := m1_rn (LinearMap.snd (ZMod 2) (m1_W n) (m1_B w)) U
  have e2 : (m1_S U L).map (m1_psi n w) =
      L ⊓ (U.map (LinearMap.snd (ZMod 2) (m1_W n) (m1_B w))).comap
        (LinearMap.fst (ZMod 2) (m1_B w) (ZMod 2 × m1_B w)) := by
    ext ⟨b, c, b'⟩
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨⟨⟨x, b0⟩, ⟨c0, b0'⟩⟩, hS, heq⟩
      rw [m1_mem_S] at hS
      have heq' : (b0, c0, b0') = (b, c, b') := heq
      rw [heq'] at hS
      have hb : b0 = b := congrArg Prod.fst heq'
      subst hb
      exact ⟨hS.2, Submodule.mem_map.mpr ⟨(x, b0), hS.1, rfl⟩⟩
    · rintro ⟨hL, hR⟩
      obtain ⟨⟨x, b0⟩, hu, hb⟩ := Submodule.mem_map.mp hR
      have hb' : b0 = b := hb
      subst hb'
      exact ⟨((x, b0), (c, b')), m1_mem_S.mpr ⟨hu, hL⟩, rfl⟩
  have e3 : m1_S U L ⊓ LinearMap.ker (m1_phi n w t) =
      (U.comap (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w)) ⊓
        L.comap (LinearMap.inl (ZMod 2) (m1_B w) (ZMod 2 × m1_B w))).map
        ((LinearMap.inl (ZMod 2) (m1_W n × m1_B w) (ZMod 2 × m1_B w)) ∘ₗ
          (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w))) := by
    ext ⟨⟨x, b⟩, ⟨c, b'⟩⟩
    rw [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, m1_mem_S]
    constructor
    · rintro ⟨⟨hu, hL⟩, hphi⟩
      have hx : x + c • Pi.single t 1 = 0 := congrArg Prod.fst hphi
      have hb' : b' = 0 := congrArg Prod.snd hphi
      obtain ⟨hc, hx0⟩ := m1_single_cancel t x c (hU _ hu) hx
      subst hc hx0 hb'
      exact ⟨b, ⟨hu, hL⟩, rfl⟩
    · rintro ⟨b0, ⟨hu, hL⟩, heq⟩
      have heq' : (((0 : m1_W n), b0), ((0 : ZMod 2), (0 : m1_B w))) = ((x, b), (c, b')) := heq
      cases heq'
      exact ⟨⟨hu, hL⟩, by simp [m1_phi]⟩
  have e4 : m1_S U L ⊓ LinearMap.ker (m1_psi n w) =
      (U ⊓ LinearMap.ker (LinearMap.snd (ZMod 2) (m1_W n) (m1_B w))).map
        (LinearMap.inl (ZMod 2) (m1_W n × m1_B w) (ZMod 2 × m1_B w)) := by
    ext ⟨⟨x, b⟩, ⟨c, b'⟩⟩
    rw [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, m1_mem_S]
    constructor
    · rintro ⟨⟨hu, _⟩, hpsi⟩
      have hpsi' : (b, c, b') = ((0 : m1_B w), (0 : ZMod 2), (0 : m1_B w)) := hpsi
      cases hpsi'
      exact ⟨(x, 0), ⟨hu, rfl⟩, rfl⟩
    · rintro ⟨⟨x0, b0⟩, ⟨hu, hk⟩, heq⟩
      have hk' : b0 = 0 := hk
      subst hk'
      have heq' : ((x0, (0 : m1_B w)), ((0 : ZMod 2), (0 : m1_B w))) = ((x, b), (c, b')) := heq
      cases heq'
      exact ⟨⟨hu, L.zero_mem⟩, rfl⟩
  have i3 : Function.Injective ((LinearMap.inl (ZMod 2) (m1_W n × m1_B w) (ZMod 2 × m1_B w)) ∘ₗ
      (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w))) := by
    intro a b hab
    have := congrArg (fun p : m1_V n w => p.1.2) hab
    exact this
  have i4 : Function.Injective (LinearMap.inl (ZMod 2) (m1_W n × m1_B w) (ZMod 2 × m1_B w)) :=
    LinearMap.inl_injective
  rw [e3, m1_inj _ i3] at h1
  rw [e2, e4, m1_inj _ i4] at h2
  unfold m1_ext
  omega

theorem m1_ext_snd {n w : ℕ} (U : Submodule (ZMod 2) (m1_W n × m1_B w))
    (L : Submodule (ZMod 2) (m1_E w)) (t : Fin n) :
    (m1_ext U L t).map (LinearMap.snd (ZMod 2) (m1_W n) (m1_B w)) =
      m1_stepR (U.map (LinearMap.snd (ZMod 2) (m1_W n) (m1_B w))) L := by
  ext b'
  rw [m1_mem_stepR, Submodule.mem_map]
  constructor
  · rintro ⟨⟨x', b''⟩, hmem, heq⟩
    have heq' : b'' = b' := heq
    subst heq'
    obtain ⟨x, b, c, hu, hL, _⟩ := m1_mem_ext.mp hmem
    exact ⟨b, Submodule.mem_map.mpr ⟨(x, b), hu, rfl⟩, c, hL⟩
  · rintro ⟨b, hR, c, hL⟩
    obtain ⟨⟨x, b0⟩, hu, hb⟩ := Submodule.mem_map.mp hR
    have hb' : b0 = b := hb
    subst hb'
    exact ⟨(x + c • Pi.single t 1, b'), m1_mem_ext.mpr ⟨x, b0, c, hu, hL, rfl⟩, rfl⟩

theorem m1_ext_zero {n w : ℕ} (U : Submodule (ZMod 2) (m1_W n × m1_B w))
    (L : Submodule (ZMod 2) (m1_E w)) (t : Fin n) (hU : ∀ p ∈ U, p.1 t = 0) :
    (m1_ext U L t).comap (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w)) =
      m1_stepR0 (U.comap (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w))) L := by
  ext b'
  rw [m1_mem_stepR0, Submodule.mem_comap]
  have hinr : (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w)) b' = ((0 : m1_W n), b') := rfl
  rw [hinr, m1_mem_ext]
  constructor
  · rintro ⟨x, b, c, hu, hL, heq⟩
    obtain ⟨hc, hx0⟩ := m1_single_cancel t x c (hU _ hu) heq.symm
    subst hc hx0
    exact ⟨b, hu, hL⟩
  · rintro ⟨b, hu, hL⟩
    exact ⟨0, b, 0, hu, hL, by simp⟩

noncomputable def m1_U {n w : ℕ} (lam : Fin n → Submodule (ZMod 2) (m1_E w)) :
    ℕ → Submodule (ZMod 2) (m1_W n × m1_B w)
  | 0 => (⊤ : Submodule (ZMod 2) (m1_B w)).map (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w))
  | t + 1 => if h : t < n then m1_ext (m1_U lam t) (lam ⟨t, h⟩) ⟨t, h⟩ else m1_U lam t

noncomputable def m1_state {n w : ℕ}
    (lam : Fin n → Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))) :
    ℕ → Submodule (ZMod 2) (Fin w → ZMod 2) × Submodule (ZMod 2) (Fin w → ZMod 2) × ℕ
  | 0 => (⊤, ⊤, w)
  | t + 1 => if h : t < n then
      (m1_stepR (m1_state lam t).1 (lam ⟨t, h⟩), m1_stepR0 (m1_state lam t).2.1 (lam ⟨t, h⟩),
        m1_stepSc (m1_state lam t).1 (m1_state lam t).2.1 (m1_state lam t).2.2 (lam ⟨t, h⟩))
    else m1_state lam t

theorem m1_state_zero {n w : ℕ}
    (lam : Fin n → Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))) :
    m1_state lam 0 = (⊤, ⊤, w) := rfl

theorem m1_state_succ {n w : ℕ}
    (lam : Fin n → Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2)))
    (t : ℕ) (h : t < n) :
    m1_state lam (t + 1) =
      (m1_stepR (m1_state lam t).1 (lam ⟨t, h⟩), m1_stepR0 (m1_state lam t).2.1 (lam ⟨t, h⟩),
        m1_stepSc (m1_state lam t).1 (m1_state lam t).2.1 (m1_state lam t).2.2 (lam ⟨t, h⟩)) := by
  rw [m1_state]
  simp only [h, ↓reduceDIte]

theorem m1_U_succ {n w : ℕ} (lam : Fin n → Submodule (ZMod 2) (m1_E w)) (t : ℕ) (h : t < n) :
    m1_U lam (t + 1) = m1_ext (m1_U lam t) (lam ⟨t, h⟩) ⟨t, h⟩ := by
  rw [m1_U]
  simp only [h, ↓reduceDIte]

theorem m1_char {n w : ℕ} (lam : Fin n → Submodule (ZMod 2) (m1_E w)) :
    ∀ t : ℕ, t ≤ n → ∀ (x : m1_W n) (b : m1_B w), (x, b) ∈ m1_U lam t ↔
      (∀ t' : Fin n, t ≤ t'.val → x t' = 0) ∧ ∃ y : ℕ → m1_B w, y t = b ∧
        ∀ t' : Fin n, t'.val < t → (y t'.val, x t', y (t'.val + 1)) ∈ lam t' := by
  intro t
  induction t with
  | zero =>
    intro _ x b
    rw [m1_U, Submodule.mem_map]
    constructor
    · rintro ⟨b0, _, heq⟩
      have heq' : ((0 : m1_W n), b0) = (x, b) := heq
      have hx : (0 : m1_W n) = x := congrArg Prod.fst heq'
      subst hx
      exact ⟨fun _ _ => rfl, fun _ => b, rfl, fun t' ht' => absurd ht' (Nat.not_lt_zero _)⟩
    · rintro ⟨hx, _⟩
      have hx0 : x = 0 := funext fun t' => hx t' (Nat.zero_le _)
      subst hx0
      exact ⟨b, Submodule.mem_top, rfl⟩
  | succ t ih =>
    intro ht x' b'
    have hlt : t < n := ht
    rw [m1_U_succ lam t hlt, m1_mem_ext]
    constructor
    · rintro ⟨x, b, c, hu, hL, rfl⟩
      obtain ⟨hz, y, hy, heqs⟩ := (ih (Nat.le_of_lt hlt) x b).mp hu
      refine ⟨?_, Function.update y (t + 1) b', by simp, ?_⟩
      · intro t' ht'
        have hne : t' ≠ ⟨t, hlt⟩ := by
          intro hh
          rw [hh] at ht'
          simp at ht'
        simp [hz t' (by omega), Pi.single_eq_of_ne hne]
      · intro t' ht'
        by_cases hcase : t'.val = t
        · have ht'eq : t' = ⟨t, hlt⟩ := Fin.ext hcase
          subst ht'eq
          have hxt : x ⟨t, hlt⟩ = 0 := hz _ (le_refl _)
          simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
            smul_eq_mul, mul_one, hxt, zero_add]
          rw [Function.update_of_ne (by omega), hy]
          exact hL
        · have hne : t' ≠ ⟨t, hlt⟩ := fun hh => hcase (congrArg Fin.val hh)
          have hlt' : t'.val < t := by omega
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hne, smul_eq_mul, mul_zero, add_zero]
          exact heqs t' hlt'
    · rintro ⟨hz, y, hy, heqs⟩
      refine ⟨Function.update x' ⟨t, hlt⟩ 0, y t, x' ⟨t, hlt⟩, ?_, ?_, ?_⟩
      · rw [ih (Nat.le_of_lt hlt)]
        refine ⟨?_, y, rfl, ?_⟩
        · intro t' ht'
          by_cases hcase : t' = ⟨t, hlt⟩
          · subst hcase
            simp
          · rw [Function.update_of_ne hcase]
            refine hz t' ?_
            have : t'.val ≠ t := fun hh => hcase (Fin.ext hh)
            omega
        · intro t' ht'
          have hne : t' ≠ ⟨t, hlt⟩ := by
            intro hh
            rw [hh] at ht'
            simp at ht'
          rw [Function.update_of_ne hne]
          exact heqs t' (by omega)
      · have := heqs ⟨t, hlt⟩ (Nat.lt_succ_self t)
        rw [hy] at this
        exact this
      · funext t'
        by_cases hcase : t' = ⟨t, hlt⟩
        · subst hcase
          simp
        · simp [Function.update_of_ne hcase, Pi.single_eq_of_ne hcase]

theorem m1_inv {n w : ℕ} (lam : Fin n → Submodule (ZMod 2) (m1_E w)) :
    ∀ t : ℕ, t ≤ n →
      m1_state lam t =
        ((m1_U lam t).map (LinearMap.snd (ZMod 2) (m1_W n) (m1_B w)),
          (m1_U lam t).comap (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w)),
          Module.finrank (ZMod 2) ↥(m1_U lam t)) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [m1_state_zero, m1_U]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext b
      simp only [Submodule.mem_top, Submodule.mem_map, true_and, true_iff]
      exact ⟨(0, b), ⟨b, rfl⟩, rfl⟩
    · ext b
      simp only [Submodule.mem_top, Submodule.mem_comap, Submodule.mem_map, true_and, true_iff]
      exact ⟨b, rfl⟩
    · change w = _
      rw [m1_inj _ LinearMap.inr_injective, finrank_top, Module.finrank_fin_fun]
  | succ t ih =>
    intro ht
    have hlt : t < n := ht
    have hz : ∀ p ∈ m1_U lam t, p.1 (⟨t, hlt⟩ : Fin n) = 0 := by
      rintro ⟨x, b⟩ hp
      exact ((m1_char lam t (Nat.le_of_lt hlt) x b).mp hp).1 ⟨t, hlt⟩ (le_refl _)
    rw [m1_state_succ lam t hlt, ih (Nat.le_of_lt hlt), m1_U_succ lam t hlt]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact (m1_ext_snd _ _ _).symm
    · exact (m1_ext_zero _ _ _ hz).symm
    · have hd := m1_ext_dim (m1_U lam t) (lam ⟨t, hlt⟩) ⟨t, hlt⟩ hz
      change m1_stepSc _ _ _ _ = Module.finrank (ZMod 2) ↥(m1_ext (m1_U lam t) (lam ⟨t, hlt⟩) ⟨t, hlt⟩)
      unfold m1_stepSc
      dsimp only
      rw [← hd]
      have key : ∀ e a b : ℕ, e + a + b - a - b = e := by
        intro e a b
        omega
      exact key _ _ _

noncomputable def m1_poss {n w : ℕ}
    (lam : Fin n → Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  (m1_U lam n).map (LinearMap.fst (ZMod 2) (m1_W n) (m1_B w))

theorem m1_mem_poss {n w : ℕ}
    {lam : Fin n → Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))}
    {x : Fin n → ZMod 2} :
    x ∈ m1_poss lam ↔ ∃ y : Fin (n + 1) → (Fin w → ZMod 2), ∀ t : Fin n,
      (y t.castSucc, x t, y t.succ) ∈ lam t := by
  unfold m1_poss
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨⟨x0, b⟩, hu, heq⟩
    have heq' : x0 = x := heq
    subst heq'
    obtain ⟨_, y, _, heqs⟩ := (m1_char lam n (le_refl _) x0 b).mp hu
    exact ⟨fun i => y i.val, fun t => heqs t t.isLt⟩
  · rintro ⟨y, hy⟩
    refine ⟨(x, y (Fin.last n)), ?_, rfl⟩
    rw [m1_char lam n (le_refl _)]
    refine ⟨fun t' ht' => absurd t'.isLt (by omega),
      fun k => if h : k < n + 1 then y ⟨k, h⟩ else 0, by simp [Fin.last], ?_⟩
    intro t' _
    have h1 : t'.val < n + 1 := by omega
    have h2 : t'.val + 1 < n + 1 := by omega
    simp only [h1, h2, ↓reduceDIte]
    exact hy t'

theorem m1_main {n w : ℕ}
    (lam : Fin n → Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))) :
    Module.finrank (ZMod 2) ↥(m1_poss lam) + Module.finrank (ZMod 2) ↥(m1_state lam n).2.1 =
      (m1_state lam n).2.2 := by
  rw [m1_inv lam n (le_refl _)]
  have h := m1_rn (LinearMap.fst (ZMod 2) (m1_W n) (m1_B w)) (m1_U lam n)
  have e : m1_U lam n ⊓ LinearMap.ker (LinearMap.fst (ZMod 2) (m1_W n) (m1_B w)) =
      ((m1_U lam n).comap (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w))).map
        (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w)) := by
    ext ⟨x, b⟩
    rw [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker]
    constructor
    · rintro ⟨hu, hx⟩
      have hx' : x = 0 := hx
      subst hx'
      exact ⟨b, hu, rfl⟩
    · rintro ⟨b0, hu, heq⟩
      have heq' : ((0 : m1_W n), b0) = (x, b) := heq
      cases heq'
      exact ⟨hu, rfl⟩
  rw [e, m1_inj (LinearMap.inr (ZMod 2) (m1_W n) (m1_B w)) LinearMap.inr_injective] at h
  exact h

theorem m1_sc_le {n w : ℕ}
    (lam : Fin n → Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2)))
    (t : ℕ) (ht : t ≤ n) : (m1_state lam t).2.2 ≤ n + w := by
  rw [m1_inv lam t ht]
  have h := Submodule.finrank_le (m1_U lam t)
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  exact h

def g_first {N : ℕ} (P : Fin N → Bool) (a : Fin N) : Bool :=
  P a && !(((List.finRange N).filter (fun a' => decide (a'.val < a.val))).any P)

def g_reach {N : ℕ} (st : Fin N → Bool) (ed : ℕ → Fin N → Fin N → Bool) : ℕ → Fin N → Bool
  | 0 => st
  | t+1 => fun b => (List.finRange N).any (fun a => g_reach st ed t a && ed t a b)

def g_sel {N : ℕ} (n : ℕ) (st sp : Fin N → Bool) (ed : ℕ → Fin N → Fin N → Bool) :
    ℕ → Fin N → Bool
  | 0 => g_first (fun a => g_reach st ed n a && sp a)
  | k+1 => g_first (fun a => g_reach st ed (n-(k+1)) a &&
      (List.finRange N).any (fun b => ed (n-(k+1)) a b && g_sel n st sp ed k b))

def g_legal {N : ℕ} (n : ℕ) (st sp : Fin N → Bool) (ed : ℕ → Fin N → Fin N → Bool)
    (q : ℕ → Fin N) : Prop :=
  st (q 0) = true ∧ sp (q n) = true ∧ ∀ t < n, ed t (q t) (q (t+1)) = true

def g_ok {N : ℕ} (n : ℕ) (st sp : Fin N → Bool) (ed : ℕ → Fin N → Fin N → Bool) : Bool :=
  (List.finRange N).any (fun a => g_reach st ed n a && sp a)

theorem g_first_eq_true_iff {N : ℕ} (P : Fin N → Bool) (m : Fin N) :
    g_first P m = true ↔ P m = true ∧ ∀ m' : Fin N, m'.val < m.val → P m' = false := by
  unfold g_first
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨hm, hprev⟩
    refine ⟨hm, fun m' hlt => ?_⟩
    cases h : P m'
    · rfl
    · exact absurd h (hprev m' hlt)
  · rintro ⟨hm, hprev⟩
    refine ⟨hm, fun m' hlt => ?_⟩
    rw [hprev m' hlt]
    decide

theorem g_first_unique {N : ℕ} (P : Fin N → Bool) {m1 m2 : Fin N}
    (h1 : g_first P m1 = true) (h2 : g_first P m2 = true) : m1 = m2 := by
  rw [g_first_eq_true_iff] at h1 h2
  ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := h2.2 m1 hlt
    rw [h1.1] at this
    exact Bool.noConfusion this
  · have := h1.2 m2 hgt
    rw [h2.1] at this
    exact Bool.noConfusion this

theorem g_first_exists {N : ℕ} (P : Fin N → Bool) (hex : ∃ m : Fin N, P m = true) :
    ∃ m : Fin N, g_first P m = true := by
  classical
  let s : Finset (Fin N) := Finset.univ.filter (fun m => P m = true)
  have hne : s.Nonempty := by
    rcases hex with ⟨m, hm⟩
    exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩⟩
  let m0 := s.min' hne
  refine ⟨m0, (g_first_eq_true_iff P m0).mpr
    ⟨(Finset.mem_filter.mp (Finset.min'_mem s hne)).2, ?_⟩⟩
  intro m' hlt
  by_contra hne_f
  have ht : P m' = true := by
    cases h : P m'
    · exact absurd h hne_f
    · rfl
  have hmem : m' ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ m', ht⟩
  have hle : m0 ≤ m' := Finset.min'_le s m' hmem
  exact Nat.not_lt.mpr hle hlt

theorem g_first_all_false {N : ℕ} (P : Fin N → Bool) (h : ∀ m : Fin N, P m = false)
    (m : Fin N) : g_first P m = false := by
  unfold g_first
  simp [h m]

theorem g_first_onehot {N : ℕ} (P : Fin N → Bool) (hex : ∃ m : Fin N, P m = true) :
    ∃ a0 : Fin N, P a0 = true ∧ ∀ a, g_first P a = decide (a0 = a) := by
  obtain ⟨a0, h0⟩ := g_first_exists P hex
  refine ⟨a0, ((g_first_eq_true_iff P a0).mp h0).1, fun a => ?_⟩
  by_cases h : a0 = a
  · subst h
    simp [h0]
  · have : g_first P a = false := by
      cases hc : g_first P a
      · rfl
      · exact absurd (g_first_unique P h0 hc) h
    simp [this, h]

theorem g_reach_iff {N : ℕ} (st : Fin N → Bool) (ed : ℕ → Fin N → Fin N → Bool) (t : ℕ)
    (a : Fin N) :
    g_reach st ed t a = true ↔
      ∃ q : ℕ → Fin N, st (q 0) = true ∧ q t = a ∧ ∀ t' < t, ed t' (q t') (q (t'+1)) = true := by
  induction t generalizing a with
  | zero =>
    constructor
    · intro h
      exact ⟨fun _ => a, h, rfl, fun t' ht' => absurd ht' (Nat.not_lt_zero t')⟩
    · rintro ⟨q, h0, hq, _⟩
      rw [← hq]
      exact h0
  | succ t ih =>
    constructor
    · intro h
      simp only [g_reach, List.any_eq_true, List.mem_finRange, true_and,
        Bool.and_eq_true] at h
      obtain ⟨a', hr, he⟩ := h
      obtain ⟨q, h0, hq, hedges⟩ := (ih a').mp hr
      refine ⟨fun i => if i = t + 1 then a else q i, ?_, ?_, ?_⟩
      · simpa using h0
      · simp
      · intro t' ht'
        by_cases hEq : t' = t
        · subst hEq
          simpa [hq] using he
        · have hlt : t' < t := by omega
          have h1 : t' ≠ t + 1 := by omega
          simpa [h1, hEq] using hedges t' hlt
    · rintro ⟨q, h0, hq, hedges⟩
      simp only [g_reach, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true]
      refine ⟨q t, (ih (q t)).mpr ⟨q, h0, rfl, fun t' ht' => hedges t' (by omega)⟩, ?_⟩
      rw [← hq]
      exact hedges t (by omega)

theorem g_ok_iff {N : ℕ} (n : ℕ) (st sp : Fin N → Bool) (ed : ℕ → Fin N → Fin N → Bool) :
    g_ok n st sp ed = true ↔ ∃ q, g_legal n st sp ed q := by
  unfold g_ok g_legal
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true]
  constructor
  · rintro ⟨a, hr, hs⟩
    obtain ⟨q, h0, hq, hedges⟩ := (g_reach_iff st ed n a).mp hr
    exact ⟨q, h0, by rw [hq]; exact hs, hedges⟩
  · rintro ⟨q, h0, hs, hedges⟩
    exact ⟨q n, (g_reach_iff st ed n (q n)).mpr ⟨q, h0, rfl, hedges⟩, hs⟩

theorem g_sel_aux {N : ℕ} (n : ℕ) (st sp : Fin N → Bool) (ed : ℕ → Fin N → Fin N → Bool)
    (hex : ∃ q, g_legal n st sp ed q) (k : ℕ) (hk : k ≤ n) :
    ∃ q : ℕ → Fin N, sp (q n) = true ∧
      (∀ t, n - k ≤ t → t ≤ n →
        (∀ a, g_sel n st sp ed (n - t) a = decide (q t = a)) ∧ g_reach st ed t (q t) = true) ∧
      ∀ t, n - k ≤ t → t < n → ed t (q t) (q (t+1)) = true := by
  induction k with
  | zero =>
    obtain ⟨q0, h0, hs, hedges⟩ := hex
    have hP : ∃ a : Fin N, (fun a => g_reach st ed n a && sp a) a = true :=
      ⟨q0 n, by
        simp only [Bool.and_eq_true]
        exact ⟨(g_reach_iff st ed n (q0 n)).mpr ⟨q0, h0, rfl, hedges⟩, hs⟩⟩
    obtain ⟨a0, ha0, hone⟩ := g_first_onehot _ hP
    simp only [Bool.and_eq_true] at ha0
    refine ⟨fun _ => a0, ha0.2, ?_, ?_⟩
    · intro t h1 h2
      have ht : t = n := by omega
      subst ht
      refine ⟨fun a => ?_, ha0.1⟩
      rw [Nat.sub_self]
      exact hone a
    · intro t h1 h2
      omega
  | succ k ih =>
    obtain ⟨q, hs, hsel, hedges⟩ := ih (by omega)
    have ht1 : n - (k + 1) + 1 = n - k := by omega
    obtain ⟨hselk, hreach1⟩ := hsel (n - k) le_rfl (Nat.sub_le n k)
    have hkk : n - (n - k) = k := by omega
    rw [hkk] at hselk
    have hreach1' : g_reach st ed (n - (k + 1) + 1) (q (n - k)) = true := by
      rw [ht1]
      exact hreach1
    simp only [g_reach, List.any_eq_true, List.mem_finRange, true_and,
      Bool.and_eq_true] at hreach1'
    obtain ⟨a', hr', he'⟩ := hreach1'
    have hP : ∃ a : Fin N, (fun a => g_reach st ed (n-(k+1)) a &&
        (List.finRange N).any (fun b => ed (n-(k+1)) a b && g_sel n st sp ed k b)) a = true := by
      refine ⟨a', ?_⟩
      simp only [Bool.and_eq_true, List.any_eq_true, List.mem_finRange, true_and]
      exact ⟨hr', q (n - k), he', by rw [hselk]; simp⟩
    obtain ⟨a0, ha0, hone⟩ := g_first_onehot _ hP
    simp only [Bool.and_eq_true, List.any_eq_true, List.mem_finRange, true_and] at ha0
    obtain ⟨hr0, b, heb, hsb⟩ := ha0
    rw [hselk] at hsb
    have hb : q (n - k) = b := by simpa using hsb
    subst hb
    refine ⟨fun i => if i = n - (k + 1) then a0 else q i, ?_, ?_, ?_⟩
    · have : n ≠ n - (k + 1) := by omega
      simpa [this] using hs
    · intro t h1 h2
      by_cases hEq : t = n - (k + 1)
      · subst hEq
        have hkk1 : n - (n - (k + 1)) = k + 1 := by omega
        simp only [ite_true]
        refine ⟨fun a => ?_, hr0⟩
        rw [hkk1]
        exact hone a
      · simp only [hEq, ite_false]
        exact hsel t (by omega) h2
    · intro t h1 h2
      by_cases hEq : t = n - (k + 1)
      · subst hEq
        have h3 : n - (k + 1) + 1 ≠ n - (k + 1) := by omega
        simp only [ite_true, h3, ite_false]
        rw [ht1]
        exact heb
      · have h3 : t + 1 ≠ n - (k + 1) := by omega
        simp only [hEq, h3, ite_false]
        exact hedges t (by omega) h2

theorem g_sel_of_exists {N : ℕ} (n : ℕ) (st sp : Fin N → Bool)
    (ed : ℕ → Fin N → Fin N → Bool) :
    (∃ q, g_legal n st sp ed q) → ∃ q, g_legal n st sp ed q ∧
      ∀ t ≤ n, ∀ a, g_sel n st sp ed (n - t) a = decide (q t = a) := by
  intro hex
  obtain ⟨q, hs, hsel, hedges⟩ := g_sel_aux n st sp ed hex n le_rfl
  refine ⟨q, ⟨?_, hs, fun t ht => hedges t (by omega) ht⟩, fun t ht a =>
    (hsel t (by omega) ht).1 a⟩
  have := (hsel 0 (by omega) (Nat.zero_le n)).2
  simpa [g_reach] using this

theorem g_sel_of_not {N : ℕ} (n : ℕ) (st sp : Fin N → Bool)
    (ed : ℕ → Fin N → Fin N → Bool) :
    (¬ ∃ q, g_legal n st sp ed q) → ∀ k ≤ n, ∀ a, g_sel n st sp ed k a = false := by
  intro hno k
  induction k with
  | zero =>
    intro _ a
    apply g_first_all_false
    intro m
    by_contra hc
    apply hno
    have hm : g_reach st ed n m = true ∧ sp m = true := by
      cases h1 : g_reach st ed n m <;> cases h2 : sp m <;> simp [h1, h2] at hc ⊢
    obtain ⟨q, h0, hq, hedges⟩ := (g_reach_iff st ed n m).mp hm.1
    exact ⟨q, h0, by rw [hq]; exact hm.2, hedges⟩
  | succ k ih =>
    intro hk a
    apply g_first_all_false
    intro m
    have : (List.finRange N).any (fun b => ed (n-(k+1)) m b && g_sel n st sp ed k b) = false := by
      simp only [List.any_eq_false, List.mem_finRange, true_implies]
      intro b
      simp [ih (by omega) b]
    simp [this]

theorem m2_z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem m2_span_aux {n : ℕ} (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (out : Fin n → Fin n → ZMod 2)
    (h1 : ∀ r : Fin n, (∃ x ∈ K, x r = 1 ∧ ∀ t : Fin n, r < t → x t = 0) →
      out r ∈ K ∧ out r r = 1 ∧ ∀ t : Fin n, r < t → out r t = 0)
    (m : ℕ) : ∀ x ∈ K, (∀ t : Fin n, m ≤ t.val → x t = 0) →
      x ∈ Submodule.span (ZMod 2) (Set.range out) := by
  induction m with
  | zero =>
    intro x _ hx0
    have : x = 0 := by
      funext t
      exact hx0 t (Nat.zero_le _)
    rw [this]
    exact Submodule.zero_mem _
  | succ m ih =>
    intro x hx hx0
    by_cases hm : m < n
    · rcases m2_z2 (x ⟨m, hm⟩) with hz | ho
      · apply ih x hx
        intro t ht
        by_cases hEq : t.val = m
        · have : t = ⟨m, hm⟩ := Fin.ext hEq
          rw [this]
          exact hz
        · exact hx0 t (by omega)
      · obtain ⟨hK, hrr, hzero⟩ := h1 ⟨m, hm⟩ ⟨x, hx, ho, fun t ht => hx0 t (by
          have : m < t.val := ht
          omega)⟩
        have hsub : x - out ⟨m, hm⟩ ∈ Submodule.span (ZMod 2) (Set.range out) := by
          apply ih _ (K.sub_mem hx hK)
          intro t ht
          by_cases hEq : t.val = m
          · have : t = ⟨m, hm⟩ := Fin.ext hEq
            rw [this]
            simp [ho, hrr]
          · have hlt : (⟨m, hm⟩ : Fin n) < t := by
              change m < t.val
              omega
            simp [hzero t hlt, hx0 t (by omega)]
        have hout : out ⟨m, hm⟩ ∈ Submodule.span (ZMod 2) (Set.range out) :=
          Submodule.subset_span ⟨_, rfl⟩
        have := Submodule.add_mem _ hsub hout
        simpa using this
    · apply ih x hx
      intro t ht
      exact hx0 t (by omega)

theorem m2_basis {n : ℕ} (K : Submodule (ZMod 2) (Fin n → ZMod 2))
    (out : Fin n → Fin n → ZMod 2) [DecidablePred fun i : Fin n => out i ≠ 0]
    (h1 : ∀ r : Fin n, (∃ x ∈ K, x r = 1 ∧ ∀ t : Fin n, r < t → x t = 0) →
      out r ∈ K ∧ out r r = 1 ∧ ∀ t : Fin n, r < t → out r t = 0)
    (h0 : ∀ r : Fin n, (¬ ∃ x ∈ K, x r = 1 ∧ ∀ t : Fin n, r < t → x t = 0) → out r = 0) :
    Submodule.span (ZMod 2) (Set.range out) = K ∧
    LinearIndependent (ZMod 2)
      (fun i : ↥((Finset.univ : Finset (Fin n)).filter (fun i => out i ≠ 0)) => out i.val) := by
  classical
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      by_cases hex : ∃ x ∈ K, x r = 1 ∧ ∀ t : Fin n, r < t → x t = 0
      · exact (h1 r hex).1
      · rw [h0 r hex]
        exact K.zero_mem
    · intro x hx
      exact m2_span_aux K out h1 n x hx (fun t ht => absurd t.isLt (by omega))
  · have hnz : ∀ i : ↥((Finset.univ : Finset (Fin n)).filter (fun i => out i ≠ 0)),
        out i.val i.val = 1 ∧ ∀ t : Fin n, i.val < t → out i.val t = 0 := by
      intro i
      have hne : out i.val ≠ 0 := (Finset.mem_filter.mp i.property).2
      have hex : ∃ x ∈ K, x i.val = 1 ∧ ∀ t : Fin n, i.val < t → x t = 0 := by
        by_contra hc
        exact hne (h0 i.val hc)
      exact (h1 i.val hex).2
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hcon
    let s : Finset ↥((Finset.univ : Finset (Fin n)).filter (fun i => out i ≠ 0)) :=
      Finset.univ.filter (fun i => g i ≠ 0)
    have hs : s.Nonempty := by
      obtain ⟨i, hi⟩ := not_forall.mp hcon
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    let j := s.max' hs
    have hj : g j ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
    have hmax : ∀ i, g i ≠ 0 → i ≤ j := fun i hi =>
      Finset.le_max' s i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    have hev := congrFun hg j.val
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
    rw [Finset.sum_eq_single j] at hev
    · rw [(hnz j).1, mul_one] at hev
      exact hj hev
    · intro i _ hij
      by_cases hgi : g i = 0
      · simp [hgi]
      · have hle := hmax i hgi
        have hlt : i < j := lt_of_le_of_ne hle hij
        have : out i.val j.val = 0 := (hnz i).2 j.val hlt
        simp [this]
    · intro hnot
      exact absurd (Finset.mem_univ j) hnot

theorem m2_card_sub {n : ℕ} (K : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card {x : Fin n → ZMod 2 // x ∈ K} = 2 ^ Module.finrank (ZMod 2) ↥K := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥K)
  simpa using h

theorem m2_span_surj (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Function.Surjective (fun f : Fin (Module.finrank (ZMod 2) V) → V =>
      Submodule.span (ZMod 2) (Set.range f)) := by
  classical
  intro S
  have hle : Module.finrank (ZMod 2) ↥S ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le S
  let b := Module.finBasis (ZMod 2) ↥S
  refine ⟨fun i => if h : i.val < Module.finrank (ZMod 2) ↥S then ((b ⟨i.val, h⟩ : ↥S) : V)
    else 0, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    dsimp only
    split_ifs with h
    · exact (b ⟨i.val, h⟩).property
    · exact S.zero_mem
  · intro x hx
    have hx' : (⟨x, hx⟩ : ↥S) ∈ Submodule.span (ZMod 2) (Set.range b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    have hmap : S.subtype ⟨x, hx⟩ ∈
        Submodule.map S.subtype (Submodule.span (ZMod 2) (Set.range b)) :=
      Submodule.mem_map_of_mem hx'
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hle⟩, ?_⟩
    simp

theorem m2_count_sub (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card (Submodule (ZMod 2) V) ≤ (Nat.card V) ^ Module.finrank (ZMod 2) V := by
  have h := Nat.card_le_card_of_surjective _ (m2_span_surj V)
  rw [Nat.card_fun] at h
  simpa using h

theorem m2_finite_sub (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (Submodule (ZMod 2) V) := inferInstance

theorem m2_count_B (w : ℕ) :
    Nat.card (Submodule (ZMod 2) (Fin w → ZMod 2)) ≤ 2^(w*w) := by
  have h := m2_count_sub (Fin w → ZMod 2)
  have hc : Nat.card (Fin w → ZMod 2) = 2 ^ w := by
    simp [Nat.card_eq_fintype_card]
  have hf : Module.finrank (ZMod 2) (Fin w → ZMod 2) = w := by simp
  rw [hc, hf, ← pow_mul] at h
  exact h

theorem m2_count_E (w : ℕ) :
    Nat.card (Submodule (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))) ≤
      2^((2*w+1)*(2*w+1)) := by
  have h := m2_count_sub ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
  have hc : Nat.card ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2)) = 2 ^ (2*w+1) := by
    simp [Nat.card_eq_fintype_card]
    ring
  have hf : Module.finrank (ZMod 2) ((Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2)) = 2*w+1 := by
    simp
    ring
  rw [hc, hf, ← pow_mul] at h
  exact h

def b_bits (n s d w : ℕ) (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2)) :
    List Bool :=
  let pack := fun y : Fin w → ZMod 2 => List.ofFn (fun i : Fin w => decide (y i ≠ 0))
  List.ofFn start ++ List.ofFn stop ++
    (List.finRange n).flatMap (fun t => (List.finRange s).flatMap (fun i =>
      (List.finRange s).flatMap (fun j => [edge t i j] ++
        (List.finRange d).flatMap (fun e =>
          let coeff := equation t i j e
          pack coeff.1 ++ [decide (coeff.2.1 ≠ 0)] ++ pack coeff.2.2))))

def b_edgeIx (s d w t i j : ℕ) : ℕ := 2*s + ((t*s+i)*s+j)*(1+d*(2*w+1))

def b_eqBlock {w : ℕ} (c : (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2)) : List Bool :=
  List.ofFn (fun i : Fin w => decide (c.1 i ≠ 0)) ++ [decide (c.2.1 ≠ 0)] ++
    List.ofFn (fun i : Fin w => decide (c.2.2 i ≠ 0))

def b_edgeBlock {n s d w : ℕ} (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (t : Fin n) (i j : Fin s) : List Bool :=
  [edge t i j] ++ (List.finRange d).flatMap (fun e => b_eqBlock (equation t i j e))

theorem b_bits_eq (n s d w : ℕ) (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2)) :
    b_bits n s d w start stop edge equation =
      List.ofFn start ++ List.ofFn stop ++
        (List.finRange n).flatMap (fun t => (List.finRange s).flatMap (fun i =>
          (List.finRange s).flatMap (fun j => b_edgeBlock edge equation t i j))) := rfl

theorem b_flat_len {α : Type} (m k : ℕ) (f : Fin m → List α) (hf : ∀ i, (f i).length = k) :
    ((List.finRange m).flatMap f).length = m * k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map, List.length_append, hf 0]
    have := ih (fun i => f i.succ) (fun i => hf i.succ)
    change k + ((List.finRange m).flatMap (fun i => f i.succ)).length = (m + 1) * k
    rw [this]
    ring

theorem b_flat_getD {α : Type} (m k : ℕ) (f : Fin m → List α) (hf : ∀ i, (f i).length = k)
    (i : Fin m) (j : ℕ) (hj : j < k) (d : α) :
    ((List.finRange m).flatMap f).getD (i.val * k + j) d = (f i).getD j d := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    change (f 0 ++ (List.finRange m).flatMap (fun r => f r.succ)).getD (i.val * k + j) d = _
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.val_zero, zero_mul, zero_add]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [hf 0]; exact hj)]
    · intro i'
      simp only [Fin.val_succ]
      have hidx : (i'.val + 1) * k + j = k + (i'.val * k + j) := by ring
      simp only [List.getD_eq_getElem?_getD]
      rw [hidx, List.getElem?_append_right (by rw [hf 0]; omega), hf 0, Nat.add_sub_cancel_left]
      have := ih (fun r => f r.succ) (fun r => hf r.succ) i'
      simpa only [List.getD_eq_getElem?_getD] using this

theorem b_eqBlock_len {w : ℕ} (c : (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2)) :
    (b_eqBlock c).length = 2*w+1 := by
  simp [b_eqBlock]; omega

theorem b_edgeBlock_len {n s d w : ℕ} (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (t : Fin n) (i j : Fin s) :
    (b_edgeBlock edge equation t i j).length = 1 + d*(2*w+1) := by
  unfold b_edgeBlock
  rw [List.length_append, List.length_singleton,
    b_flat_len d (2*w+1) _ (fun e => b_eqBlock_len _)]

theorem b_length (n s d w : ℕ) (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2)) :
    (b_bits n s d w start stop edge equation).length = 2*s + n*s*s*(1+d*(2*w+1)) := by
  rw [b_bits_eq, List.length_append, List.length_append, List.length_ofFn, List.length_ofFn,
    b_flat_len n (s*(s*(1+d*(2*w+1)))) _ (fun t =>
      b_flat_len s (s*(1+d*(2*w+1))) _ (fun i =>
        b_flat_len s (1+d*(2*w+1)) _ (fun j => b_edgeBlock_len edge equation t i j)))]
  ring

theorem b_mul_add_lt {a m r k : ℕ} (ha : a < m) (hr : r < k) : a * k + r < m * k := by
  have h : (a + 1) * k ≤ m * k := Nat.mul_le_mul_right k ha
  have h2 : (a + 1) * k = a * k + k := by ring
  omega

theorem b_get_start {n s d w : ℕ} (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (i : Fin s) :
    (b_bits n s d w start stop edge equation).getD i.val false = start i := by
  rw [b_bits_eq]
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_left (by simp)]
  simp

theorem b_get_stop {n s d w : ℕ} (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (i : Fin s) :
    (b_bits n s d w start stop edge equation).getD (s + i.val) false = stop i := by
  rw [b_bits_eq]
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simp)]
  simp

theorem b_get_core {n s d w : ℕ} (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (t : Fin n) (i j : Fin s) (r : ℕ) (hr : r < 1 + d*(2*w+1)) :
    (b_bits n s d w start stop edge equation).getD (b_edgeIx s d w t i j + r) false =
      (b_edgeBlock edge equation t i j).getD r false := by
  have h1 := b_flat_getD s (1+d*(2*w+1)) (fun j => b_edgeBlock edge equation t i j)
    (fun j => b_edgeBlock_len edge equation t i j) j r hr false
  have hr2 : j.val * (1+d*(2*w+1)) + r < s * (1+d*(2*w+1)) := b_mul_add_lt j.isLt hr
  have h2 := b_flat_getD s (s*(1+d*(2*w+1)))
    (fun i => (List.finRange s).flatMap (fun j => b_edgeBlock edge equation t i j))
    (fun i => b_flat_len s (1+d*(2*w+1)) _ (fun j => b_edgeBlock_len edge equation t i j))
    i _ hr2 false
  have hr3 : i.val * (s * (1+d*(2*w+1))) + (j.val * (1+d*(2*w+1)) + r) <
      s * (s * (1+d*(2*w+1))) := b_mul_add_lt i.isLt hr2
  have h3 := b_flat_getD n (s*(s*(1+d*(2*w+1))))
    (fun t => (List.finRange s).flatMap (fun i =>
      (List.finRange s).flatMap (fun j => b_edgeBlock edge equation t i j)))
    (fun t => b_flat_len s (s*(1+d*(2*w+1))) _ (fun i =>
      b_flat_len s (1+d*(2*w+1)) _ (fun j => b_edgeBlock_len edge equation t i j)))
    t _ hr3 false
  rw [← h1, ← h2, ← h3, b_bits_eq]
  have hidx : b_edgeIx s d w t i j + r = (List.ofFn start ++ List.ofFn stop).length +
      (t.val * (s * (s * (1+d*(2*w+1)))) +
        (i.val * (s * (1+d*(2*w+1))) + (j.val * (1+d*(2*w+1)) + r))) := by
    simp only [List.length_append, List.length_ofFn, b_edgeIx]
    ring
  rw [hidx]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem b_get_edge {n s d w : ℕ} (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (t : Fin n) (i j : Fin s) :
    (b_bits n s d w start stop edge equation).getD (b_edgeIx s d w t i j) false = edge t i j := by
  have h := b_get_core start stop edge equation t i j 0 (by omega)
  rw [Nat.add_zero] at h
  rw [h]
  simp [b_edgeBlock]

theorem b_get_eq {n s d w : ℕ} (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (t : Fin n) (i j : Fin s) (e : Fin d) (k : ℕ) (hk : k < 2*w+1) :
    (b_bits n s d w start stop edge equation).getD
      (b_edgeIx s d w t i j + 1 + e.val*(2*w+1) + k) false =
      (b_eqBlock (equation t i j e)).getD k false := by
  have hlt : e.val * (2*w+1) + k < d * (2*w+1) := b_mul_add_lt e.isLt hk
  have h := b_get_core start stop edge equation t i j (1 + (e.val*(2*w+1) + k)) (by omega)
  have hidx : b_edgeIx s d w t i j + 1 + e.val*(2*w+1) + k =
      b_edgeIx s d w t i j + (1 + (e.val*(2*w+1) + k)) := by ring
  rw [hidx, h]
  have h1 := b_flat_getD d (2*w+1) (fun e => b_eqBlock (equation t i j e))
    (fun e => b_eqBlock_len _) e k hk false
  rw [← h1]
  unfold b_edgeBlock
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem b_get_left {n s d w : ℕ} (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (t : Fin n) (i j : Fin s) (e : Fin d) (k : Fin w) :
    (b_bits n s d w start stop edge equation).getD
      (b_edgeIx s d w t i j + 1 + e.val*(2*w+1) + k.val) false =
      decide ((equation t i j e).1 k ≠ 0) := by
  rw [b_get_eq start stop edge equation t i j e k.val (by omega)]
  unfold b_eqBlock
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_left (by simp)]
  simp

theorem b_get_mid {n s d w : ℕ} (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (t : Fin n) (i j : Fin s) (e : Fin d) :
    (b_bits n s d w start stop edge equation).getD
      (b_edgeIx s d w t i j + 1 + e.val*(2*w+1) + w) false =
      decide ((equation t i j e).2.1 ≠ 0) := by
  rw [b_get_eq start stop edge equation t i j e w (by omega)]
  unfold b_eqBlock
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem b_get_right {n s d w : ℕ} (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Fin n → Fin s → Fin s → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (t : Fin n) (i j : Fin s) (e : Fin d) (k : Fin w) :
    (b_bits n s d w start stop edge equation).getD
      (b_edgeIx s d w t i j + 1 + e.val*(2*w+1) + w + 1 + k.val) false =
      decide ((equation t i j e).2.2 k ≠ 0) := by
  have hidx : b_edgeIx s d w t i j + 1 + e.val*(2*w+1) + w + 1 + k.val =
      b_edgeIx s d w t i j + 1 + e.val*(2*w+1) + (w + 1 + k.val) := by ring
  rw [hidx, b_get_eq start stop edge equation t i j e (w + 1 + k.val) (by omega)]
  unfold b_eqBlock
  simp only [List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_ofFn]
  rw [show w + 1 + k.val - w = k.val + 1 by omega]
  simp

theorem b_edgeIx_add_lt {n s d w : ℕ} (t : Fin n) (i j : Fin s) (r : ℕ)
    (hr : r < 1 + d*(2*w+1)) :
    b_edgeIx s d w t i j + r < 2*s + n*s*s*(1+d*(2*w+1)) := by
  have h1 : t.val * s + i.val < n * s := b_mul_add_lt t.isLt i.isLt
  have h2 : (t.val * s + i.val) * s + j.val < n * s * s := b_mul_add_lt h1 j.isLt
  have h3 := b_mul_add_lt h2 hr
  unfold b_edgeIx
  omega

theorem b_ix_lt {n s d w : ℕ} (t : Fin n) (i j : Fin s) (e : Fin d) (k : ℕ) (hk : k < 2*w+1) :
    b_edgeIx s d w t i j + 1 + e.val*(2*w+1) + k < 2*s + n*s*s*(1+d*(2*w+1)) := by
  have hlt : e.val * (2*w+1) + k < d * (2*w+1) := b_mul_add_lt e.isLt hk
  have h := b_edgeIx_add_lt (n := n) (s := s) (d := d) (w := w) t i j
    (1 + (e.val*(2*w+1) + k)) (by omega)
  omega

theorem b_edgeIx_lt {n s d w : ℕ} (t : Fin n) (i j : Fin s) :
    b_edgeIx s d w t i j < 2*s + n*s*s*(1+d*(2*w+1)) := by
  have h := b_edgeIx_add_lt (n := n) (s := s) (d := d) (w := w) t i j 0 (by omega)
  omega

theorem b_pow_a (w : ℕ) : 2^(2*w+1) ≤ 2^((w+2)^2) :=
  Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem b_pow_b (w : ℕ) : 2^(w*w) ≤ 2^((w+2)^2) :=
  Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem b_pow_c (w : ℕ) : 2^((2*w+1)*(2*w+1)) ≤ (2^((w+2)^2))^4 := by
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem b_pow_d (w : ℕ) : (2^((w+2)^2))^12 = 2^(12*(w+2)^2) := by
  rw [← pow_mul]
  congr 1
  ring

def Good (inputs : ℕ) (gs : List Gate) : Prop :=
  PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs ⟨gs, 0⟩

def evalWires (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

def wireAt (gs : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (evalWires gs x).getD w false

def Extends (gs1 gs2 : List Gate) : Prop :=
  ∃ extra, gs2 = gs1 ++ extra

lemma extends_refl (gs : List Gate) : Extends gs gs :=
  ⟨[], (List.append_nil gs).symm⟩

lemma extends_trans {gs1 gs2 gs3 : List Gate}
    (h1 : Extends gs1 gs2) (h2 : Extends gs2 gs3) : Extends gs1 gs3 := by
  rcases h1 with ⟨e1, rfl⟩
  rcases h2 with ⟨e2, rfl⟩
  exact ⟨e1 ++ e2, List.append_assoc gs1 e1 e2⟩

lemma extends_length_le {gs1 gs2 : List Gate} (h : Extends gs1 gs2) :
    gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl⟩
  simp

lemma getD_append_lt {α : Type*} (l1 l2 : List α) {i : ℕ} (hi : i < l1.length) (d : α) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_ge {α : Type*} (l1 l2 : List α) {i : ℕ} (hi : l1.length ≤ i) (d : α) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma foldl_wires_append (gs : List Gate) (acc : List Bool) :
    ∃ tail : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc =
        acc ++ tail := by
  induction gs generalizing acc with
  | nil => exact ⟨[], (List.append_nil acc).symm⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rcases ih (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) with ⟨tail, htail⟩
    exact ⟨[g.op.eval (g.inputs.map fun i => acc.getD i false)] ++ tail, by
      rw [htail, List.append_assoc]⟩

lemma foldl_wires_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

lemma evalWires_length (gs : List Gate) (x : List Bool) :
    (evalWires gs x).length = x.length + gs.length :=
  foldl_wires_length gs x

lemma evalWires_append (gs1 gs2 : List Gate) (x : List Bool) :
    evalWires (gs1 ++ gs2) x =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (evalWires gs1 x) := by
  unfold evalWires Circuit.wires
  exact List.foldl_append

lemma evalWires_append_one (gs : List Gate) (g : Gate) (x : List Bool) :
    evalWires (gs ++ [g]) x = evalWires gs x ++ [g.op.eval (g.inputs.map (wireAt gs x))] := by
  rw [evalWires_append]
  rfl

lemma wireAt_extends {gs1 gs2 : List Gate} (hext : Extends gs1 gs2)
    (x : List Bool) {w : ℕ} (hw : w < x.length + gs1.length) :
    wireAt gs2 x w = wireAt gs1 x w := by
  rcases hext with ⟨extra, rfl⟩
  unfold wireAt
  rw [evalWires_append]
  rcases foldl_wires_append extra (evalWires gs1 x) with ⟨tail, htail⟩
  rw [htail, getD_append_lt]
  rw [evalWires_length]
  exact hw

lemma wireAt_append_one_last {inputs : ℕ} (gs : List Gate) (g : Gate)
    {x : List Bool} (hx : x.length = inputs) :
    wireAt (gs ++ [g]) x (inputs + gs.length) = g.op.eval (g.inputs.map (wireAt gs x)) := by
  unfold wireAt
  rw [evalWires_append_one]
  have hlen : (evalWires gs x).length = inputs + gs.length := by
    rw [evalWires_length, hx]
  rw [getD_append_ge _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
  rfl

lemma wireAt_input (gs : List Gate) (x : List Bool) {w : ℕ} (hw : w < x.length) :
    wireAt gs x w = x.getD w false := by
  have h := wireAt_extends (gs1 := []) (gs2 := gs) ⟨gs, rfl⟩ x (by simpa using hw)
  exact h

lemma good_nil (inputs : ℕ) : Good inputs [] := by
  refine ⟨fun g hg => False.elim (List.not_mem_nil hg), fun j hj => False.elim (Nat.not_lt_zero j hj)⟩

lemma good_append_one {inputs : ℕ} {gs : List Gate} (hG : Good inputs gs) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < inputs + gs.length) :
    Good inputs (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hG.1 g' h1
    · rw [List.mem_singleton.mp h2]
      exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    dsimp only at hi
    by_cases hlt : j < gs.length
    · rw [getD_append_lt _ _ hlt] at hi
      exact hG.2 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [getD_append_ge _ _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero] at hi
      exact hback i hi

abbrev CG (α : Type) := List Gate → List Gate × α

def addGate (inputs : ℕ) (g : Gate) : CG ℕ :=
  fun gs => (gs ++ [g], inputs + gs.length)

def mkConst (inputs : ℕ) (c : Bool) : CG ℕ :=
  addGate inputs ⟨if c then GateOp.and else GateOp.or, []⟩

def mkNot (inputs : ℕ) (u : ℕ) : CG ℕ :=
  addGate inputs ⟨GateOp.not, [u]⟩

def mkAnd (inputs : ℕ) (u v : ℕ) : CG ℕ :=
  addGate inputs ⟨GateOp.and, [u, v]⟩

def mkOr (inputs : ℕ) (u v : ℕ) : CG ℕ :=
  addGate inputs ⟨GateOp.or, [u, v]⟩

def mkXor (inputs : ℕ) (u v : ℕ) : CG ℕ := fun gs =>
  let (gs1, o) := mkOr inputs u v gs
  let (gs2, a) := mkAnd inputs u v gs1
  let (gs3, na) := mkNot inputs a gs2
  mkAnd inputs o na gs3

lemma mkConst_spec {inputs : ℕ} (c : Bool) {gs : List Gate} (hG : Good inputs gs) :
    let res := mkConst inputs c gs
    Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = c := by
  have hop : (if c then GateOp.and else GateOp.or) ∈
      ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
    cases c <;> simp
  refine ⟨⟨_, rfl⟩, by simp [mkConst, addGate],
    good_append_one hG _ hop (by simp) (by simp), by simp [mkConst, addGate], fun x hx => ?_⟩
  dsimp only [mkConst, addGate]
  rw [wireAt_append_one_last gs _ hx]
  cases c <;> simp [GateOp.eval]

lemma mkNot_spec {inputs : ℕ} (u : ℕ) {gs : List Gate} (hG : Good inputs gs)
    (hu : u < inputs + gs.length) :
    let res := mkNot inputs u gs
    Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = !(wireAt gs x u) := by
  refine ⟨⟨_, rfl⟩, by simp [mkNot, addGate],
    good_append_one hG _ (by simp) (by simp) (by intro i hi; simp at hi; subst hi; exact hu),
    by simp [mkNot, addGate], fun x hx => ?_⟩
  dsimp only [mkNot, addGate]
  rw [wireAt_append_one_last gs _ hx]
  rfl

lemma mkAnd_spec {inputs : ℕ} (u v : ℕ) {gs : List Gate} (hG : Good inputs gs)
    (hu : u < inputs + gs.length) (hv : v < inputs + gs.length) :
    let res := mkAnd inputs u v gs
    Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = (wireAt gs x u && wireAt gs x v) := by
  refine ⟨⟨_, rfl⟩, by simp [mkAnd, addGate],
    good_append_one hG _ (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    by simp [mkAnd, addGate], fun x hx => ?_⟩
  dsimp only [mkAnd, addGate]
  rw [wireAt_append_one_last gs _ hx]
  simp [GateOp.eval]

lemma mkOr_spec {inputs : ℕ} (u v : ℕ) {gs : List Gate} (hG : Good inputs gs)
    (hu : u < inputs + gs.length) (hv : v < inputs + gs.length) :
    let res := mkOr inputs u v gs
    Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = (wireAt gs x u || wireAt gs x v) := by
  refine ⟨⟨_, rfl⟩, by simp [mkOr, addGate],
    good_append_one hG _ (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    by simp [mkOr, addGate], fun x hx => ?_⟩
  dsimp only [mkOr, addGate]
  rw [wireAt_append_one_last gs _ hx]
  simp [GateOp.eval]

lemma mkXor_spec {inputs : ℕ} (u v : ℕ) {gs : List Gate} (hG : Good inputs gs)
    (hu : u < inputs + gs.length) (hv : v < inputs + gs.length) :
    let res := mkXor inputs u v gs
    Extends gs res.1 ∧ res.1.length = gs.length + 4 ∧ Good inputs res.1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → wireAt res.1 x res.2 = xor (wireAt gs x u) (wireAt gs x v) := by
  rcases h1 : mkOr inputs u v gs with ⟨gs1, o⟩
  have s1 := mkOr_spec u v hG hu hv
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1, wo, ev1⟩
  rcases h2 : mkAnd inputs u v gs1 with ⟨gs2, a⟩
  have s2 := mkAnd_spec u v g1 (by omega) (by omega)
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2, wa, ev2⟩
  rcases h3 : mkNot inputs a gs2 with ⟨gs3, na⟩
  have s3 := mkNot_spec a g2 wa
  simp only [h3] at s3
  rcases s3 with ⟨e3, l3, g3, wna, ev3⟩
  rcases h4 : mkAnd inputs o na gs3 with ⟨gs4, out⟩
  have s4 := mkAnd_spec o na g3 (by omega) wna
  simp only [h4] at s4
  rcases s4 with ⟨e4, l4, g4, wout, ev4⟩
  have hres : mkXor inputs u v gs = (gs4, out) := by
    simp only [mkXor, h1, h2, h3, h4]
  simp only [hres]
  refine ⟨extends_trans e1 (extends_trans e2 (extends_trans e3 e4)), by omega, g4, wout, fun x hx => ?_⟩
  rw [ev4 x hx, wireAt_extends (extends_trans e2 e3) x (by omega), ev1 x hx, ev3 x hx, ev2 x hx,
    wireAt_extends e1 x (by omega), wireAt_extends e1 x (by omega)]
  cases wireAt gs x u <;> cases wireAt gs x v <;> decide

def litVal (v : ℕ → Bool) (l : ℕ × Bool) : Bool := v l.1 == l.2

def dnfVal (v : ℕ → Bool) (ts : List (List (ℕ × Bool))) : Bool :=
  ts.any (fun t => t.all (litVal v))

def xorVal (v : ℕ → Bool) (ws : List ℕ) : Bool :=
  ws.foldr (fun w acc => xor (v w) acc) false

def Sp (I : ℕ) (gs : List Gate) (res : List Gate × ℕ) (c : ℕ) (b : List Bool → Bool) : Prop :=
  Extends gs res.1 ∧ res.1.length ≤ gs.length + c ∧ Good I res.1 ∧ res.2 < I + res.1.length ∧
  ∀ x : List Bool, x.length = I → wireAt res.1 x res.2 = b x

def mkLit (I : ℕ) (l : ℕ × Bool) : CG ℕ :=
  fun gs => if l.2 = true then (gs, l.1) else mkNot I l.1 gs

def mkTerm (I : ℕ) : List (ℕ × Bool) → CG ℕ
  | [], gs => mkConst I true gs
  | l :: ls, gs => mkAnd I (mkLit I l (mkTerm I ls gs).1).2 (mkTerm I ls gs).2
      (mkLit I l (mkTerm I ls gs).1).1

def mkDNF (I : ℕ) : List (List (ℕ × Bool)) → CG ℕ
  | [], gs => mkConst I false gs
  | t :: ts, gs => mkOr I (mkTerm I t (mkDNF I ts gs).1).2 (mkDNF I ts gs).2
      (mkTerm I t (mkDNF I ts gs).1).1

def mkXorL (I : ℕ) : List ℕ → CG ℕ
  | [], gs => mkConst I false gs
  | w :: ws, gs => mkXor I w (mkXorL I ws gs).2 (mkXorL I ws gs).1

def dnfCost : List (List (ℕ × Bool)) → ℕ
  | [] => 1
  | t :: ts => dnfCost ts + 2 * t.length + 2

lemma dnfCost_le (M : ℕ) (ts : List (List (ℕ × Bool))) (h : ∀ t ∈ ts, t.length ≤ M) :
    dnfCost ts ≤ 1 + ts.length * (2 * M + 2) := by
  induction ts with
  | nil => simp [dnfCost]
  | cons t ts ih =>
    have h1 := ih (fun u hu => h u (List.mem_cons_of_mem t hu))
    have h2 := h t List.mem_cons_self
    simp only [dnfCost, List.length_cons]
    nlinarith

lemma all_congr' {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

lemma any_congr' {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

lemma mkLit_spec {I : ℕ} (l : ℕ × Bool) {gs : List Gate} (hG : Good I gs)
    (hl : l.1 < I + gs.length) :
    Sp I gs (mkLit I l gs) 1 (fun x => litVal (wireAt gs x) l) := by
  unfold mkLit
  by_cases h : l.2 = true
  · rw [ite_eq_left h]
    refine ⟨extends_refl gs, Nat.le_add_right _ _, hG, hl, fun x _ => ?_⟩
    simp [litVal, h]
  · rw [ite_eq_right h]
    have s := mkNot_spec l.1 hG hl
    rcases s with ⟨e, len, g, wv, ev⟩
    refine ⟨e, by omega, g, wv, fun x hx => ?_⟩
    rw [ev x hx]
    have h' : l.2 = false := by simpa using h
    simp [litVal, h']

lemma mkTerm_spec {I : ℕ} (t : List (ℕ × Bool)) {gs : List Gate} (hG : Good I gs)
    (ht : ∀ l ∈ t, l.1 < I + gs.length) :
    Sp I gs (mkTerm I t gs) (2 * t.length + 1) (fun x => t.all (litVal (wireAt gs x))) := by
  induction t with
  | nil =>
    have s := mkConst_spec true hG
    rcases s with ⟨e, len, g, wv, ev⟩
    exact ⟨e, by simp [mkTerm]; omega, g, wv, fun x hx => by simpa [mkTerm] using ev x hx⟩
  | cons l ls ih =>
    have s1 := ih (fun u hu => ht u (List.mem_cons_of_mem l hu))
    rcases s1 with ⟨e1, l1, g1, w1, ev1⟩
    have hl : l.1 < I + gs.length := ht l List.mem_cons_self
    have hlen1 := extends_length_le e1
    have s2 := mkLit_spec l g1 (by omega)
    rcases s2 with ⟨e2, l2, g2, w2, ev2⟩
    have hlen2 := extends_length_le e2
    have s3 := mkAnd_spec (mkLit I l (mkTerm I ls gs).1).2 (mkTerm I ls gs).2 g2 w2 (by omega)
    rcases s3 with ⟨e3, l3, g3, w3, ev3⟩
    refine ⟨extends_trans e1 (extends_trans e2 e3), ?_, g3, w3, fun x hx => ?_⟩
    · simp only [mkTerm, List.length_cons]
      omega
    · simp only [mkTerm]
      rw [ev3 x hx, ev2 x hx, wireAt_extends e2 x (by omega), ev1 x hx]
      simp only [List.all_cons]
      congr 1
      unfold litVal
      rw [wireAt_extends e1 x (by omega)]

lemma mkDNF_spec {I : ℕ} (ts : List (List (ℕ × Bool))) {gs : List Gate} (hG : Good I gs)
    (ht : ∀ t ∈ ts, ∀ l ∈ t, l.1 < I + gs.length) :
    Sp I gs (mkDNF I ts gs) (dnfCost ts) (fun x => dnfVal (wireAt gs x) ts) := by
  induction ts with
  | nil =>
    have s := mkConst_spec false hG
    rcases s with ⟨e, len, g, wv, ev⟩
    exact ⟨e, by simp [mkDNF, dnfCost]; omega, g, wv,
      fun x hx => by simpa [mkDNF, dnfVal] using ev x hx⟩
  | cons t ts ih =>
    have s1 := ih (fun u hu => ht u (List.mem_cons_of_mem t hu))
    rcases s1 with ⟨e1, l1, g1, w1, ev1⟩
    have hlen1 := extends_length_le e1
    have s2 := mkTerm_spec t g1 (fun l hl => by
      have := ht t List.mem_cons_self l hl
      omega)
    rcases s2 with ⟨e2, l2, g2, w2, ev2⟩
    have hlen2 := extends_length_le e2
    have s3 := mkOr_spec (mkTerm I t (mkDNF I ts gs).1).2 (mkDNF I ts gs).2 g2 w2 (by omega)
    rcases s3 with ⟨e3, l3, g3, w3, ev3⟩
    refine ⟨extends_trans e1 (extends_trans e2 e3), ?_, g3, w3, fun x hx => ?_⟩
    · simp only [mkDNF, dnfCost]
      omega
    · simp only [mkDNF]
      rw [ev3 x hx, ev2 x hx, wireAt_extends e2 x (by omega), ev1 x hx]
      simp only [dnfVal, List.any_cons]
      congr 1
      apply all_congr'
      intro l hl
      unfold litVal
      rw [wireAt_extends e1 x (by have := ht t List.mem_cons_self l hl; omega)]

lemma mkXorL_spec {I : ℕ} (ws : List ℕ) {gs : List Gate} (hG : Good I gs)
    (hw : ∀ u ∈ ws, u < I + gs.length) :
    Sp I gs (mkXorL I ws gs) (4 * ws.length + 1) (fun x => xorVal (wireAt gs x) ws) := by
  induction ws with
  | nil =>
    have s := mkConst_spec false hG
    rcases s with ⟨e, len, g, wv, ev⟩
    exact ⟨e, by simp [mkXorL]; omega, g, wv,
      fun x hx => by simpa [mkXorL, xorVal] using ev x hx⟩
  | cons u us ih =>
    have s1 := ih (fun a ha => hw a (List.mem_cons_of_mem u ha))
    rcases s1 with ⟨e1, l1, g1, w1, ev1⟩
    have hlen1 := extends_length_le e1
    have hu : u < I + gs.length := hw u List.mem_cons_self
    have s3 := mkXor_spec u (mkXorL I us gs).2 g1 (by omega) w1
    rcases s3 with ⟨e3, l3, g3, w3, ev3⟩
    refine ⟨extends_trans e1 e3, ?_, g3, w3, fun x hx => ?_⟩
    · simp only [mkXorL, List.length_cons]
      omega
    · simp only [mkXorL]
      rw [ev3 x hx, ev1 x hx, wireAt_extends e1 x (by omega)]
      simp [xorVal]

lemma dnfVal_congr (v v' : ℕ → Bool) (ts : List (List (ℕ × Bool))) (L : ℕ)
    (ht : ∀ t ∈ ts, ∀ l ∈ t, l.1 < L) (h : ∀ u < L, v u = v' u) :
    dnfVal v ts = dnfVal v' ts := by
  unfold dnfVal
  apply any_congr'
  intro t htm
  apply all_congr'
  intro l hl
  unfold litVal
  rw [h l.1 (ht t htm l hl)]

lemma xorVal_congr (v v' : ℕ → Bool) (ws : List ℕ) (L : ℕ)
    (hw : ∀ u ∈ ws, u < L) (h : ∀ u < L, v u = v' u) :
    xorVal v ws = xorVal v' ws := by
  induction ws with
  | nil => rfl
  | cons u us ih =>
    have h1 := ih (fun a ha => hw a (List.mem_cons_of_mem u ha))
    simp only [xorVal, List.foldr_cons] at h1 ⊢
    rw [h1, h u (hw u List.mem_cons_self)]

def mkTab : ∀ (m : ℕ), (Fin m → CG ℕ) → CG (Fin m → ℕ)
  | 0, _, gs => (gs, Fin.elim0)
  | m + 1, f, gs =>
    ((f (Fin.last m) (mkTab m (fun i => f i.castSucc) gs).1).1,
      Fin.snoc (α := fun _ => ℕ) (mkTab m (fun i => f i.castSucc) gs).2
        (f (Fin.last m) (mkTab m (fun i => f i.castSucc) gs).1).2)

lemma mkTab_spec {I : ℕ} (c : ℕ) : ∀ (m : ℕ) (g : Fin m → CG ℕ)
    (f : Fin m → (ℕ → Bool) → Bool) (gs : List Gate), Good I gs →
    (∀ i gs1, Good I gs1 → Extends gs gs1 →
      Sp I gs1 (g i gs1) c (fun x => f i (wireAt gs1 x))) →
    (∀ i (v v' : ℕ → Bool), (∀ u < I + gs.length, v u = v' u) → f i v = f i v') →
    Extends gs (mkTab m g gs).1 ∧ (mkTab m g gs).1.length ≤ gs.length + m * c ∧
    Good I (mkTab m g gs).1 ∧ (∀ i, (mkTab m g gs).2 i < I + (mkTab m g gs).1.length) ∧
    ∀ gs', Extends (mkTab m g gs).1 gs' → ∀ x : List Bool, x.length = I → ∀ i,
      wireAt gs' x ((mkTab m g gs).2 i) = f i (wireAt gs' x) := by
  intro m
  induction m with
  | zero =>
    intro g f gs hG _ _
    exact ⟨extends_refl gs, by simp [mkTab], hG, fun i => i.elim0, fun _ _ _ _ i => i.elim0⟩
  | succ m ih =>
    intro g f gs hG hg hloc
    have s1 := ih (fun i => g i.castSucc) (fun i => f i.castSucc) gs hG
      (fun i gs1 h1 h2 => hg i.castSucc gs1 h1 h2) (fun i v v' h => hloc i.castSucc v v' h)
    rcases s1 with ⟨e1, l1, g1, w1, ev1⟩
    have s2 := hg (Fin.last m) _ g1 e1
    rcases s2 with ⟨e2, l2, g2, w2, ev2⟩
    have hlen1 := extends_length_le e1
    have hlen2 := extends_length_le e2
    refine ⟨extends_trans e1 e2, ?_, g2, ?_, ?_⟩
    · simp only [mkTab]
      have : (m + 1) * c = m * c + c := by ring
      omega
    · intro i
      simp only [mkTab]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using w2
      · simp only [Fin.snoc_castSucc]
        have := w1 j
        omega
    · intro gs' he x hx i
      simp only [mkTab] at he ⊢
      have hlen3 := extends_length_le he
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        rw [wireAt_extends he x (by omega), ev2 x hx]
        apply hloc
        intro u hu
        rw [wireAt_extends (extends_trans e2 he) x (by omega)]
      · simp only [Fin.snoc_castSucc]
        exact ev1 gs' (extends_trans e2 he) x hx j

noncomputable def mkTabF (ι : Type) [Finite ι] (g : ι → CG ℕ) : CG (ι → ℕ) :=
  fun gs => ((mkTab (Nat.card ι) (fun k => g ((Finite.equivFin ι).symm k)) gs).1,
    fun i => (mkTab (Nat.card ι) (fun k => g ((Finite.equivFin ι).symm k)) gs).2
      (Finite.equivFin ι i))

lemma mkTabF_spec {I : ℕ} (c : ℕ) (ι : Type) [Finite ι] (g : ι → CG ℕ)
    (f : ι → (ℕ → Bool) → Bool) (gs : List Gate) (hG : Good I gs)
    (hg : ∀ i gs1, Good I gs1 → Extends gs gs1 →
      Sp I gs1 (g i gs1) c (fun x => f i (wireAt gs1 x)))
    (hloc : ∀ i (v v' : ℕ → Bool), (∀ u < I + gs.length, v u = v' u) → f i v = f i v') :
    Extends gs (mkTabF ι g gs).1 ∧ (mkTabF ι g gs).1.length ≤ gs.length + Nat.card ι * c ∧
    Good I (mkTabF ι g gs).1 ∧ (∀ i, (mkTabF ι g gs).2 i < I + (mkTabF ι g gs).1.length) ∧
    ∀ gs', Extends (mkTabF ι g gs).1 gs' → ∀ x : List Bool, x.length = I → ∀ i,
      wireAt gs' x ((mkTabF ι g gs).2 i) = f i (wireAt gs' x) := by
  have s := mkTab_spec (I := I) c (Nat.card ι) (fun k => g ((Finite.equivFin ι).symm k))
    (fun k => f ((Finite.equivFin ι).symm k)) gs hG
    (fun k gs1 h1 h2 => hg _ gs1 h1 h2) (fun k v v' h => hloc _ v v' h)
  rcases s with ⟨e1, l1, g1, w1, ev1⟩
  refine ⟨e1, l1, g1, fun i => w1 _, fun gs' he x hx i => ?_⟩
  have := ev1 gs' he x hx (Finite.equivFin ι i)
  simpa [mkTabF] using this

noncomputable def mkDnfTab (I : ℕ) (ι : Type) [Finite ι] (terms : ι → List (List (ℕ × Bool))) :
    CG (ι → ℕ) :=
  mkTabF ι (fun i => mkDNF I (terms i))

noncomputable def mkXorTab (I : ℕ) (ι : Type) [Finite ι] (ws : ι → List ℕ) : CG (ι → ℕ) :=
  mkTabF ι (fun i => mkXorL I (ws i))

lemma mkDnfTab_spec {I : ℕ} (c : ℕ) (ι : Type) [Finite ι] (terms : ι → List (List (ℕ × Bool)))
    (gs : List Gate) (hG : Good I gs)
    (hw : ∀ i, ∀ t ∈ terms i, ∀ l ∈ t, l.1 < I + gs.length)
    (hc : ∀ i, dnfCost (terms i) ≤ c) :
    Extends gs (mkDnfTab I ι terms gs).1 ∧
    (mkDnfTab I ι terms gs).1.length ≤ gs.length + Nat.card ι * c ∧
    Good I (mkDnfTab I ι terms gs).1 ∧
    (∀ i, (mkDnfTab I ι terms gs).2 i < I + (mkDnfTab I ι terms gs).1.length) ∧
    ∀ gs', Extends (mkDnfTab I ι terms gs).1 gs' → ∀ x : List Bool, x.length = I → ∀ i,
      wireAt gs' x ((mkDnfTab I ι terms gs).2 i) = dnfVal (wireAt gs' x) (terms i) := by
  refine mkTabF_spec c ι _ (fun i v => dnfVal v (terms i)) gs hG (fun i gs1 h1 h2 => ?_)
    (fun i v v' h => dnfVal_congr v v' (terms i) _ (hw i) h)
  have hlen := extends_length_le h2
  have s := mkDNF_spec (terms i) h1 (fun t ht l hl => by have := hw i t ht l hl; omega)
  rcases s with ⟨e, len, g, wv, ev⟩
  exact ⟨e, by have := hc i; omega, g, wv, ev⟩

lemma mkXorTab_spec {I : ℕ} (c : ℕ) (ι : Type) [Finite ι] (ws : ι → List ℕ)
    (gs : List Gate) (hG : Good I gs)
    (hw : ∀ i, ∀ u ∈ ws i, u < I + gs.length)
    (hc : ∀ i, 4 * (ws i).length + 1 ≤ c) :
    Extends gs (mkXorTab I ι ws gs).1 ∧
    (mkXorTab I ι ws gs).1.length ≤ gs.length + Nat.card ι * c ∧
    Good I (mkXorTab I ι ws gs).1 ∧
    (∀ i, (mkXorTab I ι ws gs).2 i < I + (mkXorTab I ι ws gs).1.length) ∧
    ∀ gs', Extends (mkXorTab I ι ws gs).1 gs' → ∀ x : List Bool, x.length = I → ∀ i,
      wireAt gs' x ((mkXorTab I ι ws gs).2 i) = xorVal (wireAt gs' x) (ws i) := by
  refine mkTabF_spec c ι _ (fun i v => xorVal v (ws i)) gs hG (fun i gs1 h1 h2 => ?_)
    (fun i v v' h => xorVal_congr v v' (ws i) _ (hw i) h)
  have hlen := extends_length_le h2
  have s := mkXorL_spec (ws i) h1 (fun u hu => by have := hw i u hu; omega)
  rcases s with ⟨e, len, g, wv, ev⟩
  exact ⟨e, by have := hc i; omega, g, wv, ev⟩

open Classical

abbrev BV (w : ℕ) := Fin w → ZMod 2
abbrev EV (w : ℕ) := BV w × ZMod 2 × BV w
abbrev SubB (w : ℕ) := Submodule (ZMod 2) (BV w)
abbrev SubE (w : ℕ) := Submodule (ZMod 2) (EV w)
abbrev Node (n s w : ℕ) := Fin s × SubB w × SubB w × Fin (n + w + 1)
abbrev Eqn (n s d w : ℕ) := Fin n → Fin s → Fin s → Fin d → EV w
abbrev GOut (N : ℕ) := ℕ × (ℕ → Fin N → ℕ) × (ℕ → Fin N → ℕ)

noncomputable def enumF (ι : Type) [Finite ι] : List ι :=
  (List.finRange (Nat.card ι)).map (Finite.equivFin ι).symm

lemma mem_enumF (ι : Type) [Finite ι] (a : ι) : a ∈ enumF ι := by
  unfold enumF
  exact List.mem_map.mpr ⟨Finite.equivFin ι a, List.mem_finRange _, by simp⟩

lemma length_enumF (ι : Type) [Finite ι] : (enumF ι).length = Nat.card ι := by
  simp [enumF]

def mkFam {α : Type} : ∀ (m : ℕ), (Fin m → CG α) → CG (Fin m → α)
  | 0, _, gs => (gs, Fin.elim0)
  | m + 1, f, gs =>
    ((f (Fin.last m) (mkFam m (fun i => f i.castSucc) gs).1).1,
      Fin.snoc (α := fun _ => α) (mkFam m (fun i => f i.castSucc) gs).2
        (f (Fin.last m) (mkFam m (fun i => f i.castSucc) gs).1).2)

lemma mkFam_spec {I : ℕ} {α : Type} (c : ℕ) : ∀ (m : ℕ) (g : Fin m → CG α)
    (P : Fin m → List Gate → α → Prop) (gs : List Gate), Good I gs →
    (∀ i gs1 gs2 a, Extends gs1 gs2 → P i gs1 a → P i gs2 a) →
    (∀ i gs1, Good I gs1 → Extends gs gs1 →
      Extends gs1 (g i gs1).1 ∧ (g i gs1).1.length ≤ gs1.length + c ∧ Good I (g i gs1).1 ∧
      P i (g i gs1).1 (g i gs1).2) →
    Extends gs (mkFam m g gs).1 ∧ (mkFam m g gs).1.length ≤ gs.length + m * c ∧
    Good I (mkFam m g gs).1 ∧ ∀ i, P i (mkFam m g gs).1 ((mkFam m g gs).2 i) := by
  intro m
  induction m with
  | zero =>
    intro g P gs hG _ _
    exact ⟨extends_refl gs, by simp [mkFam], hG, fun i => i.elim0⟩
  | succ m ih =>
    intro g P gs hG hmono hg
    have s1 := ih (fun i => g i.castSucc) (fun i => P i.castSucc) gs hG
      (fun i gs1 gs2 a h1 h2 => hmono i.castSucc gs1 gs2 a h1 h2)
      (fun i gs1 h1 h2 => hg i.castSucc gs1 h1 h2)
    rcases s1 with ⟨e1, l1, g1, p1⟩
    have s2 := hg (Fin.last m) _ g1 e1
    rcases s2 with ⟨e2, l2, g2, p2⟩
    refine ⟨extends_trans e1 e2, ?_, g2, ?_⟩
    · simp only [mkFam]
      have : (m + 1) * c = m * c + c := by ring
      omega
    · intro i
      simp only [mkFam]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using p2
      · simp only [Fin.snoc_castSucc]
        exact hmono j.castSucc _ _ _ e2 (p1 j)

def gCost (n N : ℕ) : ℕ := 30 * (n + 1) * (N + 1) ^ 2

def GFacts {N : ℕ} (n : ℕ) (stW spW : Fin N → ℕ) (edW : ℕ → Fin N → Fin N → ℕ)
    (o : GOut N) (V : ℕ → Bool) : Prop :=
  V o.1 = g_ok n (fun a => V (stW a)) (fun a => V (spW a)) (fun t a b => V (edW t a b)) ∧
  (∀ t ≤ n, ∀ a, V (o.2.1 t a) =
    g_reach (fun a => V (stW a)) (fun t a b => V (edW t a b)) t a) ∧
  (∀ t ≤ n, ∀ a, V (o.2.2 t a) =
    g_sel n (fun a => V (stW a)) (fun a => V (spW a)) (fun t a b => V (edW t a b)) (n - t) a)

def GSem {N : ℕ} (I n : ℕ) (stW spW : Fin N → ℕ) (edW : ℕ → Fin N → Fin N → ℕ)
    (gs : List Gate) (o : GOut N) : Prop :=
  o.1 < I + gs.length ∧ (∀ t ≤ n, ∀ a, o.2.1 t a < I + gs.length) ∧
  (∀ t ≤ n, ∀ a, o.2.2 t a < I + gs.length) ∧
  ∀ gs', Extends gs gs' → ∀ x : List Bool, x.length = I →
    GFacts n stW spW edW o (wireAt gs' x)

lemma GSem_mono {N : ℕ} {I n : ℕ} {stW spW : Fin N → ℕ} {edW : ℕ → Fin N → Fin N → ℕ}
    {gs1 gs2 : List Gate} {o : GOut N} (he : Extends gs1 gs2)
    (h : GSem I n stW spW edW gs1 o) : GSem I n stW spW edW gs2 o := by
  have hl := extends_length_le he
  rcases h with ⟨h1, h2, h3, h4⟩
  refine ⟨by omega, fun t ht a => by have := h2 t ht a; omega,
    fun t ht a => by have := h3 t ht a; omega,
    fun gs' he' x hx => h4 gs' (extends_trans he he') x hx⟩

def g2_ft (N : ℕ) (rw : Fin N → ℕ) (ew : Fin N → Fin N → ℕ) (b : Fin N) :
    List (List (ℕ × Bool)) :=
  (List.finRange N).map (fun a => [(rw a, true), (ew a b, true)])

lemma g2_ft_val (N : ℕ) (V : ℕ → Bool) (rw : Fin N → ℕ) (ew : Fin N → Fin N → ℕ) (b : Fin N) :
    dnfVal V (g2_ft N rw ew b) = (List.finRange N).any (fun a => V (rw a) && V (ew a b)) := by
  simp only [dnfVal, g2_ft, List.any_map]
  apply any_congr'
  intro a _
  simp [litVal]

lemma g2_ft_cost (N : ℕ) (rw : Fin N → ℕ) (ew : Fin N → Fin N → ℕ) (b : Fin N) :
    dnfCost (g2_ft N rw ew b) ≤ 1 + N * 6 := by
  have h := dnfCost_le 2 (g2_ft N rw ew b) (by
    intro t ht
    simp only [g2_ft, List.mem_map] at ht
    rcases ht with ⟨a, _, rfl⟩
    simp)
  simpa [g2_ft] using h

lemma g2_ft_valid (N L : ℕ) (rw : Fin N → ℕ) (ew : Fin N → Fin N → ℕ)
    (hr : ∀ a, rw a < L) (he : ∀ a b, ew a b < L) :
    ∀ b, ∀ t ∈ g2_ft N rw ew b, ∀ l ∈ t, l.1 < L := by
  intro b t ht l hl
  simp only [g2_ft, List.mem_map] at ht
  rcases ht with ⟨a, _, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact hr a
  · exact he a b

noncomputable def g2_fwd (I N : ℕ) (stW : Fin N → ℕ) (edW : ℕ → Fin N → Fin N → ℕ) :
    ℕ → CG (ℕ → Fin N → ℕ)
  | 0, gs => (gs, fun _ => stW)
  | t + 1, gs =>
    ((mkDnfTab I (Fin N) (g2_ft N ((g2_fwd I N stW edW t gs).2 t) (edW t))
        (g2_fwd I N stW edW t gs).1).1,
      fun t' => if t' = t + 1 then
        (mkDnfTab I (Fin N) (g2_ft N ((g2_fwd I N stW edW t gs).2 t) (edW t))
          (g2_fwd I N stW edW t gs).1).2
        else (g2_fwd I N stW edW t gs).2 t')

lemma g2_fwd_spec {I N : ℕ} (stW : Fin N → ℕ) (edW : ℕ → Fin N → Fin N → ℕ) (n : ℕ)
    {gs : List Gate} (hG : Good I gs) (hst : ∀ a, stW a < I + gs.length)
    (hed : ∀ t < n, ∀ a b, edW t a b < I + gs.length) :
    ∀ t ≤ n, Extends gs (g2_fwd I N stW edW t gs).1 ∧
      (g2_fwd I N stW edW t gs).1.length ≤ gs.length + t * (N * (1 + N * 6)) ∧
      Good I (g2_fwd I N stW edW t gs).1 ∧
      (∀ t' ≤ t, ∀ a, (g2_fwd I N stW edW t gs).2 t' a <
        I + (g2_fwd I N stW edW t gs).1.length) ∧
      ∀ gs', Extends (g2_fwd I N stW edW t gs).1 gs' → ∀ x : List Bool, x.length = I →
        ∀ t' ≤ t, ∀ a, wireAt gs' x ((g2_fwd I N stW edW t gs).2 t' a) =
          g_reach (fun a => wireAt gs' x (stW a)) (fun t a b => wireAt gs' x (edW t a b)) t' a := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨extends_refl gs, by simp [g2_fwd], hG, ?_, ?_⟩
    · intro t' _ a
      simpa [g2_fwd] using hst a
    · intro gs' _ x _ t' ht' a
      have h0 : t' = 0 := by omega
      subst h0
      simp [g2_fwd, g_reach]
  | succ t ih =>
    intro ht
    rcases ih (by omega) with ⟨e1, l1, g1, w1, ev1⟩
    have hl1 := extends_length_le e1
    have s := mkDnfTab_spec (I := I) (1 + N * 6) (Fin N)
      (g2_ft N ((g2_fwd I N stW edW t gs).2 t) (edW t)) (g2_fwd I N stW edW t gs).1 g1
      (g2_ft_valid N _ _ _ (fun a => w1 t le_rfl a)
        (fun a b => by have := hed t (by omega) a b; omega))
      (fun b => g2_ft_cost N _ _ b)
    rcases s with ⟨e2, l2, g2, w2, ev2⟩
    have hl2 := extends_length_le e2
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at l2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [g2_fwd]
      exact extends_trans e1 e2
    · simp only [g2_fwd]
      have hX : (t + 1) * (N * (1 + N * 6)) = t * (N * (1 + N * 6)) + N * (1 + N * 6) := by ring
      rw [hX]
      generalize N * (1 + N * 6) = X at *
      generalize t * X = Y at *
      omega
    · simp only [g2_fwd]
      exact g2
    · intro t' ht' a
      simp only [g2_fwd]
      split_ifs with h
      · exact w2 a
      · have := w1 t' (by omega) a
        omega
    · intro gs' he x hx t' ht' a
      simp only [g2_fwd] at he ⊢
      split_ifs with h
      · subst h
        rw [ev2 gs' he x hx a, g2_ft_val]
        have key : ∀ a', wireAt gs' x ((g2_fwd I N stW edW t gs).2 t a') =
            g_reach (fun a => wireAt gs' x (stW a)) (fun t a b => wireAt gs' x (edW t a b)) t a' :=
          fun a' => ev1 gs' (extends_trans e2 he) x hx t le_rfl a'
        simp only [key]
        rfl
      · exact ev1 gs' (extends_trans e2 he) x hx t' (by omega) a

def g2_p0 (N : ℕ) (rw sw : Fin N → ℕ) (a : Fin N) : List (List (ℕ × Bool)) :=
  [[(rw a, true), (sw a, true)]]

def g2_p1 (N : ℕ) (rw : Fin N → ℕ) (ew : Fin N → Fin N → ℕ) (sel : Fin N → ℕ) (a : Fin N) :
    List (List (ℕ × Bool)) :=
  (List.finRange N).map (fun b => [(rw a, true), (ew a b, true), (sel b, true)])

def g2_fst (N : ℕ) (pw : Fin N → ℕ) (a : Fin N) : List (List (ℕ × Bool)) :=
  [(pw a, true) :: ((List.finRange N).filter (fun a' => decide (a'.val < a.val))).map
    (fun a' => (pw a', false))]

lemma g2_p0_val (N : ℕ) (V : ℕ → Bool) (rw sw : Fin N → ℕ) (a : Fin N) :
    dnfVal V (g2_p0 N rw sw a) = (V (rw a) && V (sw a)) := by
  simp [dnfVal, g2_p0, litVal]

lemma g2_p1_val (N : ℕ) (V : ℕ → Bool) (rw : Fin N → ℕ) (ew : Fin N → Fin N → ℕ)
    (sel : Fin N → ℕ) (a : Fin N) :
    dnfVal V (g2_p1 N rw ew sel a) =
      (V (rw a) && (List.finRange N).any (fun b => V (ew a b) && V (sel b))) := by
  rw [Bool.eq_iff_iff]
  simp only [dnfVal, g2_p1, List.any_map, List.any_eq_true, Bool.and_eq_true, Function.comp]
  constructor
  · rintro ⟨b, hb, h⟩
    simp [litVal] at h
    exact ⟨h.1, b, hb, h.2.1, h.2.2⟩
  · rintro ⟨h1, b, hb, h2, h3⟩
    refine ⟨b, hb, ?_⟩
    simp [litVal, h1, h2, h3]

lemma g2_fst_val (N : ℕ) (V : ℕ → Bool) (pw : Fin N → ℕ) (a : Fin N) :
    dnfVal V (g2_fst N pw a) = g_first (fun a => V (pw a)) a := by
  rw [Bool.eq_iff_iff]
  simp only [dnfVal, g2_fst, g_first, List.any_cons, List.any_nil, Bool.or_false,
    List.all_cons, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp,
    Bool.not_eq_true', List.any_eq_false]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa [litVal] using h1, fun a' ha' => ?_⟩
    have := h2 a' ha'
    simpa [litVal] using this
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa [litVal] using h1, fun a' ha' => ?_⟩
    have := h2 a' ha'
    simpa [litVal] using this

lemma g2_fst_cost (N : ℕ) (pw : Fin N → ℕ) (a : Fin N) :
    dnfCost (g2_fst N pw a) ≤ 2 * N + 5 := by
  have h := List.length_filter_le (fun a' : Fin N => decide (a'.val < a.val)) (List.finRange N)
  simp only [List.length_finRange] at h
  simp only [g2_fst, dnfCost, List.length_cons, List.length_map]
  omega

lemma g2_fst_valid (N L : ℕ) (pw : Fin N → ℕ) (hp : ∀ a, pw a < L) :
    ∀ a, ∀ t ∈ g2_fst N pw a, ∀ l ∈ t, l.1 < L := by
  intro a t ht l hl
  simp only [g2_fst, List.mem_singleton] at ht
  subst ht
  simp only [List.mem_cons, List.mem_map] at hl
  rcases hl with rfl | ⟨a', _, rfl⟩
  · exact hp a
  · exact hp a'

noncomputable def g2_sel1 (I N : ℕ) (pt : Fin N → List (List (ℕ × Bool))) : CG (Fin N → ℕ) :=
  fun gs => mkDnfTab I (Fin N) (g2_fst N (mkDnfTab I (Fin N) pt gs).2)
    (mkDnfTab I (Fin N) pt gs).1

lemma g2_sel1_spec {I N : ℕ} (c : ℕ) (pt : Fin N → List (List (ℕ × Bool)))
    {gs : List Gate} (hG : Good I gs)
    (hw : ∀ a, ∀ t ∈ pt a, ∀ l ∈ t, l.1 < I + gs.length)
    (hc : ∀ a, dnfCost (pt a) ≤ c) :
    Extends gs (g2_sel1 I N pt gs).1 ∧
    (g2_sel1 I N pt gs).1.length ≤ gs.length + (N * c + N * (2 * N + 5)) ∧
    Good I (g2_sel1 I N pt gs).1 ∧
    (∀ a, (g2_sel1 I N pt gs).2 a < I + (g2_sel1 I N pt gs).1.length) ∧
    ∀ gs', Extends (g2_sel1 I N pt gs).1 gs' → ∀ x : List Bool, x.length = I → ∀ a,
      wireAt gs' x ((g2_sel1 I N pt gs).2 a) =
        g_first (fun a => dnfVal (wireAt gs' x) (pt a)) a := by
  have s1 := mkDnfTab_spec (I := I) c (Fin N) pt gs hG hw hc
  rcases s1 with ⟨e1, l1, g1, w1, ev1⟩
  have s2 := mkDnfTab_spec (I := I) (2 * N + 5) (Fin N)
    (g2_fst N (mkDnfTab I (Fin N) pt gs).2) (mkDnfTab I (Fin N) pt gs).1 g1
    (g2_fst_valid N _ _ w1) (fun a => g2_fst_cost N _ a)
  rcases s2 with ⟨e2, l2, g2, w2, ev2⟩
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at l1 l2
  refine ⟨extends_trans e1 e2, ?_, g2, w2, ?_⟩
  · simp only [g2_sel1]
    generalize N * c = X at *
    generalize N * (2 * N + 5) = Y at *
    omega
  · intro gs' he x hx a
    simp only [g2_sel1] at he ⊢
    rw [ev2 gs' he x hx a, g2_fst_val]
    have key : ∀ a', wireAt gs' x ((mkDnfTab I (Fin N) pt gs).2 a') =
        dnfVal (wireAt gs' x) (pt a') :=
      fun a' => ev1 gs' (extends_trans e2 he) x hx a'
    simp only [key]

def g2_selV {N : ℕ} (n : ℕ) (R : ℕ → Fin N → Bool) (sp : Fin N → Bool)
    (ed : ℕ → Fin N → Fin N → Bool) : ℕ → Fin N → Bool
  | 0 => g_first (fun a => R n a && sp a)
  | k + 1 => g_first (fun a => R (n - (k + 1)) a &&
      (List.finRange N).any (fun b => ed (n - (k + 1)) a b && g2_selV n R sp ed k b))

lemma g2_selV_eq {N : ℕ} (n : ℕ) (R : ℕ → Fin N → Bool) (st sp : Fin N → Bool)
    (ed : ℕ → Fin N → Fin N → Bool) (h : ∀ t ≤ n, ∀ a, R t a = g_reach st ed t a) :
    ∀ k, g2_selV n R sp ed k = g_sel n st sp ed k := by
  have hR : ∀ t ≤ n, R t = g_reach st ed t := fun t ht => funext (h t ht)
  intro k
  induction k with
  | zero =>
    simp only [g2_selV, g_sel, hR n le_rfl]
  | succ k ih =>
    simp only [g2_selV, g_sel, hR (n - (k + 1)) (Nat.sub_le _ _), ih]

noncomputable def g2_bwd (I n N : ℕ) (rW : ℕ → Fin N → ℕ) (spW : Fin N → ℕ)
    (edW : ℕ → Fin N → Fin N → ℕ) : ℕ → CG (ℕ → Fin N → ℕ)
  | 0, gs => ((g2_sel1 I N (g2_p0 N (rW n) spW) gs).1,
      fun _ => (g2_sel1 I N (g2_p0 N (rW n) spW) gs).2)
  | k + 1, gs =>
    ((g2_sel1 I N (g2_p1 N (rW (n - (k + 1))) (edW (n - (k + 1)))
        ((g2_bwd I n N rW spW edW k gs).2 k)) (g2_bwd I n N rW spW edW k gs).1).1,
      fun k' => if k' = k + 1 then
        (g2_sel1 I N (g2_p1 N (rW (n - (k + 1))) (edW (n - (k + 1)))
          ((g2_bwd I n N rW spW edW k gs).2 k)) (g2_bwd I n N rW spW edW k gs).1).2
        else (g2_bwd I n N rW spW edW k gs).2 k')

lemma g2_p0_cost (N : ℕ) (rw sw : Fin N → ℕ) (a : Fin N) :
    dnfCost (g2_p0 N rw sw a) ≤ 1 + N * 8 := by
  have := a.isLt
  simp only [g2_p0, dnfCost, List.length_cons, List.length_nil]
  omega

lemma g2_p1_cost (N : ℕ) (rw : Fin N → ℕ) (ew : Fin N → Fin N → ℕ) (sel : Fin N → ℕ)
    (a : Fin N) : dnfCost (g2_p1 N rw ew sel a) ≤ 1 + N * 8 := by
  have h := dnfCost_le 3 (g2_p1 N rw ew sel a) (by
    intro t ht
    simp only [g2_p1, List.mem_map] at ht
    rcases ht with ⟨b, _, rfl⟩
    simp)
  simpa [g2_p1] using h

lemma g2_bwd_spec {I N : ℕ} (n : ℕ) (rW : ℕ → Fin N → ℕ) (spW : Fin N → ℕ)
    (edW : ℕ → Fin N → Fin N → ℕ)
    {gs : List Gate} (hG : Good I gs) (hr : ∀ t ≤ n, ∀ a, rW t a < I + gs.length)
    (hsp : ∀ a, spW a < I + gs.length)
    (hed : ∀ t < n, ∀ a b, edW t a b < I + gs.length) :
    ∀ k ≤ n, Extends gs (g2_bwd I n N rW spW edW k gs).1 ∧
      (g2_bwd I n N rW spW edW k gs).1.length ≤
        gs.length + (k + 1) * (N * (1 + N * 8) + N * (2 * N + 5)) ∧
      Good I (g2_bwd I n N rW spW edW k gs).1 ∧
      (∀ k' ≤ k, ∀ a, (g2_bwd I n N rW spW edW k gs).2 k' a <
        I + (g2_bwd I n N rW spW edW k gs).1.length) ∧
      ∀ gs', Extends (g2_bwd I n N rW spW edW k gs).1 gs' → ∀ x : List Bool, x.length = I →
        ∀ k' ≤ k, ∀ a, wireAt gs' x ((g2_bwd I n N rW spW edW k gs).2 k' a) =
          g2_selV n (fun t a => wireAt gs' x (rW t a)) (fun a => wireAt gs' x (spW a))
            (fun t a b => wireAt gs' x (edW t a b)) k' a := by
  intro k
  induction k with
  | zero =>
    intro _
    have s := g2_sel1_spec (I := I) (1 + N * 8) (g2_p0 N (rW n) spW) hG
      (by
        intro a t ht l hl
        simp only [g2_p0, List.mem_singleton] at ht
        subst ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact hr n le_rfl a
        · exact hsp a)
      (fun a => g2_p0_cost N _ _ a)
    rcases s with ⟨e, l, g, wv, ev⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [g2_bwd] using e
    · simp only [g2_bwd]
      omega
    · simpa only [g2_bwd] using g
    · intro k' _ a
      simp only [g2_bwd]
      exact wv a
    · intro gs' he x hx k' hk' a
      have h0 : k' = 0 := by omega
      subst h0
      simp only [g2_bwd] at he ⊢
      rw [ev gs' he x hx a]
      simp only [g2_selV, g2_p0_val]
  | succ k ih =>
    intro hk
    rcases ih (by omega) with ⟨e1, l1, g1, w1, ev1⟩
    have hl1 := extends_length_le e1
    have s := g2_sel1_spec (I := I) (1 + N * 8)
      (g2_p1 N (rW (n - (k + 1))) (edW (n - (k + 1))) ((g2_bwd I n N rW spW edW k gs).2 k)) g1
      (by
        intro a t ht l hl
        simp only [g2_p1, List.mem_map] at ht
        rcases ht with ⟨b, _, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · have := hr (n - (k + 1)) (Nat.sub_le _ _) a
          omega
        · have := hed (n - (k + 1)) (by omega) a b
          omega
        · exact w1 k le_rfl b)
      (fun a => g2_p1_cost N _ _ _ a)
    rcases s with ⟨e2, l2, g2, w2, ev2⟩
    have hl2 := extends_length_le e2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [g2_bwd]
      exact extends_trans e1 e2
    · simp only [g2_bwd]
      have hX : (k + 1 + 1) * (N * (1 + N * 8) + N * (2 * N + 5)) =
          (k + 1) * (N * (1 + N * 8) + N * (2 * N + 5)) +
            (N * (1 + N * 8) + N * (2 * N + 5)) := by ring
      rw [hX]
      generalize N * (1 + N * 8) + N * (2 * N + 5) = X at *
      generalize (k + 1) * X = Y at *
      omega
    · simp only [g2_bwd]
      exact g2
    · intro k' hk' a
      simp only [g2_bwd]
      split_ifs with h
      · exact w2 a
      · have := w1 k' (by omega) a
        omega
    · intro gs' he x hx k' hk' a
      simp only [g2_bwd] at he ⊢
      split_ifs with h
      · subst h
        rw [ev2 gs' he x hx a]
        have key : ∀ c, wireAt gs' x ((g2_bwd I n N rW spW edW k gs).2 k c) =
            g2_selV n (fun t a => wireAt gs' x (rW t a)) (fun a => wireAt gs' x (spW a))
              (fun t a b => wireAt gs' x (edW t a b)) k c :=
          fun c => ev1 gs' (extends_trans e2 he) x hx k le_rfl c
        simp only [g2_selV, g2_p1_val, key]
      · exact ev1 gs' (extends_trans e2 he) x hx k' (by omega) a

def g2_okt (N : ℕ) (rw sw : Fin N → ℕ) (_ : Unit) : List (List (ℕ × Bool)) :=
  (List.finRange N).map (fun a => [(rw a, true), (sw a, true)])

lemma g2_okt_val (N : ℕ) (V : ℕ → Bool) (rw sw : Fin N → ℕ) (u : Unit) :
    dnfVal V (g2_okt N rw sw u) = (List.finRange N).any (fun a => V (rw a) && V (sw a)) := by
  simp only [dnfVal, g2_okt, List.any_map]
  apply any_congr'
  intro a _
  simp [litVal]

lemma g2_okt_cost (N : ℕ) (rw sw : Fin N → ℕ) (u : Unit) :
    dnfCost (g2_okt N rw sw u) ≤ 1 + N * 6 := by
  have h := dnfCost_le 2 (g2_okt N rw sw u) (by
    intro t ht
    simp only [g2_okt, List.mem_map] at ht
    rcases ht with ⟨a, _, rfl⟩
    simp)
  simpa [g2_okt] using h

lemma g2_cost_le (n N : ℕ) :
    n * (N * (1 + N * 6)) + (1 + N * 6) + (n + 1) * (N * (1 + N * 8) + N * (2 * N + 5)) ≤
      30 * (n + 1) * (N + 1) ^ 2 := by
  have h1 : n * (N * (1 + N * 6)) ≤ (n + 1) * (N * (1 + N * 6)) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : 1 + N * 6 ≤ (n + 1) * (1 + N * 6) := Nat.le_mul_of_pos_left _ (by omega)
  have h3 : N * (1 + N * 6) + (1 + N * 6) + (N * (1 + N * 8) + N * (2 * N + 5)) ≤
      30 * (N + 1) ^ 2 := by nlinarith
  calc n * (N * (1 + N * 6)) + (1 + N * 6) + (n + 1) * (N * (1 + N * 8) + N * (2 * N + 5))
      ≤ (n + 1) * (N * (1 + N * 6)) + (n + 1) * (1 + N * 6) +
        (n + 1) * (N * (1 + N * 8) + N * (2 * N + 5)) := by omega
    _ = (n + 1) * (N * (1 + N * 6) + (1 + N * 6) + (N * (1 + N * 8) + N * (2 * N + 5))) := by
      ring
    _ ≤ (n + 1) * (30 * (N + 1) ^ 2) := Nat.mul_le_mul_left _ h3
    _ = 30 * (n + 1) * (N + 1) ^ 2 := by ring

noncomputable def mkG (I n N : ℕ) (stW spW : Fin N → ℕ) (edW : ℕ → Fin N → Fin N → ℕ) :
    CG (GOut N) :=
  fun gs =>
    ((g2_bwd I n N (g2_fwd I N stW edW n gs).2 spW edW n
        (mkDnfTab I Unit (g2_okt N ((g2_fwd I N stW edW n gs).2 n) spW)
          (g2_fwd I N stW edW n gs).1).1).1,
      (mkDnfTab I Unit (g2_okt N ((g2_fwd I N stW edW n gs).2 n) spW)
        (g2_fwd I N stW edW n gs).1).2 (),
      (g2_fwd I N stW edW n gs).2,
      fun t => (g2_bwd I n N (g2_fwd I N stW edW n gs).2 spW edW n
        (mkDnfTab I Unit (g2_okt N ((g2_fwd I N stW edW n gs).2 n) spW)
          (g2_fwd I N stW edW n gs).1).1).2 (n - t))

theorem mkG_spec {I n N : ℕ} (stW spW : Fin N → ℕ) (edW : ℕ → Fin N → Fin N → ℕ)
    {gs : List Gate} (hG : Good I gs) (hst : ∀ a, stW a < I + gs.length)
    (hsp : ∀ a, spW a < I + gs.length) (hed : ∀ t < n, ∀ a b, edW t a b < I + gs.length) :
    Extends gs (mkG I n N stW spW edW gs).1 ∧
    (mkG I n N stW spW edW gs).1.length ≤ gs.length + gCost n N ∧
    Good I (mkG I n N stW spW edW gs).1 ∧
    GSem I n stW spW edW (mkG I n N stW spW edW gs).1 (mkG I n N stW spW edW gs).2 := by
  have sf := g2_fwd_spec (I := I) stW edW n hG hst hed n le_rfl
  rcases hf : g2_fwd I N stW edW n gs with ⟨gs1, rT⟩
  simp only [hf] at sf
  rcases sf with ⟨e1, l1, g1, w1, ev1⟩
  have hl1 := extends_length_le e1
  have so := mkDnfTab_spec (I := I) (1 + N * 6) Unit (g2_okt N (rT n) spW) gs1 g1
    (by
      intro u t ht l hl
      simp only [g2_okt, List.mem_map] at ht
      rcases ht with ⟨a, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact w1 n le_rfl a
      · have := hsp a
        omega)
    (fun u => g2_okt_cost N _ _ u)
  rcases ho : mkDnfTab I Unit (g2_okt N (rT n) spW) gs1 with ⟨gs2, oT⟩
  simp only [ho] at so
  rcases so with ⟨e2, l2, g2, w2, ev2⟩
  have hl2 := extends_length_le e2
  have hcu : Nat.card Unit = 1 := by simp
  rw [hcu, one_mul] at l2
  have sb := g2_bwd_spec (I := I) n rT spW edW g2
    (fun t ht a => by have := w1 t ht a; omega)
    (fun a => by have := hsp a; omega)
    (fun t ht a b => by have := hed t ht a b; omega) n le_rfl
  rcases hb : g2_bwd I n N rT spW edW n gs2 with ⟨gs3, sT⟩
  simp only [hb] at sb
  rcases sb with ⟨e3, l3, g3, w3, ev3⟩
  have hl3 := extends_length_le e3
  have hres : mkG I n N stW spW edW gs = (gs3, oT (), rT, fun t => sT (n - t)) := by
    simp only [mkG, hf, ho, hb]
  rw [hres]
  refine ⟨extends_trans e1 (extends_trans e2 e3), ?_, g3, ?_, ?_, ?_, ?_⟩
  · have hc := g2_cost_le n N
    unfold gCost
    generalize n * (N * (1 + N * 6)) = A at *
    generalize (n + 1) * (N * (1 + N * 8) + N * (2 * N + 5)) = B at *
    generalize 30 * (n + 1) * (N + 1) ^ 2 = C at *
    generalize N * 6 = D at *
    show gs3.length ≤ gs.length + C
    omega
  · show oT () < I + gs3.length
    have := w2 ()
    omega
  · intro t ht a
    show rT t a < I + gs3.length
    have := w1 t ht a
    omega
  · intro t ht a
    show sT (n - t) a < I + gs3.length
    exact w3 (n - t) (Nat.sub_le _ _) a
  · intro gs' he x hx
    have hreach : ∀ t ≤ n, ∀ a, wireAt gs' x (rT t a) =
        g_reach (fun a => wireAt gs' x (stW a)) (fun t a b => wireAt gs' x (edW t a b)) t a :=
      fun t ht a => ev1 gs' (extends_trans e2 (extends_trans e3 he)) x hx t ht a
    refine ⟨?_, hreach, ?_⟩
    · show wireAt gs' x (oT ()) = _
      rw [ev2 gs' (extends_trans e3 he) x hx (), g2_okt_val]
      have key : ∀ a, wireAt gs' x (rT n a) =
          g_reach (fun a => wireAt gs' x (stW a)) (fun t a b => wireAt gs' x (edW t a b)) n a :=
        fun a => hreach n le_rfl a
      simp only [key]
      rfl
    · intro t ht a
      show wireAt gs' x (sT (n - t) a) = _
      rw [ev3 gs' he x hx (n - t) (Nat.sub_le _ _) a]
      rw [g2_selV_eq n _ (fun a => wireAt gs' x (stW a)) (fun a => wireAt gs' x (spW a))
        (fun t a b => wireAt gs' x (edW t a b)) hreach (n - t)]

abbrev T1 (n s d w : ℕ) := Fin n × Fin s × Fin s × Fin d × EV w
abbrev T2 (n s w : ℕ) := Fin n × Fin s × Fin s × EV w
abbrev T3 (n s w : ℕ) := Fin n × Fin s × Fin s × SubE w
abbrev T4 (n s w : ℕ) := Fin n × Node n s w × Node n s w
abbrev T9 (n s : ℕ) := Fin (n + 1) × Fin s
abbrev T10 (n w : ℕ) := Fin n × EV w
abbrev T11 (n w : ℕ) := Fin n × Fin n × BV w × BV w
abbrev T12 (n : ℕ) := Fin n × Fin n

def inp (n s d w : ℕ) : ℕ := 2*s + n*s*s*(1+d*(2*w+1))

noncomputable def nn (n s w : ℕ) : ℕ := Nat.card (Node n s w)
noncomputable def nb (w : ℕ) : ℕ := Nat.card (BV w)
noncomputable def eN (n s w : ℕ) : Node n s w ≃ Fin (nn n s w) := Finite.equivFin (Node n s w)
noncomputable def eB (w : ℕ) : BV w ≃ Fin (nb w) := Finite.equivFin (BV w)

def eqBase (s d w t i j e : ℕ) : ℕ := b_edgeIx s d w t i j + 1 + e * (2*w+1)

noncomputable def dotWs (n s d w : ℕ) (x : T1 n s d w) : List ℕ :=
  ((List.finRange w).filter (fun k => x.2.2.2.2.1 k ≠ 0)).map
      (fun k => eqBase s d w x.1 x.2.1 x.2.2.1 x.2.2.2.1 + k.val) ++
    (if x.2.2.2.2.2.1 ≠ 0 then [eqBase s d w x.1 x.2.1 x.2.2.1 x.2.2.2.1 + w] else []) ++
    ((List.finRange w).filter (fun k => x.2.2.2.2.2.2 k ≠ 0)).map
      (fun k => eqBase s d w x.1 x.2.1 x.2.2.1 x.2.2.2.1 + w + 1 + k.val)

def memTerms (n s d w : ℕ) (dotT : T1 n s d w → ℕ) (x : T2 n s w) : List (List (ℕ × Bool)) :=
  [(List.finRange d).map (fun e => (dotT (x.1, x.2.1, x.2.2.1, e, x.2.2.2), false))]

noncomputable def eqTerms (n s w : ℕ) (memT : T2 n s w → ℕ) (x : T3 n s w) :
    List (List (ℕ × Bool)) :=
  [(enumF (EV w)).map (fun v => (memT (x.1, x.2.1, x.2.2.1, v), decide (v ∈ x.2.2.2)))]

noncomputable def stepNode {n s w : ℕ} (a : Node n s w) (L : SubE w) : SubB w × SubB w × ℕ :=
  (m1_stepR a.2.1 L, m1_stepR0 a.2.2.1 L, m1_stepSc a.2.1 a.2.2.1 a.2.2.2.val L)

def nodeMatch {n s w : ℕ} (b : Node n s w) (r : SubB w × SubB w × ℕ) : Prop :=
  b.2.1 = r.1 ∧ b.2.2.1 = r.2.1 ∧ b.2.2.2.val = r.2.2

noncomputable def edTerms (n s d w : ℕ) (eqT : T3 n s w → ℕ) (x : T4 n s w) :
    List (List (ℕ × Bool)) :=
  ((enumF (SubE w)).filter (fun c => nodeMatch x.2.2 (stepNode x.2.1 c))).map
    (fun c => [(b_edgeIx s d w x.1 x.2.1.1 x.2.2.1, true), (eqT (x.1, x.2.1.1, x.2.2.1, c), true)])

noncomputable def stTerms (n s w : ℕ) (a : Node n s w) : List (List (ℕ × Bool)) :=
  if nodeMatch a (⊤, ⊤, w) then [[(a.1.val, true)]] else []

noncomputable def obj {n s w : ℕ} (a : Node n s w) : ℕ :=
  a.2.2.2.val - Module.finrank (ZMod 2) a.2.2.1

noncomputable def okvTerms (n s w : ℕ) (reachT : ℕ → Fin (nn n s w) → ℕ) (v : Fin (n + 1)) :
    List (List (ℕ × Bool)) :=
  ((enumF (Node n s w)).filter (fun a => obj a = v.val)).map
    (fun a => [(reachT n (eN n s w a), true), (s + a.1.val, true)])

def bestTerms (n : ℕ) (okvT : Fin (n + 1) → ℕ) (v : Fin (n + 1)) : List (List (ℕ × Bool)) :=
  [(okvT v, true) :: ((List.finRange (n + 1)).filter (fun v' => v < v')).map
    (fun v' => (okvT v', false))]

noncomputable def spTerms (n s w : ℕ) (bestT : Fin (n + 1) → ℕ) (a : Node n s w) :
    List (List (ℕ × Bool)) :=
  if h : obj a < n + 1 then [[(s + a.1.val, true), (bestT ⟨obj a, h⟩, true)]] else []

noncomputable def walkTerms (n s w : ℕ) (selT : ℕ → Fin (nn n s w) → ℕ) (x : T9 n s) :
    List (List (ℕ × Bool)) :=
  ((enumF (Node n s w)).filter (fun a => a.1 = x.2)).map
    (fun a => [(selT x.1.val (eN n s w a), true)])

noncomputable def msTerms (n s w : ℕ) (walkT : T9 n s → ℕ) (memT : T2 n s w → ℕ) (x : T10 n w) :
    List (List (ℕ × Bool)) :=
  (enumF (Fin s × Fin s)).map (fun ij =>
    [(walkT (x.1.castSucc, ij.1), true), (walkT (x.1.succ, ij.2), true),
      (memT (x.1, ij.1, ij.2, x.2), true)])

noncomputable def beTerms (n w : ℕ) (msT : T10 n w → ℕ) (x : T11 n w) : List (List (ℕ × Bool)) :=
  if x.2.1 < x.1 then
    [[(msT (x.2.1, (x.2.2.1, 0, x.2.2.2)), true)], [(msT (x.2.1, (x.2.2.1, 1, x.2.2.2)), true)]]
  else if x.2.1 = x.1 then [[(msT (x.2.1, (x.2.2.1, 1, x.2.2.2)), true)]]
  else [[(msT (x.2.1, (x.2.2.1, 0, x.2.2.2)), true)]]

noncomputable def outTerms (n w : ℕ) (gf : Fin n → GOut (nb w)) (msT : T10 n w → ℕ) (x : T12 n) :
    List (List (ℕ × Bool)) :=
  if x.2 < x.1 then
    (enumF (BV w × BV w)).map (fun yy =>
      [((gf x.1).2.2 x.2.val (eB w yy.1), true), ((gf x.1).2.2 (x.2.val + 1) (eB w yy.2), true),
        (msT (x.2, (yy.1, 0, yy.2)), false)])
  else if x.2 = x.1 then [[((gf x.1).1, true)]]
  else []

noncomputable def r0 (n s d w : ℕ) : List Gate × (Unit → ℕ) :=
  mkDnfTab (inp n s d w) Unit (fun _ => [[]]) []

noncomputable def r1 (n s d w : ℕ) : List Gate × (T1 n s d w → ℕ) :=
  mkXorTab (inp n s d w) (T1 n s d w) (dotWs n s d w) (r0 n s d w).1

noncomputable def r2 (n s d w : ℕ) : List Gate × (T2 n s w → ℕ) :=
  mkDnfTab (inp n s d w) (T2 n s w) (memTerms n s d w (r1 n s d w).2) (r1 n s d w).1

noncomputable def r3 (n s d w : ℕ) : List Gate × (T3 n s w → ℕ) :=
  mkDnfTab (inp n s d w) (T3 n s w) (eqTerms n s w (r2 n s d w).2) (r2 n s d w).1

noncomputable def r4 (n s d w : ℕ) : List Gate × (T4 n s w → ℕ) :=
  mkDnfTab (inp n s d w) (T4 n s w) (edTerms n s d w (r3 n s d w).2) (r3 n s d w).1

noncomputable def r5 (n s d w : ℕ) : List Gate × (Node n s w → ℕ) :=
  mkDnfTab (inp n s d w) (Node n s w) (stTerms n s w) (r4 n s d w).1

noncomputable def stW (n s d w : ℕ) (k : Fin (nn n s w)) : ℕ :=
  (r5 n s d w).2 ((eN n s w).symm k)

noncomputable def edW (n s d w : ℕ) (t : ℕ) (ka kb : Fin (nn n s w)) : ℕ :=
  if h : t < n then (r4 n s d w).2 (⟨t, h⟩, (eN n s w).symm ka, (eN n s w).symm kb) else 0

noncomputable def r6 (n s d w : ℕ) : List Gate × GOut (nn n s w) :=
  mkG (inp n s d w) n (nn n s w) (stW n s d w) (stW n s d w) (edW n s d w) (r5 n s d w).1

noncomputable def r7 (n s d w : ℕ) : List Gate × (Fin (n + 1) → ℕ) :=
  mkDnfTab (inp n s d w) (Fin (n + 1)) (okvTerms n s w (r6 n s d w).2.2.1) (r6 n s d w).1

noncomputable def r8 (n s d w : ℕ) : List Gate × (Fin (n + 1) → ℕ) :=
  mkDnfTab (inp n s d w) (Fin (n + 1)) (bestTerms n (r7 n s d w).2) (r7 n s d w).1

noncomputable def r9 (n s d w : ℕ) : List Gate × (Node n s w → ℕ) :=
  mkDnfTab (inp n s d w) (Node n s w) (spTerms n s w (r8 n s d w).2) (r8 n s d w).1

noncomputable def spW (n s d w : ℕ) (k : Fin (nn n s w)) : ℕ :=
  (r9 n s d w).2 ((eN n s w).symm k)

noncomputable def r10 (n s d w : ℕ) : List Gate × GOut (nn n s w) :=
  mkG (inp n s d w) n (nn n s w) (stW n s d w) (spW n s d w) (edW n s d w) (r9 n s d w).1

noncomputable def r11 (n s d w : ℕ) : List Gate × (T9 n s → ℕ) :=
  mkDnfTab (inp n s d w) (T9 n s) (walkTerms n s w (r10 n s d w).2.2.2) (r10 n s d w).1

noncomputable def r12 (n s d w : ℕ) : List Gate × (T10 n w → ℕ) :=
  mkDnfTab (inp n s d w) (T10 n w) (msTerms n s w (r11 n s d w).2 (r2 n s d w).2) (r11 n s d w).1

noncomputable def r13 (n s d w : ℕ) : List Gate × (T11 n w → ℕ) :=
  mkDnfTab (inp n s d w) (T11 n w) (beTerms n w (r12 n s d w).2) (r12 n s d w).1

noncomputable def bedW (n s d w : ℕ) (r : Fin n) (t : ℕ) (ka kb : Fin (nb w)) : ℕ :=
  if h : t < n then (r13 n s d w).2 (r, ⟨t, h⟩, (eB w).symm ka, (eB w).symm kb) else 0

noncomputable def trW (n s d w : ℕ) (_ : Fin (nb w)) : ℕ := (r0 n s d w).2 ()

noncomputable def r14 (n s d w : ℕ) : List Gate × (Fin n → GOut (nb w)) :=
  mkFam n (fun r => mkG (inp n s d w) n (nb w) (trW n s d w) (trW n s d w) (bedW n s d w r))
    (r13 n s d w).1

noncomputable def r15 (n s d w : ℕ) : List Gate × (T12 n → ℕ) :=
  mkDnfTab (inp n s d w) (T12 n) (outTerms n w (r14 n s d w).2 (r12 n s d w).2) (r14 n s d w).1

def Facts (n s d w : ℕ) (V : ℕ → Bool) : Prop :=
  (V ((r0 n s d w).2 ()) = true) ∧
  (∀ x, V ((r1 n s d w).2 x) = xorVal V (dotWs n s d w x)) ∧
  (∀ x, V ((r2 n s d w).2 x) = dnfVal V (memTerms n s d w (r1 n s d w).2 x)) ∧
  (∀ x, V ((r3 n s d w).2 x) = dnfVal V (eqTerms n s w (r2 n s d w).2 x)) ∧
  (∀ x, V ((r4 n s d w).2 x) = dnfVal V (edTerms n s d w (r3 n s d w).2 x)) ∧
  (∀ x, V ((r5 n s d w).2 x) = dnfVal V (stTerms n s w x)) ∧
  GFacts n (stW n s d w) (stW n s d w) (edW n s d w) (r6 n s d w).2 V ∧
  (∀ x, V ((r7 n s d w).2 x) = dnfVal V (okvTerms n s w (r6 n s d w).2.2.1 x)) ∧
  (∀ x, V ((r8 n s d w).2 x) = dnfVal V (bestTerms n (r7 n s d w).2 x)) ∧
  (∀ x, V ((r9 n s d w).2 x) = dnfVal V (spTerms n s w (r8 n s d w).2 x)) ∧
  GFacts n (stW n s d w) (spW n s d w) (edW n s d w) (r10 n s d w).2 V ∧
  (∀ x, V ((r11 n s d w).2 x) = dnfVal V (walkTerms n s w (r10 n s d w).2.2.2 x)) ∧
  (∀ x, V ((r12 n s d w).2 x) =
    dnfVal V (msTerms n s w (r11 n s d w).2 (r2 n s d w).2 x)) ∧
  (∀ x, V ((r13 n s d w).2 x) = dnfVal V (beTerms n w (r12 n s d w).2 x)) ∧
  (∀ r, GFacts n (trW n s d w) (trW n s d w) (bedW n s d w r) ((r14 n s d w).2 r) V) ∧
  (∀ x, V ((r15 n s d w).2 x) = dnfVal V (outTerms n w (r14 n s d w).2 (r12 n s d w).2 x))

noncomputable def sizeExpr (n s d w : ℕ) : ℕ :=
  3 + Nat.card (T1 n s d w) * (4 * (2 * w + 1) + 1) + Nat.card (T2 n s w) * (2 * d + 3) +
  Nat.card (T3 n s w) * (2 * Nat.card (EV w) + 3) +
  Nat.card (T4 n s w) * (1 + Nat.card (SubE w) * 6) + nn n s w * 5 + gCost n (nn n s w) +
  (n + 1) * (1 + nn n s w * 6) + (n + 1) * (2 * (n + 2) + 3) + nn n s w * 7 +
  gCost n (nn n s w) + Nat.card (T9 n s) * (1 + nn n s w * 4) +
  Nat.card (T10 n w) * (1 + s * s * 8) + Nat.card (T11 n w) * 9 + n * gCost n (nb w) +
  Nat.card (T12 n) * (1 + nb w * nb w * 8)

def lamOf {n s d w : ℕ} (equation : Eqn n s d w) (t : Fin n) (i j : Fin s) : SubE w :=
  { carrier := {v | ∀ e : Fin d, dotProduct (equation t i j e).1 v.1 +
      (equation t i j e).2.1 * v.2.1 + dotProduct (equation t i j e).2.2 v.2.2 = 0}
    zero_mem' := by
      intro e
      simp
    smul_mem' := by
      intro c a ha e
      have h1 := ha e
      simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul]
      linear_combination c * h1
    , add_mem' := by
      intro a b ha hb e
      have h1 := ha e
      have h2 := hb e
      simp only [Prod.fst_add, Prod.snd_add, dotProduct_add, mul_add]
      linear_combination h1 + h2 }

lemma mem_lamOf {n s d w : ℕ} (equation : Eqn n s d w) (t : Fin n) (i j : Fin s) (v : EV w) :
    v ∈ lamOf equation t i j ↔ ∀ e : Fin d, dotProduct (equation t i j e).1 v.1 +
      (equation t i j e).2.1 * v.2.1 + dotProduct (equation t i j e).2.2 v.2.2 = 0 :=
  Iff.rfl

def pathLam {n s d w : ℕ} (equation : Eqn n s d w) (p : Fin (n + 1) → Fin s) (t : Fin n) :
    SubE w :=
  lamOf equation t (p t.castSucc) (p t.succ)

def legalP {n s : ℕ} (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (p : Fin (n + 1) → Fin s) : Prop :=
  start (p 0) = true ∧ stop (p (Fin.last n)) = true ∧
    ∀ t : Fin n, edge t (p t.castSucc) (p t.succ) = true

def InOK (n s d w : ℕ) (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Eqn n s d w) (V : ℕ → Bool) : Prop :=
  ∀ u < inp n s d w, V u = (b_bits n s d w start stop edge equation).getD u false

noncomputable def nodeOf {n s d w : ℕ} (equation : Eqn n s d w) (p : Fin (n + 1) → Fin s)
    (t : ℕ) : Node n s w :=
  (p ⟨min t n, by omega⟩, (m1_state (pathLam equation p) t).1,
    (m1_state (pathLam equation p) t).2.1,
    ⟨min (m1_state (pathLam equation p) t).2.2 (n + w), by omega⟩)

noncomputable def stM {n s w : ℕ} (start : Fin s → Bool) (a : Node n s w) : Bool :=
  start a.1 && decide (nodeMatch a (⊤, ⊤, w))

noncomputable def edM {n s d w : ℕ} (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Eqn n s d w) (t : ℕ) (a b : Node n s w) : Bool :=
  if h : t < n then
    edge ⟨t, h⟩ a.1 b.1 && decide (nodeMatch b (stepNode a (lamOf equation ⟨t, h⟩ a.1 b.1)))
  else false

noncomputable def outM (n s d w : ℕ) (V : ℕ → Bool) : Fin n → Fin n → ZMod 2 :=
  fun i j => if V ((r15 n s d w).2 (i, j)) then 1 else 0

def d0_bz (b : Bool) : ZMod 2 := if b then 1 else 0

lemma d0_z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma d0_bz_xor (a b : Bool) : d0_bz (xor a b) = d0_bz a + d0_bz b := by
  cases a <;> cases b <;> decide

lemma d0_bz_decide (a : ZMod 2) : d0_bz (decide (a ≠ 0)) = a := by
  rcases d0_z2 a with rfl | rfl <;> decide

lemma d0_of_bz (b : Bool) (a : ZMod 2) (h : d0_bz b = a) : b = decide (a ≠ 0) := by
  subst h
  cases b <;> decide

lemma d0_xor_append (v : ℕ → Bool) (l1 l2 : List ℕ) :
    xorVal v (l1 ++ l2) = xor (xorVal v l1) (xorVal v l2) := by
  induction l1 with
  | nil => simp [xorVal]
  | cons a l ih =>
    simp only [xorVal, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, Bool.xor_assoc]

lemma d0_xor_filter {w : ℕ} (v : ℕ → Bool) (c x : Fin w → ZMod 2) (f : Fin w → ℕ)
    (p : Fin w → Bool) (hp : ∀ k, p k = true ↔ x k ≠ 0)
    (h : ∀ k, v (f k) = decide (c k ≠ 0)) (l : List (Fin w)) :
    d0_bz (xorVal v ((l.filter p).map f)) = (l.map (fun k => c k * x k)).sum := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    by_cases hk : p k = true
    · have hx : x k = 1 := by
        rcases d0_z2 (x k) with h0 | h1
        · exact absurd h0 ((hp k).mp hk)
        · exact h1
      rw [List.filter_cons_of_pos hk]
      simp only [List.map_cons, List.sum_cons]
      show d0_bz (xor (v (f k)) (xorVal v ((l.filter p).map f))) = _
      rw [d0_bz_xor, ih, h k, d0_bz_decide, hx, mul_one]
    · have hx : x k = 0 := by
        by_contra h0
        exact hk ((hp k).mpr h0)
      rw [List.filter_cons_of_neg hk]
      simp only [List.map_cons, List.sum_cons]
      rw [ih, hx, mul_zero, zero_add]

lemma d0_dot (n s d w : ℕ) (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Eqn n s d w) (V : ℕ → Bool)
    (hin : InOK n s d w start stop edge equation V)
    (t : Fin n) (i j : Fin s) (e : Fin d) (v : EV w) :
    xorVal V (dotWs n s d w (t, i, j, e, v)) =
      decide (dotProduct (equation t i j e).1 v.1 + (equation t i j e).2.1 * v.2.1 +
        dotProduct (equation t i j e).2.2 v.2.2 ≠ 0) := by
  apply d0_of_bz
  have hL : ∀ k : Fin w, V (eqBase s d w t i j e + k.val) =
      decide ((equation t i j e).1 k ≠ 0) := by
    intro k
    unfold eqBase
    rw [hin _ (b_ix_lt (w := w) t i j e k.val (by have := k.isLt; omega))]
    exact b_get_left start stop edge equation t i j e k
  have hM : V (eqBase s d w t i j e + w) = decide ((equation t i j e).2.1 ≠ 0) := by
    unfold eqBase
    rw [hin _ (b_ix_lt (w := w) t i j e w (by omega))]
    exact b_get_mid start stop edge equation t i j e
  have hR : ∀ k : Fin w, V (eqBase s d w t i j e + w + 1 + k.val) =
      decide ((equation t i j e).2.2 k ≠ 0) := by
    intro k
    unfold eqBase
    have hlt := b_ix_lt (w := w) t i j e (w + 1 + k.val) (by have := k.isLt; omega)
    have he : b_edgeIx s d w t i j + 1 + e.val * (2 * w + 1) + (w + 1 + k.val) =
        b_edgeIx s d w t i j + 1 + e.val * (2 * w + 1) + w + 1 + k.val := by omega
    rw [he] at hlt
    rw [hin _ hlt]
    exact b_get_right start stop edge equation t i j e k
  unfold dotWs
  rw [d0_xor_append, d0_xor_append, d0_bz_xor, d0_bz_xor]
  rw [d0_xor_filter V (equation t i j e).1 v.1 _ _ (by intro k; simp) hL,
    d0_xor_filter V (equation t i j e).2.2 v.2.2 _ _ (by intro k; simp) hR]
  have hmid : d0_bz (xorVal V (if v.2.1 ≠ 0 then [eqBase s d w t i j e + w] else [])) =
      (equation t i j e).2.1 * v.2.1 := by
    by_cases hv : v.2.1 ≠ 0
    · rw [ite_eq_left hv]
      have h1 : v.2.1 = 1 := by
        rcases d0_z2 v.2.1 with h0 | h1
        · exact absurd h0 hv
        · exact h1
      show d0_bz (xor (V (eqBase s d w t i j e + w)) false) = _
      rw [Bool.xor_false, hM, d0_bz_decide, h1, mul_one]
    · rw [ite_eq_right hv]
      have h0 : v.2.1 = 0 := by
        by_contra h
        exact hv h
      rw [h0, mul_zero]
      rfl
  rw [hmid]
  simp only [dotProduct, Fin.sum_univ_def]

theorem sem_D0 (n s d w : ℕ) (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Eqn n s d w) (V : ℕ → Bool)
    (hin : InOK n s d w start stop edge equation V) (hF : Facts n s d w V) :
    (∀ t i j v, V ((r2 n s d w).2 (t, i, j, v)) = decide (v ∈ lamOf equation t i j)) ∧
    (∀ t a b, V ((r4 n s d w).2 (t, a, b)) = (edge t a.1 b.1 &&
      decide (nodeMatch b (stepNode a (lamOf equation t a.1 b.1))))) ∧
    (∀ a, V ((r5 n s d w).2 a) = stM start a) := by
  rcases hF with ⟨_, h1, h2, h3, h4, h5, _⟩
  have hmem : ∀ t i j v, V ((r2 n s d w).2 (t, i, j, v)) = decide (v ∈ lamOf equation t i j) := by
    intro t i j v
    rw [h2]
    apply Bool.eq_iff_iff.mpr
    simp only [dnfVal, memTerms, List.any_cons, List.any_nil, Bool.or_false, List.all_eq_true,
      List.mem_map, List.mem_finRange, true_and, decide_eq_true_eq, mem_lamOf]
    constructor
    · intro h e
      have h' := h _ ⟨e, rfl⟩
      simp only [litVal, beq_iff_eq] at h'
      rw [h1, d0_dot n s d w start stop edge equation V hin] at h'
      simpa using h'
    · rintro h l ⟨e, rfl⟩
      simp only [litVal, beq_iff_eq]
      rw [h1, d0_dot n s d w start stop edge equation V hin]
      simpa using h e
  have heq : ∀ t i j c, V ((r3 n s d w).2 (t, i, j, c)) = decide (lamOf equation t i j = c) := by
    intro t i j c
    rw [h3]
    apply Bool.eq_iff_iff.mpr
    simp only [dnfVal, eqTerms, List.any_cons, List.any_nil, Bool.or_false, List.all_eq_true,
      List.mem_map, decide_eq_true_eq]
    constructor
    · intro h
      apply SetLike.ext
      intro v
      have h' := h _ ⟨v, mem_enumF _ v, rfl⟩
      simp only [litVal, beq_iff_eq] at h'
      rw [hmem] at h'
      simpa using h'
    · rintro h l ⟨v, _, rfl⟩
      simp only [litVal, beq_iff_eq]
      rw [hmem, h]
  refine ⟨hmem, ?_, ?_⟩
  · intro t a b
    rw [h4]
    apply Bool.eq_iff_iff.mpr
    simp only [dnfVal, edTerms, List.any_eq_true, List.mem_map, List.mem_filter,
      decide_eq_true_eq, Bool.and_eq_true]
    have hedge : V (b_edgeIx s d w t a.1 b.1) = edge t a.1 b.1 := by
      rw [hin _ (b_edgeIx_lt t a.1 b.1)]
      exact b_get_edge start stop edge equation t a.1 b.1
    constructor
    · rintro ⟨l, ⟨c, ⟨_, hc⟩, rfl⟩, hl⟩
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, litVal,
        beq_iff_eq] at hl
      rcases hl with ⟨hl1, hl2⟩
      rw [heq] at hl2
      have hc2 : lamOf equation t a.1 b.1 = c := by simpa using hl2
      rw [hedge] at hl1
      exact ⟨hl1, by rw [hc2]; exact hc⟩
    · rintro ⟨he, hm⟩
      refine ⟨_, ⟨lamOf equation t a.1 b.1, ⟨mem_enumF _ _, hm⟩, rfl⟩, ?_⟩
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, litVal,
        beq_iff_eq]
      refine ⟨by rw [hedge]; exact he, ?_⟩
      rw [heq]
      simp
  · intro a
    rw [h5]
    have hst : V a.1.val = start a.1 := by
      rw [hin _ (by unfold inp; have := a.1.isLt; omega)]
      exact b_get_start start stop edge equation a.1
    unfold stTerms stM
    by_cases hm : nodeMatch a (⊤, ⊤, w)
    · rw [ite_eq_left hm]
      simp [dnfVal, litVal, hst, hm]
    · rw [ite_eq_right hm]
      simp [dnfVal, hm]

lemma d1_sc {n s d w : ℕ} (equation : Eqn n s d w) (p : Fin (n + 1) → Fin s) (t : ℕ)
    (ht : t ≤ n) :
    (nodeOf equation p t).2.2.2.val = (m1_state (pathLam equation p) t).2.2 := by
  show min _ _ = _
  exact Nat.min_eq_left (m1_sc_le _ t ht)

lemma d1_match {n s d w : ℕ} (equation : Eqn n s d w) (p : Fin (n + 1) → Fin s) (t : ℕ)
    (h : t < n) :
    nodeMatch (nodeOf equation p (t + 1))
      (stepNode (nodeOf equation p t) (pathLam equation p ⟨t, h⟩)) := by
  have hs := m1_state_succ (pathLam equation p) t h
  refine ⟨?_, ?_, ?_⟩
  · show (m1_state (pathLam equation p) (t + 1)).1 =
      m1_stepR (m1_state (pathLam equation p) t).1 _
    rw [hs]
  · show (m1_state (pathLam equation p) (t + 1)).2.1 =
      m1_stepR0 (m1_state (pathLam equation p) t).2.1 _
    rw [hs]
  · rw [d1_sc equation p (t + 1) (by omega)]
    show _ = m1_stepSc (m1_state (pathLam equation p) t).1
      (m1_state (pathLam equation p) t).2.1 (nodeOf equation p t).2.2.2.val _
    rw [d1_sc equation p t (by omega), hs]

lemma d1_node_ext {n s w : ℕ} (a b : Node n s w) (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1)
    (h3 : a.2.2.1 = b.2.2.1) (h4 : a.2.2.2.val = b.2.2.2.val) : a = b :=
  Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Fin.ext h4)))

theorem D1a {n s d w : ℕ} (start : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Eqn n s d w) (p : Fin (n + 1) → Fin s) (h0 : start (p 0) = true)
    (he : ∀ t : Fin n, edge t (p t.castSucc) (p t.succ) = true) :
    stM start (nodeOf equation p 0) = true ∧
    ∀ t < n, edM edge equation t (nodeOf equation p t) (nodeOf equation p (t + 1)) = true := by
  constructor
  · have h1 : (nodeOf equation p 0).1 = p 0 := by
      show p _ = p _
      congr 1
    have h2 : nodeMatch (nodeOf equation p 0) (⊤, ⊤, w) := by
      refine ⟨rfl, rfl, ?_⟩
      rw [d1_sc equation p 0 (Nat.zero_le n)]
      rfl
    unfold stM
    rw [h1, h0]
    simp [h2]
  · intro t ht
    have h1 : (nodeOf equation p t).1 = p (Fin.castSucc ⟨t, ht⟩) := by
      show p _ = p _
      congr 1
      apply Fin.ext
      simp
      omega
    have h2 : (nodeOf equation p (t + 1)).1 = p (Fin.succ ⟨t, ht⟩) := by
      show p _ = p _
      congr 1
      apply Fin.ext
      simp
      omega
    have h3 := d1_match equation p t ht
    have h4 : lamOf equation ⟨t, ht⟩ (nodeOf equation p t).1 (nodeOf equation p (t + 1)).1 =
        pathLam equation p ⟨t, ht⟩ := by
      rw [h1, h2]
      rfl
    unfold edM
    rw [dite_eq_left ht, h4]
    rw [h1, h2, he ⟨t, ht⟩]
    simp [h3]

theorem D1b {n s d w : ℕ} (start : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Eqn n s d w) (q : ℕ → Node n s w) (h0 : stM start (q 0) = true)
    (he : ∀ t < n, edM edge equation t (q t) (q (t + 1)) = true) :
    ∃ p : Fin (n + 1) → Fin s, start (p 0) = true ∧
      (∀ t : Fin n, edge t (p t.castSucc) (p t.succ) = true) ∧
      ∀ t ≤ n, q t = nodeOf equation p t := by
  have hst : start (q 0).1 = true ∧ nodeMatch (q 0) (⊤, ⊤, w) := by
    unfold stM at h0
    simpa using h0
  have hed : ∀ t (h : t < n), edge ⟨t, h⟩ (q t).1 (q (t + 1)).1 = true ∧
      nodeMatch (q (t + 1)) (stepNode (q t) (lamOf equation ⟨t, h⟩ (q t).1 (q (t + 1)).1)) := by
    intro t h
    have := he t h
    unfold edM at this
    rw [dite_eq_left h] at this
    simpa using this
  refine ⟨fun t => (q t.val).1, hst.1, fun t => (hed t.val t.isLt).1, ?_⟩
  have hfst : ∀ t ≤ n, (nodeOf equation (fun t : Fin (n + 1) => (q t.val).1) t).1 = (q t).1 := by
    intro t ht
    show (q (min t n)).1 = _
    rw [Nat.min_eq_left ht]
  intro t
  induction t with
  | zero =>
    intro ht
    rcases hst.2 with ⟨a1, a2, a3⟩
    refine d1_node_ext _ _ (hfst 0 ht).symm a1 a2 ?_
    rw [d1_sc equation _ 0 ht, a3]
    rfl
  | succ t ih =>
    intro ht
    have hlt : t < n := by omega
    have hq := ih (by omega)
    have hm := (hed t hlt).2
    have hl : lamOf equation ⟨t, hlt⟩ (q t).1 (q (t + 1)).1 =
        pathLam equation (fun t : Fin (n + 1) => (q t.val).1) ⟨t, hlt⟩ := rfl
    rw [hl, hq] at hm
    have hm' := d1_match equation (fun t : Fin (n + 1) => (q t.val).1) t hlt
    rcases hm with ⟨a1, a2, a3⟩
    rcases hm' with ⟨b1, b2, b3⟩
    exact d1_node_ext _ _ (hfst (t + 1) ht).symm (a1.trans b1.symm) (a2.trans b2.symm)
      (a3.trans b3.symm)

theorem D1c {n s d w : ℕ} (equation : Eqn n s d w) (p : Fin (n + 1) → Fin s) :
    (∀ t : Fin (n + 1), (nodeOf equation p t.val).1 = p t) ∧
    obj (nodeOf equation p n) = Module.finrank (ZMod 2) ↥(m1_poss (pathLam equation p)) := by
  constructor
  · intro t
    show p _ = p _
    congr 1
    apply Fin.ext
    have := t.isLt
    simp
    omega
  · unfold obj
    rw [d1_sc equation p n (le_refl n)]
    exact Nat.sub_eq_of_eq_add (m1_main (pathLam equation p)).symm

noncomputable def dd_f {n s d w : ℕ} (equation : Eqn n s d w) (p : Fin (n + 1) → Fin s) : ℕ :=
  Module.finrank (ZMod 2) ↥(m1_poss (pathLam equation p))

lemma dd_f_le {n s d w : ℕ} (equation : Eqn n s d w) (p : Fin (n + 1) → Fin s) :
    dd_f equation p ≤ n := by
  unfold dd_f
  have h := Submodule.finrank_le (m1_poss (pathLam equation p))
  simpa using h

lemma dd_dnf_map {α : Type} (V : ℕ → Bool) (l : List α) (f : α → List (ℕ × Bool)) :
    dnfVal V (l.map f) = true ↔ ∃ a ∈ l, ∀ x ∈ f a, V x.1 = x.2 := by
  simp [dnfVal, litVal]

lemma dd_stop {n s d w : ℕ} {start stop : Fin s → Bool} {edge : Fin n → Fin s → Fin s → Bool}
    {equation : Eqn n s d w} {V : ℕ → Bool}
    (hin : InOK n s d w start stop edge equation V) (i : Fin s) : V (s + i.val) = stop i := by
  rw [hin (s + i.val) (Nat.lt_of_lt_of_le (by omega : s + i.val < 2 * s) (Nat.le_add_right _ _))]
  exact b_get_stop start stop edge equation i

lemma dd_st_eq {n s d w : ℕ} {start stop : Fin s → Bool} {edge : Fin n → Fin s → Fin s → Bool}
    {equation : Eqn n s d w} {V : ℕ → Bool}
    (hin : InOK n s d w start stop edge equation V) (hF : Facts n s d w V)
    (k : Fin (nn n s w)) : V (stW n s d w k) = stM start ((eN n s w).symm k) :=
  (sem_D0 n s d w start stop edge equation V hin hF).2.2 _

lemma dd_ed_eq {n s d w : ℕ} {start stop : Fin s → Bool} {edge : Fin n → Fin s → Fin s → Bool}
    {equation : Eqn n s d w} {V : ℕ → Bool}
    (hin : InOK n s d w start stop edge equation V) (hF : Facts n s d w V)
    (t : ℕ) (ht : t < n) (ka kb : Fin (nn n s w)) :
    V (edW n s d w t ka kb) =
      edM edge equation t ((eN n s w).symm ka) ((eN n s w).symm kb) := by
  simp only [edW, edM, dite_eq_left ht]
  exact (sem_D0 n s d w start stop edge equation V hin hF).2.1 _ _ _

lemma dd_path {n s d w : ℕ} {start stop : Fin s → Bool} {edge : Fin n → Fin s → Fin s → Bool}
    {equation : Eqn n s d w} {V : ℕ → Bool}
    (hin : InOK n s d w start stop edge equation V) (hF : Facts n s d w V)
    (q : ℕ → Fin (nn n s w)) :
    (V (stW n s d w (q 0)) = true ∧ ∀ t < n, V (edW n s d w t (q t) (q (t + 1))) = true) ↔
    ∃ p : Fin (n + 1) → Fin s, start (p 0) = true ∧
      (∀ t : Fin n, edge t (p t.castSucc) (p t.succ) = true) ∧
      ∀ t ≤ n, q t = eN n s w (nodeOf equation p t) := by
  constructor
  · rintro ⟨h0, he⟩
    rw [dd_st_eq hin hF] at h0
    obtain ⟨p, hp0, hpe, hq⟩ := D1b start edge equation (fun t => (eN n s w).symm (q t)) h0
      (fun t ht => by rw [← dd_ed_eq hin hF t ht]; exact he t ht)
    refine ⟨p, hp0, hpe, fun t ht => ?_⟩
    rw [← hq t ht]
    simp
  · rintro ⟨p, hp0, hpe, hq⟩
    obtain ⟨a0, ae⟩ := D1a start edge equation p hp0 hpe
    refine ⟨?_, fun t ht => ?_⟩
    · rw [dd_st_eq hin hF, hq 0 (Nat.zero_le _)]
      simpa using a0
    · rw [dd_ed_eq hin hF t ht, hq t (le_of_lt ht), hq (t + 1) ht]
      simpa using ae t ht

lemma dd_okv {n s d w : ℕ} {start stop : Fin s → Bool} {edge : Fin n → Fin s → Fin s → Bool}
    {equation : Eqn n s d w} {V : ℕ → Bool}
    (hin : InOK n s d w start stop edge equation V) (hF : Facts n s d w V) (v : Fin (n + 1)) :
    V ((r7 n s d w).2 v) = true ↔
      ∃ p, legalP start stop edge p ∧ dd_f equation p = v.val := by
  have hF' := hF
  obtain ⟨_, _, _, _, _, _, hG6, h7, _⟩ := hF'
  rw [h7 v, okvTerms, dd_dnf_map]
  constructor
  · rintro ⟨a, ha, hx⟩
    have hobj : obj a = v.val := of_decide_eq_true (List.mem_filter.mp ha).2
    have h1 := hx ((r6 n s d w).2.2.1 n (eN n s w a), true) (by simp)
    have h2 := hx (s + a.1.val, true) (by simp)
    simp only at h1 h2
    rw [hG6.2.1 n le_rfl, g_reach_iff] at h1
    obtain ⟨q, hq0, hqn, hqe⟩ := h1
    obtain ⟨p, hp0, hpe, hq⟩ := (dd_path hin hF q).mp ⟨hq0, hqe⟩
    have han : a = nodeOf equation p n := by
      have h3 := hq n le_rfl
      rw [hqn] at h3
      exact (eN n s w).injective h3
    rw [dd_stop hin] at h2
    refine ⟨p, ⟨hp0, ?_, hpe⟩, ?_⟩
    · have h4 := (D1c equation p).1 (Fin.last n)
      simp only [Fin.val_last] at h4
      rw [← h4, ← han]
      exact h2
    · unfold dd_f
      rw [← (D1c equation p).2, ← han]
      exact hobj
  · rintro ⟨p, ⟨hp0, hps, hpe⟩, hf⟩
    have h4 := (D1c equation p).1 (Fin.last n)
    simp only [Fin.val_last] at h4
    refine ⟨nodeOf equation p n, List.mem_filter.mpr ⟨mem_enumF _ _, decide_eq_true ?_⟩, ?_⟩
    · rw [(D1c equation p).2]
      exact hf
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · simp only
        rw [hG6.2.1 n le_rfl, g_reach_iff]
        have h5 := (dd_path hin hF (fun t => eN n s w (nodeOf equation p t))).mpr
          ⟨p, hp0, hpe, fun t _ => rfl⟩
        exact ⟨fun t => eN n s w (nodeOf equation p t), h5.1, rfl, h5.2⟩
      · simp only
        rw [dd_stop hin, h4]
        exact hps

lemma dd_best {n s d w : ℕ} {V : ℕ → Bool} (hF : Facts n s d w V) (v : Fin (n + 1)) :
    V ((r8 n s d w).2 v) = true ↔ V ((r7 n s d w).2 v) = true ∧
      ∀ v' : Fin (n + 1), v < v' → V ((r7 n s d w).2 v') = false := by
  obtain ⟨_, _, _, _, _, _, _, _, h8, _⟩ := hF
  rw [h8 v]
  simp only [bestTerms, dnfVal, litVal, List.any_cons, List.any_nil, Bool.or_false,
    List.all_cons, List.all_map, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, Function.comp]

lemma dd_sp {n s d w : ℕ} {start stop : Fin s → Bool} {edge : Fin n → Fin s → Fin s → Bool}
    {equation : Eqn n s d w} {V : ℕ → Bool}
    (hin : InOK n s d w start stop edge equation V) (hF : Facts n s d w V) (a : Node n s w) :
    V ((r9 n s d w).2 a) = true ↔
      ∃ h : obj a < n + 1, stop a.1 = true ∧ V ((r8 n s d w).2 ⟨obj a, h⟩) = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, h9, _⟩ := hF
  rw [h9 a]
  unfold spTerms
  by_cases h : obj a < n + 1
  · rw [dite_eq_left h]
    simp [dnfVal, litVal, dd_stop hin, h]
  · rw [dite_eq_right h]
    simp [dnfVal, h]

lemma dd_legal2 {n s d w : ℕ} {start stop : Fin s → Bool} {edge : Fin n → Fin s → Fin s → Bool}
    {equation : Eqn n s d w} {V : ℕ → Bool}
    (hin : InOK n s d w start stop edge equation V) (hF : Facts n s d w V)
    (q : ℕ → Fin (nn n s w)) :
    g_legal n (fun a => V (stW n s d w a)) (fun a => V (spW n s d w a))
      (fun t a b => V (edW n s d w t a b)) q ↔
    ∃ p, legalP start stop edge p ∧ (∀ t ≤ n, q t = eN n s w (nodeOf equation p t)) ∧
      ∀ p', legalP start stop edge p' → dd_f equation p' ≤ dd_f equation p := by
  constructor
  · rintro ⟨h0, hsp, he⟩
    obtain ⟨p, hp0, hpe, hq⟩ := (dd_path hin hF q).mp ⟨h0, he⟩
    have h4 := (D1c equation p).1 (Fin.last n)
    simp only [Fin.val_last] at h4
    have hsp' : V ((r9 n s d w).2 (nodeOf equation p n)) = true := by
      have h5 : V (spW n s d w (q n)) = true := hsp
      rw [hq n le_rfl] at h5
      simpa [spW] using h5
    obtain ⟨hlt, hstop, hb⟩ := (dd_sp hin hF _).mp hsp'
    rw [h4] at hstop
    have hobj : obj (nodeOf equation p n) = dd_f equation p := (D1c equation p).2
    refine ⟨p, ⟨hp0, hstop, hpe⟩, hq, fun p' hp' => ?_⟩
    by_contra hcon
    have hgt : dd_f equation p < dd_f equation p' := Nat.lt_of_not_le hcon
    have hle := dd_f_le equation p'
    have h6 := ((dd_best hF _).mp hb).2 ⟨dd_f equation p', by omega⟩
      (by rw [Fin.lt_def]; simp only; omega)
    have h7 := (dd_okv hin hF ⟨dd_f equation p', by omega⟩).mpr ⟨p', hp', rfl⟩
    rw [h6] at h7
    exact Bool.noConfusion h7
  · rintro ⟨p, ⟨hp0, hps, hpe⟩, hq, hmax⟩
    have h5 := (dd_path hin hF q).mpr ⟨p, hp0, hpe, hq⟩
    have h4 := (D1c equation p).1 (Fin.last n)
    simp only [Fin.val_last] at h4
    have hobj : obj (nodeOf equation p n) = dd_f equation p := (D1c equation p).2
    have hle := dd_f_le equation p
    refine ⟨h5.1, ?_, h5.2⟩
    show V (spW n s d w (q n)) = true
    rw [hq n le_rfl]
    have hgoal : V ((r9 n s d w).2 (nodeOf equation p n)) = true := by
      rw [dd_sp hin hF]
      refine ⟨by omega, by rw [h4]; exact hps, ?_⟩
      rw [dd_best hF]
      refine ⟨(dd_okv hin hF _).mpr ⟨p, ⟨hp0, hps, hpe⟩, hobj.symm⟩, fun v' hv' => ?_⟩
      by_contra hcon
      have h8 : V ((r7 n s d w).2 v') = true := by simpa using hcon
      obtain ⟨p', hp', hf'⟩ := (dd_okv hin hF v').mp h8
      have h9 := hmax p' hp'
      rw [Fin.lt_def] at hv'
      simp only at hv'
      omega
    simpa [spW] using hgoal

lemma dd_exists_max {n s d w : ℕ} {start stop : Fin s → Bool}
    {edge : Fin n → Fin s → Fin s → Bool} (equation : Eqn n s d w)
    (h : ∃ p, legalP start stop edge p) :
    ∃ p, legalP start stop edge p ∧
      ∀ p', legalP start stop edge p' → dd_f equation p' ≤ dd_f equation p := by
  obtain ⟨p0, hp0⟩ := h
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun p : Fin (n + 1) → Fin s => legalP start stop edge p))
    (dd_f equation) ⟨p0, by simp [hp0]⟩
  refine ⟨p, by simpa using hp, fun p' hp' => hmax p' (by simp [hp'])⟩

theorem sem_D1 (n s d w : ℕ) (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Eqn n s d w) (V : ℕ → Bool)
    (hin : InOK n s d w start stop edge equation V) (hF : Facts n s d w V) :
    (V (r10 n s d w).2.1 = true ↔ ∃ p, legalP start stop edge p) ∧
    (V (r10 n s d w).2.1 = true → ∃ p, legalP start stop edge p ∧
      (∀ t j, V ((r11 n s d w).2 (t, j)) = decide (p t = j)) ∧
      ∀ q, legalP start stop edge q →
        Module.finrank (ZMod 2) ↥(m1_poss (pathLam equation q)) ≤
          Module.finrank (ZMod 2) ↥(m1_poss (pathLam equation p))) ∧
    (V (r10 n s d w).2.1 = false → ∀ t j, V ((r11 n s d w).2 (t, j)) = false) := by
  have hF' := hF
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hG10, h11, _⟩ := hF'
  obtain ⟨hok, _, hsel⟩ := hG10
  have hiff : V (r10 n s d w).2.1 = true ↔ ∃ p, legalP start stop edge p := by
    rw [hok, g_ok_iff]
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨p, hp, _⟩ := (dd_legal2 hin hF q).mp hq
      exact ⟨p, hp⟩
    · intro h
      obtain ⟨p, hp, hmax⟩ := dd_exists_max equation h
      exact ⟨fun t => eN n s w (nodeOf equation p t),
        (dd_legal2 hin hF _).mpr ⟨p, hp, fun t _ => rfl, hmax⟩⟩
  refine ⟨hiff, ?_, ?_⟩
  · intro h
    rw [hok, g_ok_iff] at h
    obtain ⟨q, hq, hs⟩ := g_sel_of_exists _ _ _ _ h
    obtain ⟨p, hp, hqp, hmax⟩ := (dd_legal2 hin hF q).mp hq
    refine ⟨p, hp, fun t j => ?_, hmax⟩
    have hc := (D1c equation p).1 t
    rw [Bool.eq_iff_iff, h11 (t, j), walkTerms, dd_dnf_map, decide_eq_true_iff]
    have htn : t.val ≤ n := Nat.le_of_lt_succ t.isLt
    constructor
    · rintro ⟨a, ha, hx⟩
      have ha1 : a.1 = j := of_decide_eq_true (List.mem_filter.mp ha).2
      have h1 := hx ((r10 n s d w).2.2.2 t.val (eN n s w a), true) (by simp)
      simp only at h1
      rw [hsel t.val htn, hs t.val htn, decide_eq_true_iff, hqp t.val htn] at h1
      have h2 := (eN n s w).injective h1
      rw [← hc, h2]
      exact ha1
    · intro hpj
      refine ⟨nodeOf equation p t.val, List.mem_filter.mpr ⟨mem_enumF _ _, decide_eq_true ?_⟩, ?_⟩
      · rw [hc]
        exact hpj
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx
        simp only
        rw [hsel t.val htn, hs t.val htn, decide_eq_true_iff, hqp t.val htn]
  · intro h t j
    have hno : ¬ ∃ q, g_legal n (fun a => V (stW n s d w a)) (fun a => V (spW n s d w a))
        (fun t a b => V (edW n s d w t a b)) q := by
      intro hex
      rw [hok] at h
      have := (g_ok_iff _ _ _ _).mpr hex
      rw [h] at this
      exact Bool.noConfusion this
    have hs := g_sel_of_not _ _ _ _ hno
    have htn : t.val ≤ n := Nat.le_of_lt_succ t.isLt
    rw [Bool.eq_false_iff]
    intro hcon
    rw [h11 (t, j), walkTerms, dd_dnf_map] at hcon
    obtain ⟨a, _, hx⟩ := hcon
    have h1 := hx ((r10 n s d w).2.2.2 t.val (eN n s w a), true) (by simp)
    simp only at h1
    rw [hsel t.val htn, hs (n - t.val) (Nat.sub_le _ _)] at h1
    exact Bool.noConfusion h1

lemma d2_z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

def d2_ed {n w : ℕ} (lam : Fin n → SubE w) (r t : Fin n) (y y' : BV w) : Prop :=
  if t < r then ((y, (0 : ZMod 2), y') ∈ lam t ∨ (y, (1 : ZMod 2), y') ∈ lam t)
  else if t = r then (y, (1 : ZMod 2), y') ∈ lam t else (y, (0 : ZMod 2), y') ∈ lam t

lemma d2_ms_hot {n s d w : ℕ} (equation : Eqn n s d w) (p : Fin (n + 1) → Fin s) (V : ℕ → Bool)
    (walkT : T9 n s → ℕ) (memT : T2 n s w → ℕ)
    (hwalk : ∀ t j, V (walkT (t, j)) = decide (p t = j))
    (hmem : ∀ t i j v, V (memT (t, i, j, v)) = decide (v ∈ lamOf equation t i j))
    (t : Fin n) (v : EV w) :
    dnfVal V (msTerms n s w walkT memT (t, v)) = decide (v ∈ pathLam equation p t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [dnfVal, msTerms, List.any_map, List.any_eq_true, Function.comp, decide_eq_true_eq]
  constructor
  · rintro ⟨ij, _, h⟩
    simp only [List.all_cons, List.all_nil, litVal, hwalk, hmem, Bool.and_true,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    unfold pathLam
    rw [h1, h2]
    exact h3
  · intro h
    refine ⟨(p t.castSucc, p t.succ), mem_enumF _ _, ?_⟩
    simp only [List.all_cons, List.all_nil, litVal, hwalk, hmem, Bool.and_true,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨trivial, trivial, h⟩

lemma d2_ms_cold {n s w : ℕ} (V : ℕ → Bool)
    (walkT : T9 n s → ℕ) (memT : T2 n s w → ℕ)
    (hwalk : ∀ t j, V (walkT (t, j)) = false) (x : T10 n w) :
    dnfVal V (msTerms n s w walkT memT x) = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [dnfVal, msTerms, List.any_map, List.any_eq_true, Function.comp] at h
  obtain ⟨ij, _, h⟩ := h
  simp [litVal, hwalk] at h

lemma d2_be {n w : ℕ} (lam : Fin n → SubE w) (V : ℕ → Bool) (msT : T10 n w → ℕ)
    (hms : ∀ t v, V (msT (t, v)) = decide (v ∈ lam t)) (r t : Fin n) (y y' : BV w) :
    dnfVal V (beTerms n w msT (r, t, y, y')) = decide (d2_ed lam r t y y') := by
  unfold beTerms d2_ed
  by_cases h1 : t < r
  · simp [h1, dnfVal, litVal, hms]
  · by_cases h2 : t = r
    · subst h2
      simp [dnfVal, litVal, hms]
    · simp [h1, h2, dnfVal, litVal, hms]

lemma d2_be_cold {n w : ℕ} (V : ℕ → Bool) (msT : T10 n w → ℕ)
    (hms : ∀ x, V (msT x) = false) (x : T11 n w) :
    dnfVal V (beTerms n w msT x) = false := by
  unfold beTerms
  split_ifs <;> simp [dnfVal, litVal, hms]

noncomputable def d2_x {n w : ℕ} (lam : Fin n → SubE w) (r : Fin n) (y : ℕ → BV w) :
    Fin n → ZMod 2 :=
  fun t => if t < r then (if (y t.val, (0 : ZMod 2), y (t.val + 1)) ∈ lam t then 0 else 1)
    else if t = r then 1 else 0

lemma d2_x_mem {n w : ℕ} (lam : Fin n → SubE w) (r : Fin n)
    (ed : ℕ → Fin (nb w) → Fin (nb w) → Bool)
    (hed : ∀ t : Fin n, ∀ ka kb, ed t.val ka kb =
      decide (d2_ed lam r t ((eB w).symm ka) ((eB w).symm kb)))
    (q : ℕ → Fin (nb w)) (hq : g_legal n (fun _ => true) (fun _ => true) ed q) :
    d2_x lam r (fun t => (eB w).symm (q t)) ∈ m1_poss lam := by
  rw [m1_mem_poss]
  refine ⟨fun t => (eB w).symm (q t.val), fun t => ?_⟩
  have h := hq.2.2 t.val t.isLt
  rw [hed t] at h
  have h' := of_decide_eq_true h
  unfold d2_ed at h'
  simp only [d2_x, Fin.val_castSucc, Fin.val_succ]
  by_cases h1 : t < r
  · rw [ite_eq_left h1] at h' ⊢
    by_cases h3 : ((eB w).symm (q t.val), (0 : ZMod 2), (eB w).symm (q (t.val + 1))) ∈ lam t
    · rw [ite_eq_left h3]
      exact h3
    · rw [ite_eq_right h3]
      exact h'.resolve_left h3
  · rw [ite_eq_right h1] at h' ⊢
    by_cases h2 : t = r
    · rw [ite_eq_left h2] at h' ⊢
      exact h'
    · rw [ite_eq_right h2] at h' ⊢
      exact h'

lemma d2_legal_of_x {n w : ℕ} (lam : Fin n → SubE w) (r : Fin n)
    (ed : ℕ → Fin (nb w) → Fin (nb w) → Bool)
    (hed : ∀ t : Fin n, ∀ ka kb, ed t.val ka kb =
      decide (d2_ed lam r t ((eB w).symm ka) ((eB w).symm kb)))
    (x : Fin n → ZMod 2) (hx : x ∈ m1_poss lam) (hr : x r = 1)
    (hz : ∀ t : Fin n, r < t → x t = 0) :
    ∃ q, g_legal n (fun _ => true) (fun _ => true) ed q := by
  rw [m1_mem_poss] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨fun t => eB w (y ⟨min t n, Nat.lt_succ_of_le (Nat.min_le_right t n)⟩), rfl, rfl,
    fun t ht => ?_⟩
  have hd := hed ⟨t, ht⟩ (eB w (y ⟨min t n, Nat.lt_succ_of_le (Nat.min_le_right t n)⟩))
    (eB w (y ⟨min (t + 1) n, Nat.lt_succ_of_le (Nat.min_le_right (t + 1) n)⟩))
  simp only [Equiv.symm_apply_apply] at hd
  show ed t _ _ = true
  rw [hd]
  apply decide_eq_true
  have e1 : (⟨min t n, Nat.lt_succ_of_le (Nat.min_le_right t n)⟩ : Fin (n + 1)) =
      (⟨t, ht⟩ : Fin n).castSucc := Fin.ext (by simp; omega)
  have e2 : (⟨min (t + 1) n, Nat.lt_succ_of_le (Nat.min_le_right (t + 1) n)⟩ : Fin (n + 1)) =
      (⟨t, ht⟩ : Fin n).succ := Fin.ext (by simp; omega)
  rw [e1, e2]
  have h := hy ⟨t, ht⟩
  unfold d2_ed
  by_cases h1 : (⟨t, ht⟩ : Fin n) < r
  · rw [ite_eq_left h1]
    rcases d2_z2 (x ⟨t, ht⟩) with h0 | h0
    · rw [h0] at h
      exact Or.inl h
    · rw [h0] at h
      exact Or.inr h
  · rw [ite_eq_right h1]
    by_cases h2 : (⟨t, ht⟩ : Fin n) = r
    · rw [ite_eq_left h2]
      have hx1 : x ⟨t, ht⟩ = 1 := by rw [h2]; exact hr
      rw [hx1] at h
      exact h
    · rw [ite_eq_right h2]
      have hx0 : x ⟨t, ht⟩ = 0 := hz _ (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))
      rw [hx0] at h
      exact h

lemma d2_out_iff {n w : ℕ} (V : ℕ → Bool) (gf : Fin n → GOut (nb w)) (msT : T10 n w → ℕ)
    (r t : Fin n) :
    dnfVal V (outTerms n w gf msT (r, t)) = true ↔
      (t < r ∧ ∃ y y' : BV w, V ((gf r).2.2 t.val (eB w y)) = true ∧
        V ((gf r).2.2 (t.val + 1) (eB w y')) = true ∧ V (msT (t, (y, 0, y'))) = false) ∨
      (t = r ∧ V (gf r).1 = true) := by
  unfold outTerms
  by_cases h1 : t < r
  · have h2 : t ≠ r := ne_of_lt h1
    simp only [h1, ite_true, dnfVal, List.any_map, List.any_eq_true, Function.comp, true_and,
      h2, false_and, or_false]
    constructor
    · rintro ⟨yy, _, h⟩
      simp only [List.all_cons, List.all_nil, litVal, Bool.and_true, Bool.and_eq_true,
        beq_iff_eq] at h
      exact ⟨yy.1, yy.2, h.1, h.2.1, h.2.2⟩
    · rintro ⟨y, y', ha, hb, hc⟩
      refine ⟨(y, y'), mem_enumF _ _, ?_⟩
      simp only [List.all_cons, List.all_nil, litVal, Bool.and_true, Bool.and_eq_true,
        beq_iff_eq]
      exact ⟨ha, hb, hc⟩
  · by_cases h2 : t = r
    · subst h2
      simp [dnfVal, litVal]
    · simp [h1, h2, dnfVal]

lemma d2_out_cold {n w : ℕ} (V : ℕ → Bool) (gf : Fin n → GOut (nb w)) (msT : T10 n w → ℕ)
    (r t : Fin n) (hok : V (gf r).1 = false)
    (hsel : ∀ t ≤ n, ∀ a, V ((gf r).2.2 t a) = false) :
    dnfVal V (outTerms n w gf msT (r, t)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [d2_out_iff] at h
  rcases h with ⟨_, y, y', ha, _⟩ | ⟨_, h⟩
  · rw [hsel _ (le_of_lt t.isLt)] at ha
    cases ha
  · rw [hok] at h
    cases h

lemma d2_out_hot {n w : ℕ} (lam : Fin n → SubE w) (V : ℕ → Bool) (gf : Fin n → GOut (nb w))
    (msT : T10 n w → ℕ) (r t : Fin n) (q : ℕ → Fin (nb w)) (hok : V (gf r).1 = true)
    (hsel : ∀ t ≤ n, ∀ a, V ((gf r).2.2 t a) = decide (q t = a))
    (hms : ∀ t v, V (msT (t, v)) = decide (v ∈ lam t)) :
    dnfVal V (outTerms n w gf msT (r, t)) = true ↔
      (t < r ∧ ((eB w).symm (q t.val), (0 : ZMod 2), (eB w).symm (q (t.val + 1))) ∉ lam t) ∨
      t = r := by
  rw [d2_out_iff]
  constructor
  · rintro (⟨h1, y, y', ha, hb, hc⟩ | ⟨h2, _⟩)
    · left
      refine ⟨h1, ?_⟩
      rw [hsel _ (le_of_lt t.isLt)] at ha
      rw [hsel _ t.isLt] at hb
      have ea : q t.val = eB w y := of_decide_eq_true ha
      have eb : q (t.val + 1) = eB w y' := of_decide_eq_true hb
      rw [ea, eb, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rw [hms] at hc
      exact of_decide_eq_false hc
    · exact Or.inr h2
  · rintro (⟨h1, h⟩ | h2)
    · left
      refine ⟨h1, (eB w).symm (q t.val), (eB w).symm (q (t.val + 1)), ?_, ?_, ?_⟩
      · rw [hsel _ (le_of_lt t.isLt)]
        simp
      · rw [hsel _ t.isLt]
        simp
      · rw [hms]
        exact decide_eq_false h
    · exact Or.inr ⟨h2, hok⟩

lemma d2_row {n w : ℕ} (lam : Fin n → SubE w) (r : Fin n) (V : ℕ → Bool)
    (gf : Fin n → GOut (nb w)) (msT : T10 n w → ℕ)
    (ed : ℕ → Fin (nb w) → Fin (nb w) → Bool)
    (hok : V (gf r).1 = g_ok n (fun _ => true) (fun _ => true) ed)
    (hsel : ∀ t ≤ n, ∀ a, V ((gf r).2.2 t a) =
      g_sel n (fun _ => true) (fun _ => true) ed (n - t) a)
    (hms : ∀ t v, V (msT (t, v)) = decide (v ∈ lam t))
    (hed : ∀ t : Fin n, ∀ ka kb, ed t.val ka kb =
      decide (d2_ed lam r t ((eB w).symm ka) ((eB w).symm kb)))
    (o : Fin n → ZMod 2)
    (ho : ∀ t, o t = if dnfVal V (outTerms n w gf msT (r, t)) = true then 1 else 0) :
    ((∃ x ∈ m1_poss lam, x r = 1 ∧ ∀ t : Fin n, r < t → x t = 0) →
      o ∈ m1_poss lam ∧ o r = 1 ∧ ∀ t : Fin n, r < t → o t = 0) ∧
    ((¬ ∃ x ∈ m1_poss lam, x r = 1 ∧ ∀ t : Fin n, r < t → x t = 0) → o = 0) := by
  constructor
  · rintro ⟨x, hx, hr, hz⟩
    have hex := d2_legal_of_x lam r ed hed x hx hr hz
    obtain ⟨q, hq, hs⟩ := g_sel_of_exists n _ _ ed hex
    have hokt : V (gf r).1 = true := by
      rw [hok]
      exact (g_ok_iff n _ _ ed).mpr hex
    have hsel' : ∀ t ≤ n, ∀ a, V ((gf r).2.2 t a) = decide (q t = a) :=
      fun t ht a => by rw [hsel t ht a, hs t ht a]
    have ho' : o = d2_x lam r (fun t => (eB w).symm (q t)) := by
      funext t
      rw [ho t]
      have hiff := d2_out_hot lam V gf msT r t q hokt hsel' hms
      simp only [d2_x]
      by_cases h1 : t < r
      · rw [ite_eq_left h1]
        by_cases h3 : ((eB w).symm (q t.val), (0 : ZMod 2), (eB w).symm (q (t.val + 1))) ∈ lam t
        · rw [ite_eq_left h3, ite_eq_right]
          intro hc
          rcases hiff.mp hc with ⟨_, h⟩ | h
          · exact h h3
          · exact (ne_of_lt h1) h
        · rw [ite_eq_right h3, ite_eq_left (hiff.mpr (Or.inl ⟨h1, h3⟩))]
      · rw [ite_eq_right h1]
        by_cases h2 : t = r
        · rw [ite_eq_left h2, ite_eq_left (hiff.mpr (Or.inr h2))]
        · rw [ite_eq_right h2, ite_eq_right]
          intro hc
          rcases hiff.mp hc with ⟨h, _⟩ | h
          · exact h1 h
          · exact h2 h
    rw [ho']
    refine ⟨d2_x_mem lam r ed hed q hq, by simp [d2_x], fun t ht => ?_⟩
    simp [d2_x, not_lt_of_gt ht, ne_of_gt ht]
  · intro hno
    have hnl : ¬ ∃ q, g_legal n (fun _ => true) (fun _ => true) ed q := by
      rintro ⟨q, hq⟩
      refine hno ⟨d2_x lam r (fun t => (eB w).symm (q t)), d2_x_mem lam r ed hed q hq,
        by simp [d2_x], fun t ht => ?_⟩
      simp [d2_x, not_lt_of_gt ht, ne_of_gt ht]
    have hokf : V (gf r).1 = false := by
      rw [hok, Bool.eq_false_iff]
      intro h
      exact hnl ((g_ok_iff n _ _ ed).mp h)
    have hself : ∀ t ≤ n, ∀ a, V ((gf r).2.2 t a) = false := fun t ht a => by
      rw [hsel t ht a]
      exact g_sel_of_not n _ _ ed hnl (n - t) (Nat.sub_le n t) a
    funext t
    rw [ho t, d2_out_cold V gf msT r t hokf hself]
    simp

theorem sem_D2 (n s d w : ℕ) (hn : 0 < n) (start stop : Fin s → Bool)
    (edge : Fin n → Fin s → Fin s → Bool)
    (equation : Eqn n s d w) (V : ℕ → Bool)
    (hin : InOK n s d w start stop edge equation V) (hF : Facts n s d w V) :
    (∀ p : Fin (n + 1) → Fin s, (∀ t j, V ((r11 n s d w).2 (t, j)) = decide (p t = j)) →
      (∀ r : Fin n, (∃ x ∈ m1_poss (pathLam equation p), x r = 1 ∧ ∀ t : Fin n, r < t → x t = 0) →
        outM n s d w V r ∈ m1_poss (pathLam equation p) ∧ outM n s d w V r r = 1 ∧
          ∀ t : Fin n, r < t → outM n s d w V r t = 0) ∧
      (∀ r : Fin n, (¬ ∃ x ∈ m1_poss (pathLam equation p), x r = 1 ∧
        ∀ t : Fin n, r < t → x t = 0) → outM n s d w V r = 0)) ∧
    ((∀ t j, V ((r11 n s d w).2 (t, j)) = false) → ∀ i j, V ((r15 n s d w).2 (i, j)) = false) := by
  have hmem := (sem_D0 n s d w start stop edge equation V hin hF).1
  obtain ⟨h0, _, _, _, _, _, _, _, _, _, _, _, h12, h13, h14, h15⟩ := hF
  have hst : (fun a => V (trW n s d w a)) = fun _ => true := by
    funext a
    exact h0
  constructor
  · intro p hwalk
    have hms : ∀ t v, V ((r12 n s d w).2 (t, v)) = decide (v ∈ pathLam equation p t) :=
      fun t v => by
        rw [h12 (t, v)]
        exact d2_ms_hot equation p V _ _ hwalk hmem t v
    have hrow : ∀ r : Fin n,
        ((∃ x ∈ m1_poss (pathLam equation p), x r = 1 ∧ ∀ t : Fin n, r < t → x t = 0) →
          outM n s d w V r ∈ m1_poss (pathLam equation p) ∧ outM n s d w V r r = 1 ∧
            ∀ t : Fin n, r < t → outM n s d w V r t = 0) ∧
        ((¬ ∃ x ∈ m1_poss (pathLam equation p), x r = 1 ∧ ∀ t : Fin n, r < t → x t = 0) →
          outM n s d w V r = 0) := by
      intro r
      have hg := h14 r
      unfold GFacts at hg
      obtain ⟨g1, _, g3⟩ := hg
      rw [hst] at g1 g3
      refine d2_row (pathLam equation p) r V (r14 n s d w).2 (r12 n s d w).2
        (fun t a b => V (bedW n s d w r t a b)) g1 g3 hms (fun t ka kb => ?_)
        (outM n s d w V r) (fun t => ?_)
      · simp only [bedW, dite_eq_left t.isLt, Fin.eta]
        rw [h13]
        exact d2_be (pathLam equation p) V _ hms r t _ _
      · simp only [outM]
        rw [h15 (r, t)]
    exact ⟨fun r => (hrow r).1, fun r => (hrow r).2⟩
  · intro hw i j
    have hms : ∀ x, V ((r12 n s d w).2 x) = false := fun x => by
      rw [h12 x]
      exact d2_ms_cold V _ _ hw x
    have hbe : ∀ x, V ((r13 n s d w).2 x) = false := fun x => by
      rw [h13 x]
      exact d2_be_cold V _ hms x
    have hg := h14 i
    unfold GFacts at hg
    obtain ⟨g1, _, g3⟩ := hg
    have hnl : ¬ ∃ q, g_legal n (fun a => V (trW n s d w a)) (fun a => V (trW n s d w a))
        (fun t a b => V (bedW n s d w i t a b)) q := by
      rintro ⟨q, _, _, he⟩
      have h := he 0 hn
      simp only [bedW, dite_eq_left hn] at h
      rw [hbe] at h
      cases h
    have hokf : V ((r14 n s d w).2 i).1 = false := by
      rw [g1, Bool.eq_false_iff]
      intro h
      exact hnl ((g_ok_iff n _ _ _).mp h)
    have hself : ∀ t ≤ n, ∀ a, V (((r14 n s d w).2 i).2.2 t a) = false := fun t ht a => by
      rw [g3 t ht a]
      exact g_sel_of_not n _ _ _ hnl (n - t) (Nat.sub_le n t) a
    rw [h15 (i, j)]
    exact d2_out_cold V (r14 n s d w).2 (r12 n s d w).2 i j hokf hself

lemma bs_inp_s (n s d w k : ℕ) (hk : k < s) : s + k < inp n s d w := by
  unfold inp
  omega

lemma bs_inp_e (n s d w : ℕ) (t : Fin n) (i j : Fin s) :
    b_edgeIx s d w t i j < inp n s d w := by
  unfold inp
  exact b_edgeIx_lt t i j

lemma bs_dot_lt (n s d w : ℕ) (x : T1 n s d w) : ∀ u ∈ dotWs n s d w x, u < inp n s d w := by
  intro u hu
  unfold dotWs at hu
  simp only [List.mem_append, List.mem_map, List.mem_filter] at hu
  unfold inp
  rcases hu with (⟨k, _, rfl⟩ | hu) | ⟨k, _, rfl⟩
  · have h := b_ix_lt (d := d) (w := w) x.1 x.2.1 x.2.2.1 x.2.2.2.1 k.val
      (by have := k.isLt; omega)
    unfold eqBase
    exact h
  · split_ifs at hu
    · simp only [List.mem_singleton] at hu
      subst hu
      have h := b_ix_lt (d := d) (w := w) x.1 x.2.1 x.2.2.1 x.2.2.2.1 w (by omega)
      unfold eqBase
      exact h
    · simp at hu
  · have h := b_ix_lt (d := d) (w := w) x.1 x.2.1 x.2.2.1 x.2.2.2.1 (w + 1 + k.val)
      (by have := k.isLt; omega)
    unfold eqBase
    omega

lemma bs_dot_len (n s d w : ℕ) (x : T1 n s d w) : (dotWs n s d w x).length ≤ 2 * w + 1 := by
  have key : ∀ (l1 l2 l3 : List ℕ), l1.length ≤ w → l2.length ≤ 1 → l3.length ≤ w →
      (l1 ++ l2 ++ l3).length ≤ 2 * w + 1 := by
    intro l1 l2 l3 h1 h2 h3
    simp only [List.length_append]
    omega
  unfold dotWs
  apply key
  · rw [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  · split_ifs <;> simp
  · rw [List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)

lemma bs_fm_cost {ι : Type} [Finite ι] (p : ι → Bool) (f : ι → List (ℕ × Bool)) (M k : ℕ)
    (h : ∀ a, (f a).length ≤ M) (hk : 2 * M + 2 ≤ k) :
    dnfCost (((enumF ι).filter p).map f) ≤ 1 + Nat.card ι * k := by
  have h1 := dnfCost_le M (((enumF ι).filter p).map f) (fun t ht => by
    rcases List.mem_map.mp ht with ⟨a, _, rfl⟩
    exact h a)
  have h2 : (((enumF ι).filter p).map f).length ≤ Nat.card ι := by
    rw [List.length_map, ← length_enumF ι]
    exact List.length_filter_le _ _
  have h3 := Nat.mul_le_mul h2 hk
  omega

lemma bs_m_cost {ι : Type} [Finite ι] (f : ι → List (ℕ × Bool)) (M k : ℕ)
    (h : ∀ a, (f a).length ≤ M) (hk : 2 * M + 2 ≤ k) :
    dnfCost ((enumF ι).map f) ≤ 1 + Nat.card ι * k := by
  have h1 := dnfCost_le M ((enumF ι).map f) (fun t ht => by
    rcases List.mem_map.mp ht with ⟨a, _, rfl⟩
    exact h a)
  have h2 : ((enumF ι).map f).length ≤ Nat.card ι := by
    rw [List.length_map, length_enumF ι]
  have h3 := Nat.mul_le_mul h2 hk
  omega

lemma bs_0 (n s d w : ℕ) :
    (r0 n s d w).1.length ≤ 3 ∧ Good (inp n s d w) (r0 n s d w).1 ∧
    (r0 n s d w).2 () < inp n s d w + (r0 n s d w).1.length ∧
    ∀ gs', Extends (r0 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w →
      wireAt gs' x ((r0 n s d w).2 ()) = true := by
  unfold r0
  have h := mkDnfTab_spec (I := inp n s d w) 3 Unit (fun _ => [[]]) [] (good_nil _)
    (fun i t ht l hl => by
      simp only [List.mem_singleton] at ht
      subst ht
      simp at hl)
    (fun i => by simp [dnfCost])
  obtain ⟨e, l, g, v, q⟩ := h
  refine ⟨?_, g, v (), fun gs' he x hx => ?_⟩
  · have hc : Nat.card Unit = 1 := by simp
    rw [hc] at l
    simpa using l
  · have h1 := q gs' he x hx ()
    rw [h1]
    simp [dnfVal]

lemma bs_1 (n s d w : ℕ) :
    Extends (r0 n s d w).1 (r1 n s d w).1 ∧
    (r1 n s d w).1.length ≤ (r0 n s d w).1.length +
      Nat.card (T1 n s d w) * (4 * (2 * w + 1) + 1) ∧
    Good (inp n s d w) (r1 n s d w).1 ∧
    (∀ i, (r1 n s d w).2 i < inp n s d w + (r1 n s d w).1.length) ∧
    ∀ gs', Extends (r1 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r1 n s d w).2 i) = xorVal (wireAt gs' x) (dotWs n s d w i) := by
  obtain ⟨_, g0, _, _⟩ := bs_0 n s d w
  exact mkXorTab_spec (4 * (2 * w + 1) + 1) (T1 n s d w) (dotWs n s d w) (r0 n s d w).1 g0
    (fun i u hu => by
      have := bs_dot_lt n s d w i u hu
      omega)
    (fun i => by
      have := bs_dot_len n s d w i
      omega)

lemma bs_2 (n s d w : ℕ) :
    Extends (r1 n s d w).1 (r2 n s d w).1 ∧
    (r2 n s d w).1.length ≤ (r1 n s d w).1.length + Nat.card (T2 n s w) * (2 * d + 3) ∧
    Good (inp n s d w) (r2 n s d w).1 ∧
    (∀ i, (r2 n s d w).2 i < inp n s d w + (r2 n s d w).1.length) ∧
    ∀ gs', Extends (r2 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r2 n s d w).2 i) =
        dnfVal (wireAt gs' x) (memTerms n s d w (r1 n s d w).2 i) := by
  obtain ⟨_, _, g1, v1, _⟩ := bs_1 n s d w
  exact mkDnfTab_spec (2 * d + 3) (T2 n s w) (memTerms n s d w (r1 n s d w).2) (r1 n s d w).1 g1
    (fun i t ht l hl => by
      simp only [memTerms, List.mem_singleton] at ht
      subst ht
      rcases List.mem_map.mp hl with ⟨e, _, rfl⟩
      exact v1 _)
    (fun i => by
      simp only [memTerms, dnfCost, List.length_map, List.length_finRange]
      omega)

lemma bs_3 (n s d w : ℕ) :
    Extends (r2 n s d w).1 (r3 n s d w).1 ∧
    (r3 n s d w).1.length ≤ (r2 n s d w).1.length +
      Nat.card (T3 n s w) * (2 * Nat.card (EV w) + 3) ∧
    Good (inp n s d w) (r3 n s d w).1 ∧
    (∀ i, (r3 n s d w).2 i < inp n s d w + (r3 n s d w).1.length) ∧
    ∀ gs', Extends (r3 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r3 n s d w).2 i) =
        dnfVal (wireAt gs' x) (eqTerms n s w (r2 n s d w).2 i) := by
  obtain ⟨_, _, g2, v2, _⟩ := bs_2 n s d w
  exact mkDnfTab_spec (2 * Nat.card (EV w) + 3) (T3 n s w) (eqTerms n s w (r2 n s d w).2)
    (r2 n s d w).1 g2
    (fun i t ht l hl => by
      simp only [eqTerms, List.mem_singleton] at ht
      subst ht
      rcases List.mem_map.mp hl with ⟨e, _, rfl⟩
      exact v2 _)
    (fun i => by
      simp only [eqTerms, dnfCost, List.length_map, length_enumF]
      omega)

lemma bs_4 (n s d w : ℕ) :
    Extends (r3 n s d w).1 (r4 n s d w).1 ∧
    (r4 n s d w).1.length ≤ (r3 n s d w).1.length +
      Nat.card (T4 n s w) * (1 + Nat.card (SubE w) * 6) ∧
    Good (inp n s d w) (r4 n s d w).1 ∧
    (∀ i, (r4 n s d w).2 i < inp n s d w + (r4 n s d w).1.length) ∧
    ∀ gs', Extends (r4 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r4 n s d w).2 i) =
        dnfVal (wireAt gs' x) (edTerms n s d w (r3 n s d w).2 i) := by
  obtain ⟨_, _, g3, v3, _⟩ := bs_3 n s d w
  exact mkDnfTab_spec (1 + Nat.card (SubE w) * 6) (T4 n s w) (edTerms n s d w (r3 n s d w).2)
    (r3 n s d w).1 g3
    (fun i t ht l hl => by
      unfold edTerms at ht
      rcases List.mem_map.mp ht with ⟨c, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · have := bs_inp_e n s d w i.1 i.2.1.1 i.2.2.1
        dsimp only
        omega
      · exact v3 _)
    (fun i => bs_fm_cost _ _ 2 6 (fun a => by simp) (by norm_num))

lemma bs_5 (n s d w : ℕ) :
    Extends (r4 n s d w).1 (r5 n s d w).1 ∧
    (r5 n s d w).1.length ≤ (r4 n s d w).1.length + nn n s w * 5 ∧
    Good (inp n s d w) (r5 n s d w).1 ∧
    (∀ i, (r5 n s d w).2 i < inp n s d w + (r5 n s d w).1.length) ∧
    ∀ gs', Extends (r5 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r5 n s d w).2 i) = dnfVal (wireAt gs' x) (stTerms n s w i) := by
  obtain ⟨_, _, g4, _, _⟩ := bs_4 n s d w
  exact mkDnfTab_spec 5 (Node n s w) (stTerms n s w) (r4 n s d w).1 g4
    (fun i t ht l hl => by
      unfold stTerms at ht
      split_ifs at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        simp only [List.mem_singleton] at hl
        subst hl
        have := bs_inp_s n s d w i.1.val i.1.isLt
        dsimp only
        omega
      · simp at ht)
    (fun i => by
      unfold stTerms
      split_ifs <;> simp [dnfCost])

lemma bs_6 (n s d w : ℕ) :
    Extends (r5 n s d w).1 (r6 n s d w).1 ∧
    (r6 n s d w).1.length ≤ (r5 n s d w).1.length + gCost n (nn n s w) ∧
    Good (inp n s d w) (r6 n s d w).1 ∧
    GSem (inp n s d w) n (stW n s d w) (stW n s d w) (edW n s d w) (r6 n s d w).1
      (r6 n s d w).2 := by
  obtain ⟨_, _, _, v4, _⟩ := bs_4 n s d w
  obtain ⟨e5, _, g5, v5, _⟩ := bs_5 n s d w
  have l5 := extends_length_le e5
  exact mkG_spec (stW n s d w) (stW n s d w) (edW n s d w) g5 (fun a => v5 _) (fun a => v5 _)
    (fun t ht a b => by
      unfold edW
      simp only [ht, ↓reduceDIte]
      have := v4 (⟨t, ht⟩, (eN n s w).symm a, (eN n s w).symm b)
      omega)

lemma bs_7 (n s d w : ℕ) :
    Extends (r6 n s d w).1 (r7 n s d w).1 ∧
    (r7 n s d w).1.length ≤ (r6 n s d w).1.length +
      Nat.card (Fin (n + 1)) * (1 + nn n s w * 6) ∧
    Good (inp n s d w) (r7 n s d w).1 ∧
    (∀ i, (r7 n s d w).2 i < inp n s d w + (r7 n s d w).1.length) ∧
    ∀ gs', Extends (r7 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r7 n s d w).2 i) =
        dnfVal (wireAt gs' x) (okvTerms n s w (r6 n s d w).2.2.1 i) := by
  obtain ⟨_, _, g6, ⟨_, vr, _, _⟩⟩ := bs_6 n s d w
  exact mkDnfTab_spec (1 + nn n s w * 6) (Fin (n + 1)) (okvTerms n s w (r6 n s d w).2.2.1)
    (r6 n s d w).1 g6
    (fun i t ht l hl => by
      unfold okvTerms at ht
      rcases List.mem_map.mp ht with ⟨a, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact vr n le_rfl (eN n s w a)
      · have := bs_inp_s n s d w a.1.val a.1.isLt
        dsimp only
        omega)
    (fun i => bs_fm_cost _ _ 2 6 (fun a => by simp) (by norm_num))

lemma bs_8 (n s d w : ℕ) :
    Extends (r7 n s d w).1 (r8 n s d w).1 ∧
    (r8 n s d w).1.length ≤ (r7 n s d w).1.length +
      Nat.card (Fin (n + 1)) * (2 * (n + 2) + 3) ∧
    Good (inp n s d w) (r8 n s d w).1 ∧
    (∀ i, (r8 n s d w).2 i < inp n s d w + (r8 n s d w).1.length) ∧
    ∀ gs', Extends (r8 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r8 n s d w).2 i) =
        dnfVal (wireAt gs' x) (bestTerms n (r7 n s d w).2 i) := by
  obtain ⟨_, _, g7, v7, _⟩ := bs_7 n s d w
  have key : ∀ (a : ℕ × Bool) (L : List (ℕ × Bool)), L.length ≤ n + 1 →
      dnfCost [a :: L] ≤ 2 * (n + 2) + 3 := by
    intro a L hL
    simp only [dnfCost, List.length_cons]
    omega
  exact mkDnfTab_spec (2 * (n + 2) + 3) (Fin (n + 1)) (bestTerms n (r7 n s d w).2)
    (r7 n s d w).1 g7
    (fun i t ht l hl => by
      unfold bestTerms at ht
      simp only [List.mem_singleton] at ht
      subst ht
      rcases List.mem_cons.mp hl with rfl | hl
      · exact v7 _
      · rcases List.mem_map.mp hl with ⟨v', _, rfl⟩
        exact v7 _)
    (fun i => by
      unfold bestTerms
      apply key
      rw [List.length_map]
      exact (List.length_filter_le _ _).trans (by simp))

lemma bs_9 (n s d w : ℕ) :
    Extends (r8 n s d w).1 (r9 n s d w).1 ∧
    (r9 n s d w).1.length ≤ (r8 n s d w).1.length + nn n s w * 7 ∧
    Good (inp n s d w) (r9 n s d w).1 ∧
    (∀ i, (r9 n s d w).2 i < inp n s d w + (r9 n s d w).1.length) ∧
    ∀ gs', Extends (r9 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r9 n s d w).2 i) =
        dnfVal (wireAt gs' x) (spTerms n s w (r8 n s d w).2 i) := by
  obtain ⟨_, _, g8, v8, _⟩ := bs_8 n s d w
  exact mkDnfTab_spec 7 (Node n s w) (spTerms n s w (r8 n s d w).2) (r8 n s d w).1 g8
    (fun i t ht l hl => by
      unfold spTerms at ht
      split_ifs at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · have := bs_inp_s n s d w i.1.val i.1.isLt
          dsimp only
          omega
        · exact v8 _
      · simp at ht)
    (fun i => by
      unfold spTerms
      split_ifs <;> simp [dnfCost])

lemma bs_10 (n s d w : ℕ) :
    Extends (r9 n s d w).1 (r10 n s d w).1 ∧
    (r10 n s d w).1.length ≤ (r9 n s d w).1.length + gCost n (nn n s w) ∧
    Good (inp n s d w) (r10 n s d w).1 ∧
    GSem (inp n s d w) n (stW n s d w) (spW n s d w) (edW n s d w) (r10 n s d w).1
      (r10 n s d w).2 := by
  obtain ⟨_, _, _, v4, _⟩ := bs_4 n s d w
  obtain ⟨e5, _, _, v5, _⟩ := bs_5 n s d w
  obtain ⟨e6, _, _, _⟩ := bs_6 n s d w
  obtain ⟨e7, _, _, _, _⟩ := bs_7 n s d w
  obtain ⟨e8, _, _, _, _⟩ := bs_8 n s d w
  obtain ⟨e9, _, g9, v9, _⟩ := bs_9 n s d w
  have l5 := extends_length_le e5
  have l6 := extends_length_le e6
  have l7 := extends_length_le e7
  have l8 := extends_length_le e8
  have l9 := extends_length_le e9
  exact mkG_spec (stW n s d w) (spW n s d w) (edW n s d w) g9
    (fun a => by
      have := v5 ((eN n s w).symm a)
      unfold stW
      omega)
    (fun a => v9 _)
    (fun t ht a b => by
      unfold edW
      simp only [ht, ↓reduceDIte]
      have := v4 (⟨t, ht⟩, (eN n s w).symm a, (eN n s w).symm b)
      omega)

lemma bs_11 (n s d w : ℕ) :
    Extends (r10 n s d w).1 (r11 n s d w).1 ∧
    (r11 n s d w).1.length ≤ (r10 n s d w).1.length +
      Nat.card (T9 n s) * (1 + nn n s w * 4) ∧
    Good (inp n s d w) (r11 n s d w).1 ∧
    (∀ i, (r11 n s d w).2 i < inp n s d w + (r11 n s d w).1.length) ∧
    ∀ gs', Extends (r11 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r11 n s d w).2 i) =
        dnfVal (wireAt gs' x) (walkTerms n s w (r10 n s d w).2.2.2 i) := by
  obtain ⟨_, _, g10, ⟨_, _, vs, _⟩⟩ := bs_10 n s d w
  exact mkDnfTab_spec (1 + nn n s w * 4) (T9 n s) (walkTerms n s w (r10 n s d w).2.2.2)
    (r10 n s d w).1 g10
    (fun i t ht l hl => by
      unfold walkTerms at ht
      rcases List.mem_map.mp ht with ⟨a, _, rfl⟩
      simp only [List.mem_singleton] at hl
      subst hl
      exact vs i.1.val (Nat.lt_succ_iff.mp i.1.isLt) (eN n s w a))
    (fun i => bs_fm_cost _ _ 1 4 (fun a => by simp) (by norm_num))

lemma bs_len_2_11 (n s d w : ℕ) : (r2 n s d w).1.length ≤ (r11 n s d w).1.length := by
  have l3 := extends_length_le (bs_3 n s d w).1
  have l4 := extends_length_le (bs_4 n s d w).1
  have l5 := extends_length_le (bs_5 n s d w).1
  have l6 := extends_length_le (bs_6 n s d w).1
  have l7 := extends_length_le (bs_7 n s d w).1
  have l8 := extends_length_le (bs_8 n s d w).1
  have l9 := extends_length_le (bs_9 n s d w).1
  have l10 := extends_length_le (bs_10 n s d w).1
  have l11 := extends_length_le (bs_11 n s d w).1
  omega

lemma bs_12 (n s d w : ℕ) :
    Extends (r11 n s d w).1 (r12 n s d w).1 ∧
    (r12 n s d w).1.length ≤ (r11 n s d w).1.length +
      Nat.card (T10 n w) * (1 + s * s * 8) ∧
    Good (inp n s d w) (r12 n s d w).1 ∧
    (∀ i, (r12 n s d w).2 i < inp n s d w + (r12 n s d w).1.length) ∧
    ∀ gs', Extends (r12 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r12 n s d w).2 i) =
        dnfVal (wireAt gs' x) (msTerms n s w (r11 n s d w).2 (r2 n s d w).2 i) := by
  obtain ⟨_, _, _, v2, _⟩ := bs_2 n s d w
  obtain ⟨_, _, g11, v11, _⟩ := bs_11 n s d w
  have l := bs_len_2_11 n s d w
  exact mkDnfTab_spec (1 + s * s * 8) (T10 n w)
    (msTerms n s w (r11 n s d w).2 (r2 n s d w).2) (r11 n s d w).1 g11
    (fun i t ht l hl => by
      unfold msTerms at ht
      rcases List.mem_map.mp ht with ⟨ij, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact v11 _
      · exact v11 _
      · have := v2 (i.1, ij.1, ij.2, i.2)
        dsimp only
        omega)
    (fun i => by
      have hc : Nat.card (Fin s × Fin s) = s * s := by simp
      have h := bs_m_cost (ι := Fin s × Fin s) (fun ij =>
        [((r11 n s d w).2 (i.1.castSucc, ij.1), true), ((r11 n s d w).2 (i.1.succ, ij.2), true),
          ((r2 n s d w).2 (i.1, ij.1, ij.2, i.2), true)]) 3 8 (fun a => by simp) (by norm_num)
      rw [hc] at h
      exact h)

lemma bs_13 (n s d w : ℕ) :
    Extends (r12 n s d w).1 (r13 n s d w).1 ∧
    (r13 n s d w).1.length ≤ (r12 n s d w).1.length + Nat.card (T11 n w) * 9 ∧
    Good (inp n s d w) (r13 n s d w).1 ∧
    (∀ i, (r13 n s d w).2 i < inp n s d w + (r13 n s d w).1.length) ∧
    ∀ gs', Extends (r13 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r13 n s d w).2 i) =
        dnfVal (wireAt gs' x) (beTerms n w (r12 n s d w).2 i) := by
  obtain ⟨_, _, g12, v12, _⟩ := bs_12 n s d w
  exact mkDnfTab_spec 9 (T11 n w) (beTerms n w (r12 n s d w).2) (r12 n s d w).1 g12
    (fun i t ht l hl => by
      have key : ∃ y, t = [((r12 n s d w).2 y, true)] := by
        unfold beTerms at ht
        split_ifs at ht
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨_, rfl⟩
          · rcases List.mem_cons.mp ht with rfl | ht
            · exact ⟨_, rfl⟩
            · simp at ht
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨_, rfl⟩
          · simp at ht
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨_, rfl⟩
          · simp at ht
      obtain ⟨y, rfl⟩ := key
      simp only [List.mem_singleton] at hl
      subst hl
      exact v12 _)
    (fun i => by
      unfold beTerms
      split_ifs <;> simp [dnfCost])

lemma bs_len_0_13 (n s d w : ℕ) : (r0 n s d w).1.length ≤ (r13 n s d w).1.length := by
  have l1 := extends_length_le (bs_1 n s d w).1
  have l2 := extends_length_le (bs_2 n s d w).1
  have l3 := bs_len_2_11 n s d w
  have l12 := extends_length_le (bs_12 n s d w).1
  have l13 := extends_length_le (bs_13 n s d w).1
  omega

lemma bs_14 (n s d w : ℕ) :
    Extends (r13 n s d w).1 (r14 n s d w).1 ∧
    (r14 n s d w).1.length ≤ (r13 n s d w).1.length + n * gCost n (nb w) ∧
    Good (inp n s d w) (r14 n s d w).1 ∧
    ∀ r, GSem (inp n s d w) n (trW n s d w) (trW n s d w) (bedW n s d w r) (r14 n s d w).1
      ((r14 n s d w).2 r) := by
  obtain ⟨_, _, v0, _⟩ := bs_0 n s d w
  obtain ⟨_, _, g13, v13, _⟩ := bs_13 n s d w
  have l0 := bs_len_0_13 n s d w
  exact mkFam_spec (I := inp n s d w) (gCost n (nb w)) n
    (fun r => mkG (inp n s d w) n (nb w) (trW n s d w) (trW n s d w) (bedW n s d w r))
    (fun r gs o => GSem (inp n s d w) n (trW n s d w) (trW n s d w) (bedW n s d w r) gs o)
    (r13 n s d w).1 g13
    (fun i gs1 gs2 a he h => GSem_mono he h)
    (fun i gs1 hG1 he => by
      have l := extends_length_le he
      have ht : ∀ a, trW n s d w a < inp n s d w + gs1.length := by
        intro a
        show (r0 n s d w).2 () < _
        omega
      exact mkG_spec (trW n s d w) (trW n s d w) (bedW n s d w i) hG1 ht ht
        (fun t htn a b => by
          unfold bedW
          simp only [htn, ↓reduceDIte]
          have := v13 (i, ⟨t, htn⟩, (eB w).symm a, (eB w).symm b)
          omega))

lemma bs_15 (n s d w : ℕ) :
    Extends (r14 n s d w).1 (r15 n s d w).1 ∧
    (r15 n s d w).1.length ≤ (r14 n s d w).1.length +
      Nat.card (T12 n) * (1 + nb w * nb w * 8) ∧
    Good (inp n s d w) (r15 n s d w).1 ∧
    (∀ i, (r15 n s d w).2 i < inp n s d w + (r15 n s d w).1.length) ∧
    ∀ gs', Extends (r15 n s d w).1 gs' → ∀ x : List Bool, x.length = inp n s d w → ∀ i,
      wireAt gs' x ((r15 n s d w).2 i) =
        dnfVal (wireAt gs' x) (outTerms n w (r14 n s d w).2 (r12 n s d w).2 i) := by
  obtain ⟨_, _, _, v12, _⟩ := bs_12 n s d w
  obtain ⟨e13, _, _, _, _⟩ := bs_13 n s d w
  obtain ⟨e14, _, g14, v14⟩ := bs_14 n s d w
  have l13 := extends_length_le e13
  have l14 := extends_length_le e14
  have hpos : 0 < nb w := Nat.card_pos
  have hpos2 : 1 ≤ nb w * nb w := Nat.mul_pos hpos hpos
  exact mkDnfTab_spec (1 + nb w * nb w * 8) (T12 n)
    (outTerms n w (r14 n s d w).2 (r12 n s d w).2) (r14 n s d w).1 g14
    (fun i t ht l hl => by
      unfold outTerms at ht
      split_ifs at ht
      · rcases List.mem_map.mp ht with ⟨yy, _, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact (v14 i.1).2.2.1 i.2.val (le_of_lt i.2.isLt) _
        · exact (v14 i.1).2.2.1 (i.2.val + 1) i.2.isLt _
        · have := v12 (i.2, (yy.1, 0, yy.2))
          dsimp only
          omega
      · simp only [List.mem_singleton] at ht
        subst ht
        simp only [List.mem_singleton] at hl
        subst hl
        exact (v14 i.1).1
      · simp at ht)
    (fun i => by
      unfold outTerms
      split_ifs
      · have hc : Nat.card (BV w × BV w) = nb w * nb w := by
          rw [Nat.card_prod]
          rfl
        have h := bs_m_cost (ι := BV w × BV w) (fun yy =>
          [(((r14 n s d w).2 i.1).2.2 i.2.val (eB w yy.1), true),
            (((r14 n s d w).2 i.1).2.2 (i.2.val + 1) (eB w yy.2), true),
            ((r12 n s d w).2 (i.2, (yy.1, 0, yy.2)), false)]) 3 8 (fun a => by simp)
          (by norm_num)
        rw [hc] at h
        exact h
      · simp only [dnfCost, List.length_cons, List.length_nil]
        omega
      · simp only [dnfCost]
        omega)

theorem build_spec (n s d w : ℕ) (_hn : 0 < n) (_hs : 0 < s) :
    Good (inp n s d w) (r15 n s d w).1 ∧ (r15 n s d w).1.length ≤ sizeExpr n s d w ∧
    (r10 n s d w).2.1 < inp n s d w + (r15 n s d w).1.length ∧
    (∀ x, (r11 n s d w).2 x < inp n s d w + (r15 n s d w).1.length) ∧
    (∀ x, (r15 n s d w).2 x < inp n s d w + (r15 n s d w).1.length) ∧
    ∀ xs : List Bool, xs.length = inp n s d w → Facts n s d w (wireAt (r15 n s d w).1 xs) := by
  obtain ⟨l0, _, _, q0⟩ := bs_0 n s d w
  obtain ⟨e1, l1, _, _, q1⟩ := bs_1 n s d w
  obtain ⟨e2, l2, _, _, q2⟩ := bs_2 n s d w
  obtain ⟨e3, l3, _, _, q3⟩ := bs_3 n s d w
  obtain ⟨e4, l4, _, _, q4⟩ := bs_4 n s d w
  obtain ⟨e5, l5, _, _, q5⟩ := bs_5 n s d w
  obtain ⟨e6, l6, _, ⟨_, _, _, q6⟩⟩ := bs_6 n s d w
  obtain ⟨e7, l7, _, _, q7⟩ := bs_7 n s d w
  obtain ⟨e8, l8, _, _, q8⟩ := bs_8 n s d w
  obtain ⟨e9, l9, _, _, q9⟩ := bs_9 n s d w
  obtain ⟨e10, l10, _, ⟨vok, _, _, q10⟩⟩ := bs_10 n s d w
  obtain ⟨e11, l11, _, v11, q11⟩ := bs_11 n s d w
  obtain ⟨e12, l12, _, _, q12⟩ := bs_12 n s d w
  obtain ⟨e13, l13, _, _, q13⟩ := bs_13 n s d w
  obtain ⟨e14, l14, _, q14⟩ := bs_14 n s d w
  obtain ⟨e15, l15, g15, v15, q15⟩ := bs_15 n s d w
  have c7 : Nat.card (Fin (n + 1)) = n + 1 := by simp
  rw [c7] at l7 l8
  have E15 := extends_refl (r15 n s d w).1
  have E14 := extends_trans e15 E15
  have E13 := extends_trans e14 E14
  have E12 := extends_trans e13 E13
  have E11 := extends_trans e12 E12
  have E10 := extends_trans e11 E11
  have E9 := extends_trans e10 E10
  have E8 := extends_trans e9 E9
  have E7 := extends_trans e8 E8
  have E6 := extends_trans e7 E7
  have E5 := extends_trans e6 E6
  have E4 := extends_trans e5 E5
  have E3 := extends_trans e4 E4
  have E2 := extends_trans e3 E3
  have E1 := extends_trans e2 E2
  have E0 := extends_trans e1 E1
  have L10 := extends_length_le E10
  have L11 := extends_length_le E11
  refine ⟨g15, ?_, by omega, fun x => by have := v11 x; omega, v15, fun xs hx => ?_⟩
  · unfold sizeExpr
    omega
  · exact ⟨q0 _ E0 xs hx, q1 _ E1 xs hx, q2 _ E2 xs hx, q3 _ E3 xs hx, q4 _ E4 xs hx,
      q5 _ E5 xs hx, q6 _ E6 xs hx, q7 _ E7 xs hx, q8 _ E8 xs hx, q9 _ E9 xs hx,
      q10 _ E10 xs hx, q11 _ E11 xs hx, q12 _ E12 xs hx, q13 _ E13 xs hx,
      fun r => (q14 r).2.2.2 _ E14 xs hx, q15 _ E15 xs hx⟩

lemma sz_mono (P Q a b : ℕ) (hP : 1 ≤ P) (hQ : 1 ≤ Q) (ha : a ≤ 5) (hb : b ≤ 8) :
    P ^ a * Q ^ b ≤ P ^ 5 * Q ^ 8 :=
  Nat.mul_le_mul (Nat.pow_le_pow_right hP ha) (Nat.pow_le_pow_right hQ hb)

lemma sz_arith (n s d w P Q cE cSE nnv nbv : ℕ) (hn0 : 0 < n) (hs0 : 0 < s)
    (hP : P = n + s + d + w + 6) (hQ : 1 ≤ Q)
    (hcE : cE ≤ Q) (hcSE : cSE ≤ Q ^ 4) (hnn : nnv ≤ P ^ 2 * Q ^ 2) (hnb : nbv ≤ Q) :
    3 + n * (s * (s * (d * cE))) * (4 * (2 * w + 1) + 1) + n * (s * (s * cE)) * (2 * d + 3) +
    n * (s * (s * cSE)) * (2 * cE + 3) + n * (nnv * nnv) * (1 + cSE * 6) + nnv * 5 +
    30 * (n + 1) * (nnv + 1) ^ 2 + (n + 1) * (1 + nnv * 6) + (n + 1) * (2 * (n + 2) + 3) +
    nnv * 7 + 30 * (n + 1) * (nnv + 1) ^ 2 + (n + 1) * s * (1 + nnv * 4) +
    n * cE * (1 + s * s * 8) + n * (n * (nbv * nbv)) * 9 + n * (30 * (n + 1) * (nbv + 1) ^ 2) +
    n * n * (1 + nbv * nbv * 8) ≤ P ^ 12 * Q ^ 12 := by
  have hn : n ≤ P := by omega
  have hs : s ≤ P := by omega
  have hd : d ≤ P := by omega
  have hn1 : n + 1 ≤ P := by omega
  have h8 : 4 * (2 * w + 1) + 1 ≤ 8 * P := by omega
  have h2d : 2 * d + 3 ≤ 2 * P := by omega
  have h2n : 2 * (n + 2) + 3 ≤ 2 * P := by omega
  have hP1 : 1 ≤ P := by omega
  have hP8 : 8 ≤ P := by omega
  have hQ4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQ
  have hX1 : 1 ≤ P ^ 2 * Q ^ 2 :=
    Nat.mul_pos (Nat.one_le_pow _ _ hP1) (Nat.one_le_pow _ _ hQ)
  have hQQ : 1 ≤ Q * Q := Nat.mul_pos hQ hQ
  have hPP : 1 ≤ P * P := Nat.mul_pos hP1 hP1
  have hM1 : 1 ≤ P ^ 5 * Q ^ 8 :=
    Nat.mul_pos (Nat.one_le_pow _ _ hP1) (Nat.one_le_pow _ _ hQ)
  have hss : s * s ≤ P * P := Nat.mul_le_mul hs hs
  have hbb : nbv * nbv ≤ Q * Q := Nat.mul_le_mul hnb hnb
  have a5 : 1 + cSE * 6 ≤ 7 * Q ^ 4 := by linarith
  have a4 : 2 * cE + 3 ≤ 5 * Q := by linarith
  have a7 : nnv + 1 ≤ 2 * (P ^ 2 * Q ^ 2) := by linarith
  have a8 : 1 + nnv * 6 ≤ 7 * (P ^ 2 * Q ^ 2) := by linarith
  have a12 : 1 + nnv * 4 ≤ 5 * (P ^ 2 * Q ^ 2) := by linarith
  have a13 : 1 + s * s * 8 ≤ 9 * (P * P) := by linarith
  have a15 : nbv + 1 ≤ 2 * Q := by linarith
  have a16 : 1 + nbv * nbv * 8 ≤ 9 * (Q * Q) := by linarith
  have mo := fun a b (ha : a ≤ 5) (hb : b ≤ 8) => sz_mono P Q a b hP1 hQ ha hb
  have t1 : 3 ≤ 3 * (P ^ 5 * Q ^ 8) := by linarith
  have t2 : n * (s * (s * (d * cE))) * (4 * (2 * w + 1) + 1) ≤ 8 * (P ^ 5 * Q ^ 8) := by
    calc n * (s * (s * (d * cE))) * (4 * (2 * w + 1) + 1)
        ≤ P * (P * (P * (P * Q))) * (8 * P) :=
          Nat.mul_le_mul (Nat.mul_le_mul hn (Nat.mul_le_mul hs (Nat.mul_le_mul hs
            (Nat.mul_le_mul hd hcE)))) h8
      _ = 8 * (P ^ 5 * Q ^ 1) := by ring
      _ ≤ 8 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 5 1 (by omega) (by omega))
  have t3 : n * (s * (s * cE)) * (2 * d + 3) ≤ 2 * (P ^ 5 * Q ^ 8) := by
    calc n * (s * (s * cE)) * (2 * d + 3)
        ≤ P * (P * (P * Q)) * (2 * P) :=
          Nat.mul_le_mul (Nat.mul_le_mul hn (Nat.mul_le_mul hs (Nat.mul_le_mul hs hcE))) h2d
      _ = 2 * (P ^ 4 * Q ^ 1) := by ring
      _ ≤ 2 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 4 1 (by omega) (by omega))
  have t4 : n * (s * (s * cSE)) * (2 * cE + 3) ≤ 5 * (P ^ 5 * Q ^ 8) := by
    calc n * (s * (s * cSE)) * (2 * cE + 3)
        ≤ P * (P * (P * Q ^ 4)) * (5 * Q) :=
          Nat.mul_le_mul (Nat.mul_le_mul hn (Nat.mul_le_mul hs (Nat.mul_le_mul hs hcSE))) a4
      _ = 5 * (P ^ 3 * Q ^ 5) := by ring
      _ ≤ 5 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 3 5 (by omega) (by omega))
  have t5 : n * (nnv * nnv) * (1 + cSE * 6) ≤ 7 * (P ^ 5 * Q ^ 8) := by
    calc n * (nnv * nnv) * (1 + cSE * 6)
        ≤ P * ((P ^ 2 * Q ^ 2) * (P ^ 2 * Q ^ 2)) * (7 * Q ^ 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul hn (Nat.mul_le_mul hnn hnn)) a5
      _ = 7 * (P ^ 5 * Q ^ 8) := by ring
  have t6 : nnv * 5 ≤ 5 * (P ^ 5 * Q ^ 8) := by
    calc nnv * 5 ≤ 5 * (P ^ 2 * Q ^ 2) := by linarith
      _ ≤ 5 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 2 2 (by omega) (by omega))
  have t7 : 30 * (n + 1) * (nnv + 1) ^ 2 ≤ 120 * (P ^ 5 * Q ^ 8) := by
    calc 30 * (n + 1) * (nnv + 1) ^ 2
        ≤ 30 * P * (2 * (P ^ 2 * Q ^ 2)) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hn1) (Nat.pow_le_pow_left a7 2)
      _ = 120 * (P ^ 5 * Q ^ 4) := by ring
      _ ≤ 120 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 5 4 (by omega) (by omega))
  have t8 : (n + 1) * (1 + nnv * 6) ≤ 7 * (P ^ 5 * Q ^ 8) := by
    calc (n + 1) * (1 + nnv * 6) ≤ P * (7 * (P ^ 2 * Q ^ 2)) := Nat.mul_le_mul hn1 a8
      _ = 7 * (P ^ 3 * Q ^ 2) := by ring
      _ ≤ 7 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 3 2 (by omega) (by omega))
  have t9 : (n + 1) * (2 * (n + 2) + 3) ≤ 2 * (P ^ 5 * Q ^ 8) := by
    calc (n + 1) * (2 * (n + 2) + 3) ≤ P * (2 * P) := Nat.mul_le_mul hn1 h2n
      _ = 2 * (P ^ 2 * Q ^ 0) := by ring
      _ ≤ 2 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 2 0 (by omega) (by omega))
  have t10 : nnv * 7 ≤ 7 * (P ^ 5 * Q ^ 8) := by
    calc nnv * 7 ≤ 7 * (P ^ 2 * Q ^ 2) := by linarith
      _ ≤ 7 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 2 2 (by omega) (by omega))
  have t12 : (n + 1) * s * (1 + nnv * 4) ≤ 5 * (P ^ 5 * Q ^ 8) := by
    calc (n + 1) * s * (1 + nnv * 4) ≤ P * P * (5 * (P ^ 2 * Q ^ 2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul hn1 hs) a12
      _ = 5 * (P ^ 4 * Q ^ 2) := by ring
      _ ≤ 5 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 4 2 (by omega) (by omega))
  have t13 : n * cE * (1 + s * s * 8) ≤ 9 * (P ^ 5 * Q ^ 8) := by
    calc n * cE * (1 + s * s * 8) ≤ P * Q * (9 * (P * P)) :=
          Nat.mul_le_mul (Nat.mul_le_mul hn hcE) a13
      _ = 9 * (P ^ 3 * Q ^ 1) := by ring
      _ ≤ 9 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 3 1 (by omega) (by omega))
  have t14 : n * (n * (nbv * nbv)) * 9 ≤ 9 * (P ^ 5 * Q ^ 8) := by
    calc n * (n * (nbv * nbv)) * 9 ≤ P * (P * (Q * Q)) * 9 :=
          Nat.mul_le_mul (Nat.mul_le_mul hn (Nat.mul_le_mul hn hbb)) le_rfl
      _ = 9 * (P ^ 2 * Q ^ 2) := by ring
      _ ≤ 9 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 2 2 (by omega) (by omega))
  have t15 : n * (30 * (n + 1) * (nbv + 1) ^ 2) ≤ 120 * (P ^ 5 * Q ^ 8) := by
    calc n * (30 * (n + 1) * (nbv + 1) ^ 2) ≤ P * (30 * P * (2 * Q) ^ 2) :=
          Nat.mul_le_mul hn (Nat.mul_le_mul (Nat.mul_le_mul_left _ hn1)
            (Nat.pow_le_pow_left a15 2))
      _ = 120 * (P ^ 2 * Q ^ 2) := by ring
      _ ≤ 120 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 2 2 (by omega) (by omega))
  have t16 : n * n * (1 + nbv * nbv * 8) ≤ 9 * (P ^ 5 * Q ^ 8) := by
    calc n * n * (1 + nbv * nbv * 8) ≤ P * P * (9 * (Q * Q)) :=
          Nat.mul_le_mul (Nat.mul_le_mul hn hn) a16
      _ = 9 * (P ^ 2 * Q ^ 2) := by ring
      _ ≤ 9 * (P ^ 5 * Q ^ 8) := Nat.mul_le_mul_left _ (mo 2 2 (by omega) (by omega))
  have hfin : 438 * (P ^ 5 * Q ^ 8) ≤ P ^ 12 * Q ^ 12 := by
    have h7 : 438 ≤ P ^ 7 := by
      calc 438 ≤ 8 ^ 7 := by norm_num
        _ ≤ P ^ 7 := Nat.pow_le_pow_left hP8 7
    have hq : Q ^ 8 ≤ Q ^ 12 := Nat.pow_le_pow_right hQ (by omega)
    calc 438 * (P ^ 5 * Q ^ 8) ≤ P ^ 7 * (P ^ 5 * Q ^ 12) :=
          Nat.mul_le_mul h7 (Nat.mul_le_mul_left _ hq)
      _ = P ^ 12 * Q ^ 12 := by ring
  linarith

lemma sz_cardB (w : ℕ) : Nat.card (BV w) = 2 ^ w := by
  simp [Nat.card_eq_fintype_card]

lemma sz_cardE (w : ℕ) : Nat.card (EV w) = 2 ^ (2 * w + 1) := by
  rw [Nat.card_prod, Nat.card_prod, sz_cardB]
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  ring

lemma sz_nn (n s w : ℕ) :
    nn n s w = s * (Nat.card (SubB w) * (Nat.card (SubB w) * (n + w + 1))) := by
  unfold nn
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin]

theorem size_le (n s d w : ℕ) (hn : 0 < n) (hs : 0 < s) :
    sizeExpr n s d w ≤ 2^(12*(w+2)^2)*(n+s+d+w+6)^12 := by
  have hQ : 1 ≤ 2 ^ ((w + 2) ^ 2) := Nat.one_le_two_pow
  have hcE : Nat.card (EV w) ≤ 2 ^ ((w + 2) ^ 2) := by
    rw [sz_cardE]
    exact b_pow_a w
  have hcSE : Nat.card (SubE w) ≤ (2 ^ ((w + 2) ^ 2)) ^ 4 :=
    le_trans (m2_count_E w) (b_pow_c w)
  have hcSB : Nat.card (SubB w) ≤ 2 ^ ((w + 2) ^ 2) := le_trans (m2_count_B w) (b_pow_b w)
  have hnb : nb w ≤ 2 ^ ((w + 2) ^ 2) := by
    unfold nb
    rw [sz_cardB]
    exact le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (b_pow_a w)
  have hnn : nn n s w ≤ (n + s + d + w + 6) ^ 2 * (2 ^ ((w + 2) ^ 2)) ^ 2 := by
    rw [sz_nn]
    calc s * (Nat.card (SubB w) * (Nat.card (SubB w) * (n + w + 1)))
        ≤ (n + s + d + w + 6) * (2 ^ ((w + 2) ^ 2) * (2 ^ ((w + 2) ^ 2) * (n + s + d + w + 6))) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul hcSB (Nat.mul_le_mul hcSB (by omega)))
      _ = (n + s + d + w + 6) ^ 2 * (2 ^ ((w + 2) ^ 2)) ^ 2 := by ring
  have h1 : Nat.card (T1 n s d w) = n * (s * (s * (d * Nat.card (EV w)))) := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod]
    simp only [Nat.card_fin]
  have h2 : Nat.card (T2 n s w) = n * (s * (s * Nat.card (EV w))) := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod]
    simp only [Nat.card_fin]
  have h3 : Nat.card (T3 n s w) = n * (s * (s * Nat.card (SubE w))) := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod]
    simp only [Nat.card_fin]
  have h4 : Nat.card (T4 n s w) = n * (nn n s w * nn n s w) := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_fin]
    rfl
  have h9 : Nat.card (T9 n s) = (n + 1) * s := by
    rw [Nat.card_prod, Nat.card_fin, Nat.card_fin]
  have h10 : Nat.card (T10 n w) = n * Nat.card (EV w) := by
    rw [Nat.card_prod, Nat.card_fin]
  have h11 : Nat.card (T11 n w) = n * (n * (nb w * nb w)) := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_fin]
    rfl
  have h12 : Nat.card (T12 n) = n * n := by
    rw [Nat.card_prod, Nat.card_fin]
  have key := sz_arith n s d w (n + s + d + w + 6) (2 ^ ((w + 2) ^ 2)) (Nat.card (EV w))
    (Nat.card (SubE w)) (nn n s w) (nb w) hn hs rfl hQ hcE hcSE hnn hnb
  unfold sizeExpr gCost
  rw [h1, h2, h3, h4, h9, h10, h11, h12]
  rw [← b_pow_d w]
  exact le_trans key (le_of_eq (Nat.mul_comm _ _))

theorem final_core (n s d w : ℕ) (hn : 0 < n) (hs : 0 < s) (start stop : Fin s → Bool)
    (edge : Fin n → Fin s → Fin s → Bool) (equation : Eqn n s d w) :
    Facts n s d w (wireAt (r15 n s d w).1 (b_bits n s d w start stop edge equation)) ∧
    InOK n s d w start stop edge equation
      (wireAt (r15 n s d w).1 (b_bits n s d w start stop edge equation)) := by
  obtain ⟨_, _, _, _, _, hfacts⟩ := build_spec n s d w hn hs
  refine ⟨hfacts _ (b_length n s d w start stop edge equation), fun u hu => ?_⟩
  exact wireAt_input _ _ (by rw [b_length]; exact hu)

theorem poss_iff {n s d w : ℕ} (equation : Eqn n s d w) (p : Fin (n + 1) → Fin s)
    (x : Fin n → ZMod 2) :
    (∃ y : Fin (n + 1) → (Fin w → ZMod 2), ∀ (t : Fin n) (j : Fin d),
      dotProduct (equation t (p t.castSucc) (p t.succ) j).1 (y t.castSucc) +
        (equation t (p t.castSucc) (p t.succ) j).2.1 * x t +
        dotProduct (equation t (p t.castSucc) (p t.succ) j).2.2 (y t.succ) = 0) ↔
    x ∈ m1_poss (pathLam equation p) := by
  rw [m1_mem_poss]
  rfl


theorem lib807 : (∀ (n s d w : Nat) (hn : 0 < n) (hs : 0 < s),
  let F := ZMod 2
  let B := Fin w → F
  let W := Fin n → F
  let inputs := 2*s + n*s*s*(1+d*(2*w+1))
  ∃ (A : PEqualNP.CircuitLowerBounds.Circuit) (ok : Fin (inputs+A.size))
    (walk : Fin (n+1) → Fin s → Fin (inputs+A.size))
    (basisWire : Fin n → Fin n → Fin (inputs+A.size)),
    PEqualNP.MetaComplexity.FanInTwo A ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs A ∧
    A.output = ok.val ∧ A.size ≤ 2^(12*(w+2)^2)*(n+s+d+w+6)^12 ∧
    ∀ (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
      (equation : Fin n → Fin s → Fin s → Fin d → B × F × B),
      let pack := fun y : B => List.ofFn (fun i : Fin w => decide (y i ≠ 0))
      let bits := List.ofFn start ++ List.ofFn stop ++
        (List.finRange n).flatMap (fun t => (List.finRange s).flatMap (fun i =>
          (List.finRange s).flatMap (fun j => [edge t i j] ++
            (List.finRange d).flatMap (fun e =>
              let coeff := equation t i j e
              pack coeff.1 ++ [decide (coeff.2.1 ≠ 0)] ++ pack coeff.2.2))))
      let wire := fun i : Fin (inputs+A.size) => (A.wires bits).getD i.val false
      let out := fun i j => (if wire (basisWire i j) then 1 else 0 : F)
      let K := Submodule.span F (Set.range out)
      let nz := (Finset.univ : Finset (Fin n)).filter (fun i => out i ≠ 0)
      let legal := fun p : Fin (n+1) → Fin s =>
        start (p 0) = true ∧ stop (p (Fin.last n)) = true ∧
          ∀ t : Fin n, edge t (p t.castSucc) (p t.succ) = true
      let possible := fun (p : Fin (n+1) → Fin s) (x : W) =>
        ∃ y : Fin (n+1) → B, ∀ (t : Fin n) (j : Fin d),
          let coeff := equation t (p t.castSucc) (p t.succ) j
          dotProduct coeff.1 (y t.castSucc) + coeff.2.1*x t + dotProduct coeff.2.2 (y t.succ) = 0
      (wire ok = true ↔ ∃ p, legal p) ∧
        (wire ok = true → ∃ p, legal p ∧
          (∀ t j, wire (walk t j) = decide (p t = j)) ∧
          (∀ x : W, x ∈ K ↔ possible p x) ∧ LinearIndependent F (fun i : ↥nz => out i.val) ∧
          (∀ q, legal q → Nat.card {x : W // possible q x} ≤ 2^(Module.finrank F K))) ∧
        (wire ok = false → (∀ i, out i = 0) ∧ ∀ t j, wire (walk t j) = false)) := by
  intro n s d w hn hs F B W inputs
  obtain ⟨hGood, hlen, hok, hwalk, hout, -⟩ :=
    PEqualNP.Outside.L_meta_29723.build_spec n s d w hn hs
  refine ⟨⟨(PEqualNP.Outside.L_meta_29723.r15 n s d w).1,
      (PEqualNP.Outside.L_meta_29723.r10 n s d w).2.1⟩,
    ⟨(PEqualNP.Outside.L_meta_29723.r10 n s d w).2.1, hok⟩,
    fun t j => ⟨(PEqualNP.Outside.L_meta_29723.r11 n s d w).2 (t, j), hwalk _⟩,
    fun i j => ⟨(PEqualNP.Outside.L_meta_29723.r15 n s d w).2 (i, j), hout _⟩,
    hGood.1, hGood.2, rfl,
    le_trans hlen (PEqualNP.Outside.L_meta_29723.size_le n s d w hn hs), ?_⟩
  intro start stop edge equation pack bits wire out K nz legal possible
  obtain ⟨hF, hin⟩ :=
    PEqualNP.Outside.L_meta_29723.final_core n s d w hn hs start stop edge equation
  obtain ⟨h1, h2, h3⟩ :=
    PEqualNP.Outside.L_meta_29723.sem_D1 n s d w start stop edge equation _ hin hF
  obtain ⟨h4, h5⟩ :=
    PEqualNP.Outside.L_meta_29723.sem_D2 n s d w hn start stop edge equation _ hin hF
  refine ⟨h1, ?_, ?_⟩
  · intro hokv
    obtain ⟨p, hp, hw, hopt⟩ := h2 hokv
    obtain ⟨hb1, hb0⟩ := h4 p hw
    have hK : K = PEqualNP.Outside.L_meta_29723.m1_poss
        (PEqualNP.Outside.L_meta_29723.pathLam equation p) :=
      (PEqualNP.Outside.L_meta_29723.m2_basis _ _ hb1 hb0).1
    refine ⟨p, hp, hw, ?_, ?_, ?_⟩
    · intro x
      rw [hK]
      exact (PEqualNP.Outside.L_meta_29723.poss_iff equation p x).symm
    · exact (PEqualNP.Outside.L_meta_29723.m2_basis _ _ hb1 hb0).2
    · intro q hq
      have hc : Nat.card {x : W // possible q x} =
          Nat.card {x : Fin n → ZMod 2 // x ∈ PEqualNP.Outside.L_meta_29723.m1_poss
            (PEqualNP.Outside.L_meta_29723.pathLam equation q)} :=
        Nat.card_congr (Equiv.subtypeEquivRight
          (fun x => PEqualNP.Outside.L_meta_29723.poss_iff equation q x))
      rw [hc, PEqualNP.Outside.L_meta_29723.m2_card_sub, hK]
      exact Nat.pow_le_pow_right (by norm_num) (hopt q hq)
  · intro hokv
    have hwf := h3 hokv
    refine ⟨fun i => ?_, hwf⟩
    funext j
    have := h5 hwf i j
    change (if PEqualNP.Outside.L_meta_29723.wireAt (PEqualNP.Outside.L_meta_29723.r15 n s d w).1
      (PEqualNP.Outside.L_meta_29723.b_bits n s d w start stop edge equation)
      ((PEqualNP.Outside.L_meta_29723.r15 n s d w).2 (i, j)) = true then (1 : ZMod 2) else 0) = 0
    rw [this]
    rfl

end L807

section Prelude

open PEqualNP.CircuitLowerBounds

def ix {k : ℕ} (hk : 0 < k) (s : ℕ) : Fin k := ⟨s % k, Nat.mod_lt _ hk⟩

def rot {k : ℕ} (hk : 0 < k) (s : ℕ) (w : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  w (ix hk (j.val+k-s % k))

def run {k : ℕ} (hk : 0 < k) (col : Bool) (name c key : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  let d := if col then 2 else 1
  let z := rot hk (if col then 3 else 1) key + name
  let y := fun i : Fin k => z i + z (ix hk (i.val+d)) + z (ix hk (i.val+k-d % k))
  y j + (1+y (ix hk (j.val+1)))*y (ix hk (j.val+2)) +
    rot hk (if col then 4 else 0) key j + c j

def lin {k : ℕ} (hk : 0 < k) (col : Bool) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  rot hk (if col then 3 else 1) x i +
    rot hk (if col then 3 else 1) x (ix hk (i.val+(if col then 2 else 1))) +
    rot hk (if col then 3 else 1) x (ix hk (i.val+k-(if col then 2 else 1) % k))

def Adm {k : ℕ} (hk : 0 < k) (m h : ℕ) (Q : Fin m → Fin k → ZMod 2)
    (marked : Bool → Fin k → Bool) (U : Submodule (ZMod 2) (Fin k → ZMod 2)) : Prop :=
  (∀ x ∈ U, ∀ i : Fin m, dotProduct (Q i) x = 0) ∧
  (∀ (name c : Bool → (Fin k → ZMod 2)) (a : Fin k → ZMod 2),
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range
      (fun (u : {u : Bool × Fin k // marked u.1 u.2 = true}) (xy : U × U) =>
        run hk u.val.1 (name u.val.1) (c u.val.1) a u.val.2 +
        run hk u.val.1 (name u.val.1) (c u.val.1) (a+xy.1.val) u.val.2 +
        run hk u.val.1 (name u.val.1) (c u.val.1) (a+xy.2.val) u.val.2 +
        run hk u.val.1 (name u.val.1) (c u.val.1) (a+xy.1.val+xy.2.val) u.val.2))) ≤ h)

theorem polar_eq {k : ℕ} (hk : 0 < k) (col : Bool) (name c a x y : Fin k → ZMod 2) (j : Fin k) :
    run hk col name c a j + run hk col name c (a+x) j + run hk col name c (a+y) j +
      run hk col name c (a+x+y) j =
    lin hk col x (ix hk (j.val+1)) * lin hk col y (ix hk (j.val+2)) +
      lin hk col y (ix hk (j.val+1)) * lin hk col x (ix hk (j.val+2)) := by
  have hq : ∀ u1 u2 p1 p2 q1 q2 : ZMod 2,
      (1+u1)*u2 + (1+(u1+p1))*(u2+p2) + (1+(u1+q1))*(u2+q2) + (1+(u1+p1+q1))*(u2+p2+q2) =
        p1*q2 + q1*p2 := by decide
  have hl : ∀ l lx ly : ZMod 2, l + (l+lx) + (l+ly) + (l+lx+ly) = 0 := by decide
  have hr : ∀ (s : ℕ) (u v : Fin k → ZMod 2) (i : Fin k),
      rot hk s (u + v) i = rot hk s u i + rot hk s v i := fun _ _ _ _ => rfl
  unfold run lin
  simp only [Pi.add_apply, hr]
  have e1 := hq
    ((rot hk (if col then 3 else 1) a (ix hk (j.val+1)) + name (ix hk (j.val+1))) +
      (rot hk (if col then 3 else 1) a (ix hk ((ix hk (j.val+1)).val+(if col then 2 else 1))) +
        name (ix hk ((ix hk (j.val+1)).val+(if col then 2 else 1)))) +
      (rot hk (if col then 3 else 1) a (ix hk ((ix hk (j.val+1)).val+k-(if col then 2 else 1) % k)) +
        name (ix hk ((ix hk (j.val+1)).val+k-(if col then 2 else 1) % k))))
    ((rot hk (if col then 3 else 1) a (ix hk (j.val+2)) + name (ix hk (j.val+2))) +
      (rot hk (if col then 3 else 1) a (ix hk ((ix hk (j.val+2)).val+(if col then 2 else 1))) +
        name (ix hk ((ix hk (j.val+2)).val+(if col then 2 else 1)))) +
      (rot hk (if col then 3 else 1) a (ix hk ((ix hk (j.val+2)).val+k-(if col then 2 else 1) % k)) +
        name (ix hk ((ix hk (j.val+2)).val+k-(if col then 2 else 1) % k))))
    (rot hk (if col then 3 else 1) x (ix hk (j.val+1)) +
      rot hk (if col then 3 else 1) x (ix hk ((ix hk (j.val+1)).val+(if col then 2 else 1))) +
      rot hk (if col then 3 else 1) x (ix hk ((ix hk (j.val+1)).val+k-(if col then 2 else 1) % k)))
    (rot hk (if col then 3 else 1) x (ix hk (j.val+2)) +
      rot hk (if col then 3 else 1) x (ix hk ((ix hk (j.val+2)).val+(if col then 2 else 1))) +
      rot hk (if col then 3 else 1) x (ix hk ((ix hk (j.val+2)).val+k-(if col then 2 else 1) % k)))
    (rot hk (if col then 3 else 1) y (ix hk (j.val+1)) +
      rot hk (if col then 3 else 1) y (ix hk ((ix hk (j.val+1)).val+(if col then 2 else 1))) +
      rot hk (if col then 3 else 1) y (ix hk ((ix hk (j.val+1)).val+k-(if col then 2 else 1) % k)))
    (rot hk (if col then 3 else 1) y (ix hk (j.val+2)) +
      rot hk (if col then 3 else 1) y (ix hk ((ix hk (j.val+2)).val+(if col then 2 else 1))) +
      rot hk (if col then 3 else 1) y (ix hk ((ix hk (j.val+2)).val+k-(if col then 2 else 1) % k)))
  have e2 := hl
    ((rot hk (if col then 3 else 1) a j + name j) +
      (rot hk (if col then 3 else 1) a (ix hk (j.val+(if col then 2 else 1))) +
        name (ix hk (j.val+(if col then 2 else 1)))) +
      (rot hk (if col then 3 else 1) a (ix hk (j.val+k-(if col then 2 else 1) % k)) +
        name (ix hk (j.val+k-(if col then 2 else 1) % k))) +
      rot hk (if col then 4 else 0) a j + c j)
    (rot hk (if col then 3 else 1) x j +
      rot hk (if col then 3 else 1) x (ix hk (j.val+(if col then 2 else 1))) +
      rot hk (if col then 3 else 1) x (ix hk (j.val+k-(if col then 2 else 1) % k)) +
      rot hk (if col then 4 else 0) x j)
    (rot hk (if col then 3 else 1) y j +
      rot hk (if col then 3 else 1) y (ix hk (j.val+(if col then 2 else 1))) +
      rot hk (if col then 3 else 1) y (ix hk (j.val+k-(if col then 2 else 1) % k)) +
      rot hk (if col then 4 else 0) y j)
  linear_combination e1 + e2

def wedge {s : ℕ} (α β : Fin s → ZMod 2) : Fin s → Fin s → ZMod 2 :=
  fun i j => α i * β j + α j * β i

def EdgeOK {s H : ℕ} (g : Fin H → Fin s → Fin s → ZMod 2) :
    Option (Fin s → ZMod 2) → Option (Fin s → ZMod 2) → Prop
  | some α, some β => wedge α β ∈ Submodule.span (ZMod 2) (Set.range g)
  | none, none => True
  | some α, none => α = 0
  | none, some β => β = 0

def LValid {k : ℕ} (hk : 0 < k) {s H : ℕ} (marked : Bool → Fin k → Bool)
    (g : Fin H → Fin s → Fin s → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2)) : Prop :=
  ∀ (col : Bool) (j : Fin k), marked col j = true →
    EdgeOK g (lab col (ix hk (j.val+1))) (lab col (ix hk (j.val+2)))

def LSol {k : ℕ} (hk : 0 < k) {s r : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) : Prop :=
  ∃ τ : Fin s → ZMod 2, (∀ i, dotProduct (M i) x = 0) ∧
    (∀ (col : Bool) (v : Fin k) (α : Fin s → ZMod 2), lab col v = some α →
      lin hk col x v = dotProduct α τ) ∧
    (∀ (col : Bool) (j : Fin k), marked col j = true →
      lab col (ix hk (j.val+1)) = none → lab col (ix hk (j.val+2)) = none →
      lin hk col x (ix hk (j.val+1)) = lin hk col x (ix hk (j.val+2)))

noncomputable def ins {k r : ℕ} (S : Fin (r+1) → Fin k → ZMod 2) (q : Fin k → ZMod 2) :
    Fin (r+1) → Fin k → ZMod 2 :=
  haveI := Classical.propDecidable (q ∈ Submodule.span (ZMod 2) (Set.range S))
  if q ∈ Submodule.span (ZMod 2) (Set.range S) then S
  else (Fin.cons q (fun j : Fin r => S j.castSucc) : Fin (r+1) → Fin k → ZMod 2)

noncomputable def elim {k r m : ℕ} (Q : Fin m → Fin k → ZMod 2) : Fin (r+1) → Fin k → ZMod 2 :=
  (List.ofFn Q).foldl ins 0

abbrev Idx (r s : ℕ) := (Fin 5 ⊕ Fin 5) ⊕ (Fin r ⊕ Fin s)

inductive Src (r : ℕ) : Type where
  | c0 : Src r
  | c1 : Src r
  | mr : Src r
  | mc : Src r
  | mb : Fin r → Src r

def Src.val {r : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) : Src r → ZMod 2
  | Src.c0 => 0
  | Src.c1 => 1
  | Src.mr => if mr then 1 else 0
  | Src.mc => if mc then 1 else 0
  | Src.mb i => mcol i

def cvec {r s : ℕ} (fw fp : Fin 5 → Src r) (fa : Fin r → Src r) (fs : Fin s → Src r) :
    Idx r s → Src r
  | Sum.inl (Sum.inl j) => fw j
  | Sum.inl (Sum.inr j) => fp j
  | Sum.inr (Sum.inl i) => fa i
  | Sum.inr (Sum.inr i) => fs i

def bsrc {r : ℕ} (b : Bool) : Src r := if b then Src.c1 else Src.c0

def zsrc {r : ℕ} {α : Type} : α → Src r := fun _ => Src.c0

abbrev SEq (r s : ℕ) := (Idx r s → Src r) × Src r × (Idx r s → Src r)

def zeroEq {r s : ℕ} : SEq r s := (fun _ => Src.c0, Src.c0, fun _ => Src.c0)

def eqs {r s : ℕ} (k t : ℕ) (pr pc cr cc : Option (Fin s → ZMod 2)) : List (SEq r s) :=
  List.ofFn (fun j : Fin 4 =>
    ((cvec (fun i => bsrc (decide (i.val = j.val+1))) zsrc zsrc zsrc, Src.c0,
      cvec (fun i => bsrc (decide (i.val = j.val))) zsrc zsrc zsrc) : SEq r s)) ++
  [((cvec zsrc zsrc zsrc zsrc, Src.c1,
      cvec (fun i => bsrc (decide (i.val = 4))) zsrc zsrc zsrc) : SEq r s)] ++
  List.ofFn (fun j : Fin 5 =>
    ((cvec zsrc (fun i => bsrc (decide (i = j))) zsrc zsrc, Src.c0,
      cvec zsrc (fun i => bsrc (decide (i = j))) zsrc zsrc) : SEq r s)) ++
  List.ofFn (fun j : Fin r =>
    ((cvec zsrc zsrc (fun i => bsrc (decide (i = j))) zsrc, Src.mb j,
      cvec zsrc zsrc (fun i => bsrc (decide (i = j))) zsrc) : SEq r s)) ++
  List.ofFn (fun j : Fin s =>
    ((cvec zsrc zsrc zsrc (fun i => bsrc (decide (i = j))), Src.c0,
      cvec zsrc zsrc zsrc (fun i => bsrc (decide (i = j)))) : SEq r s)) ++
  (if t = 0 then
    List.ofFn (fun j : Fin 5 =>
      ((cvec (fun i => bsrc (decide (i = j))) (fun i => bsrc (decide (i = j))) zsrc zsrc, Src.c0,
        cvec zsrc zsrc zsrc zsrc) : SEq r s)) ++
    List.ofFn (fun j : Fin r =>
      ((cvec zsrc zsrc (fun i => bsrc (decide (i = j))) zsrc, Src.c0,
        cvec zsrc zsrc zsrc zsrc) : SEq r s))
   else []) ++
  (if t + 1 = k then
    List.ofFn (fun j : Fin 5 =>
      ((cvec zsrc zsrc zsrc zsrc, Src.c0,
        cvec (fun i => bsrc (decide (i = j))) (fun i => bsrc (decide (i = j))) zsrc zsrc) : SEq r s)) ++
    List.ofFn (fun j : Fin r =>
      ((cvec zsrc zsrc zsrc zsrc, Src.c0,
        cvec zsrc zsrc (fun i => bsrc (decide (i = j))) zsrc) : SEq r s))
   else []) ++
  [match cr with
    | some α => ((cvec (fun i => bsrc (decide (i.val = 3 ∨ i.val = 4))) zsrc zsrc
        (fun i => bsrc (decide (α i ≠ 0))), Src.c1, cvec zsrc zsrc zsrc zsrc) : SEq r s)
    | none => zeroEq] ++
  [match cc with
    | some β => ((cvec (fun i => bsrc (decide (i.val = 1 ∨ i.val = 3))) zsrc zsrc
        (fun i => bsrc (decide (β i ≠ 0))), Src.c1, cvec zsrc zsrc zsrc zsrc) : SEq r s)
    | none => zeroEq] ++
  [if pr.isNone && cr.isNone then
      ((cvec (fun i => if i.val = 2 then Src.mr else Src.c0) zsrc zsrc zsrc, Src.mr,
        cvec zsrc zsrc zsrc zsrc) : SEq r s)
    else zeroEq] ++
  [if pc.isNone && cc.isNone then
      ((cvec (fun _ => Src.mc) zsrc zsrc zsrc, Src.mc, cvec zsrc zsrc zsrc zsrc) : SEq r s)
    else zeroEq]

def holds {r s : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (q : SEq r s)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) : Prop :=
  (∑ i, (q.1 i).val mr mc mcol * Y i) + q.2.1.val mr mc mcol * xt +
    (∑ i, (q.2.2 i).val mr mc mcol * Y' i) = 0

def iterCG {α : Type} (step : ℕ → α → CG α) : ℕ → α → CG α
  | 0, a, gs => (gs, a)
  | t+1, a, gs => step t (iterCG step t a gs).2 (iterCG step t a gs).1

theorem iterCG_spec {I : ℕ} {α : Type} (step : ℕ → α → CG α)
    (Inv : ℕ → List Gate → α → Prop) (c n : ℕ)
    (hstep : ∀ t a gs, t < n → Good I gs → Inv t gs a →
      Extends gs (step t a gs).1 ∧ (step t a gs).1.length ≤ gs.length + c ∧
      Good I (step t a gs).1 ∧ Inv (t+1) (step t a gs).1 (step t a gs).2)
    (a : α) (gs : List Gate) (hG : Good I gs) (h0 : Inv 0 gs a) :
    ∀ t ≤ n, Extends gs (iterCG step t a gs).1 ∧
      (iterCG step t a gs).1.length ≤ gs.length + t * c ∧
      Good I (iterCG step t a gs).1 ∧ Inv t (iterCG step t a gs).1 (iterCG step t a gs).2 := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨extends_refl gs, ?_, hG, h0⟩
    show gs.length ≤ gs.length + 0 * c
    omega
  | succ t ih =>
    intro ht
    obtain ⟨e1, l1, g1, i1⟩ := ih (by omega)
    obtain ⟨e2, l2, g2, i2⟩ := hstep t _ _ (by omega) g1 i1
    refine ⟨extends_trans e1 e2, ?_, g2, i2⟩
    show (step t (iterCG step t a gs).2 (iterCG step t a gs).1).1.length ≤ gs.length + (t + 1) * c
    have hc : (t + 1) * c = t * c + c := by ring
    omega

def copyGates (srcs : List ℕ) : List Gate := srcs.map (fun u => ⟨GateOp.or, [u, u]⟩)

def shiftGates (P : ℕ) (gs : List Gate) : List Gate :=
  gs.map (fun g => ⟨g.op, g.inputs.map (fun i => i + P)⟩)

end Prelude


theorem sa_lin_add {k : ℕ} (hk : 0 < k) (col : Bool) (x y : Fin k → ZMod 2) (v : Fin k) :
    lin hk col (x + y) v = lin hk col x v + lin hk col y v := by
  have hr : ∀ (s : ℕ) (u w : Fin k → ZMod 2) (i : Fin k),
      rot hk s (u + w) i = rot hk s u i + rot hk s w i := fun _ _ _ _ => rfl
  unfold lin
  simp only [hr]
  ring

theorem sa_lin_smul {k : ℕ} (hk : 0 < k) (col : Bool) (a : ZMod 2) (x : Fin k → ZMod 2)
    (v : Fin k) : lin hk col (a • x) v = a * lin hk col x v := by
  have hr : ∀ (s : ℕ) (u : Fin k → ZMod 2) (i : Fin k),
      rot hk s (a • u) i = a * rot hk s u i := fun _ _ _ => rfl
  unfold lin
  simp only [hr]
  ring

theorem sa_lin_zero {k : ℕ} (hk : 0 < k) (col : Bool) (v : Fin k) :
    lin hk col (0 : Fin k → ZMod 2) v = 0 := by
  have hr : ∀ (s : ℕ) (i : Fin k), rot hk s (0 : Fin k → ZMod 2) i = 0 := fun _ _ => rfl
  unfold lin
  simp only [hr]
  ring

-- pairs (x, tau) with x in K and tau a labelling witness for x
def sa_Kt {k : ℕ} (hk : 0 < k) {s : ℕ} (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (K : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    Submodule (ZMod 2) ((Fin k → ZMod 2) × (Fin s → ZMod 2)) :=
  { carrier := {p | p.1 ∈ K ∧ ∀ (col : Bool) (v : Fin k) (α : Fin s → ZMod 2),
      lab col v = some α → lin hk col p.1 v = dotProduct α p.2}, add_mem' := by
      rintro p q ⟨hp1, hp2⟩ ⟨hq1, hq2⟩
      refine ⟨K.add_mem hp1 hq1, ?_⟩
      intro col v α hα
      show lin hk col (p.1 + q.1) v = dotProduct α (p.2 + q.2)
      rw [sa_lin_add, dotProduct_add, hp2 col v α hα, hq2 col v α hα]
    zero_mem' := by
      refine ⟨K.zero_mem, ?_⟩
      intro col v α _
      show lin hk col 0 v = dotProduct α 0
      rw [sa_lin_zero, dotProduct_zero]
    smul_mem' := by
      rintro a p ⟨hp1, hp2⟩
      refine ⟨K.smul_mem a hp1, ?_⟩
      intro col v α hα
      show lin hk col (a • p.1) v = dotProduct α (a • p.2)
      rw [sa_lin_smul, dotProduct_smul, hp2 col v α hα, smul_eq_mul] }

theorem sa_exT {k : ℕ} (hk : 0 < k) {s r : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (K : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hK : ∀ x ∈ K, LSol hk marked M lab x) :
    ∃ T : K →ₗ[ZMod 2] (Fin s → ZMod 2),
      ∀ (x : K) (col : Bool) (v : Fin k) (α : Fin s → ZMod 2),
        lab col v = some α → lin hk col x.val v = dotProduct α (T x) := by
  let π : sa_Kt hk lab K →ₗ[ZMod 2] K :=
    LinearMap.codRestrict K
      ((LinearMap.fst (ZMod 2) (Fin k → ZMod 2) (Fin s → ZMod 2)).comp (sa_Kt hk lab K).subtype)
      (fun p => p.2.1)
  have hsurj : LinearMap.range π = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨x, hx⟩
    obtain ⟨τ, -, h2, -⟩ := hK x hx
    exact ⟨⟨(x, τ), ⟨hx, h2⟩⟩, rfl⟩
  obtain ⟨σ, hσ⟩ := π.exists_rightInverse_of_surjective hsurj
  refine ⟨(LinearMap.snd (ZMod 2) (Fin k → ZMod 2) (Fin s → ZMod 2)).comp
    ((sa_Kt hk lab K).subtype.comp σ), ?_⟩
  intro x col v α hα
  have h1 : π (σ x) = x := LinearMap.congr_fun hσ x
  have h2 : (σ x).val.1 = x.val := congrArg Subtype.val h1
  have h3 := (σ x).2.2 col v α hα
  rw [h2] at h3
  exact h3

def sa_Psi {k s : ℕ} (K : Submodule (ZMod 2) (Fin k → ZMod 2))
    (T : K →ₗ[ZMod 2] (Fin s → ZMod 2)) :
    (Fin s → Fin s → ZMod 2) →ₗ[ZMod 2] (K × K → ZMod 2) where
  toFun A := fun xy => ∑ i, ∑ j, A i j * T xy.1 i * T xy.2 j
  map_add' := by
    intro A B
    funext xy
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a A
    funext xy
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem sa_Psi_apply {k s : ℕ} (K : Submodule (ZMod 2) (Fin k → ZMod 2))
    (T : K →ₗ[ZMod 2] (Fin s → ZMod 2)) (A : Fin s → Fin s → ZMod 2) (xy : K × K) :
    sa_Psi K T A xy = ∑ i, ∑ j, A i j * T xy.1 i * T xy.2 j := rfl

theorem sa_wedge_sum {s : ℕ} (α β tx ty : Fin s → ZMod 2) :
    (∑ i, ∑ j, wedge α β i j * tx i * ty j) =
      dotProduct α tx * dotProduct β ty + dotProduct α ty * dotProduct β tx := by
  unfold wedge dotProduct
  rw [Finset.sum_mul_sum, mul_comm (∑ i, α i * ty i) (∑ i, β i * tx i), Finset.sum_mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem sa_edge {k : ℕ} (hk : 0 < k) {s r H : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2)
    (g : Fin H → Fin s → Fin s → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (hv : LValid hk marked g lab) (K : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hK : ∀ x ∈ K, LSol hk marked M lab x)
    (T : K →ₗ[ZMod 2] (Fin s → ZMod 2))
    (hT : ∀ (x : K) (col : Bool) (v : Fin k) (α : Fin s → ZMod 2),
      lab col v = some α → lin hk col x.val v = dotProduct α (T x))
    (col : Bool) (j : Fin k) (hm : marked col j = true)
    (f : K × K → ZMod 2)
    (hf : ∀ xy : K × K, f xy =
      lin hk col xy.1.val (ix hk (j.val+1)) * lin hk col xy.2.val (ix hk (j.val+2)) +
      lin hk col xy.2.val (ix hk (j.val+1)) * lin hk col xy.1.val (ix hk (j.val+2))) :
    f ∈ Submodule.map (sa_Psi K T) (Submodule.span (ZMod 2) (Set.range g)) := by
  have h2 : ∀ a b : ZMod 2, a * b + b * a = 0 := by decide
  have he := hv col j hm
  rcases hA : lab col (ix hk (j.val+1)) with _ | α
  · rcases hB : lab col (ix hk (j.val+2)) with _ | β
    · have hz : f = 0 := by
        funext xy
        have e1 : lin hk col xy.1.val (ix hk (j.val+1)) =
            lin hk col xy.1.val (ix hk (j.val+2)) := by
          obtain ⟨τ, -, -, h3⟩ := hK xy.1.val xy.1.2
          exact h3 col j hm hA hB
        have e2 : lin hk col xy.2.val (ix hk (j.val+1)) =
            lin hk col xy.2.val (ix hk (j.val+2)) := by
          obtain ⟨τ, -, -, h3⟩ := hK xy.2.val xy.2.2
          exact h3 col j hm hA hB
        rw [hf xy, e1, e2]
        exact h2 _ _
      rw [hz]
      exact Submodule.zero_mem _
    · rw [hA, hB] at he
      have hβ : β = 0 := he
      have hz : f = 0 := by
        funext xy
        have e1 := hT xy.1 col _ β hB
        have e2 := hT xy.2 col _ β hB
        rw [hβ, zero_dotProduct] at e1 e2
        rw [hf xy, e1, e2]
        simp
      rw [hz]
      exact Submodule.zero_mem _
  · rcases hB : lab col (ix hk (j.val+2)) with _ | β
    · rw [hA, hB] at he
      have hα : α = 0 := he
      have hz : f = 0 := by
        funext xy
        have e1 := hT xy.1 col _ α hA
        have e2 := hT xy.2 col _ α hA
        rw [hα, zero_dotProduct] at e1 e2
        rw [hf xy, e1, e2]
        simp
      rw [hz]
      exact Submodule.zero_mem _
    · rw [hA, hB] at he
      have hw : wedge α β ∈ Submodule.span (ZMod 2) (Set.range g) := he
      refine ⟨wedge α β, hw, ?_⟩
      funext xy
      rw [sa_Psi_apply, sa_wedge_sum, hf xy, hT xy.1 col _ α hA, hT xy.2 col _ β hB,
        hT xy.2 col _ α hA, hT xy.1 col _ β hB]

theorem sa_rank {k s H : ℕ} (K : Submodule (ZMod 2) (Fin k → ZMod 2))
    (T : K →ₗ[ZMod 2] (Fin s → ZMod 2)) (g : Fin H → Fin s → Fin s → ZMod 2)
    {ι : Type} (P : ι → (K × K → ZMod 2))
    (hP : ∀ u, P u ∈ Submodule.map (sa_Psi K T) (Submodule.span (ZMod 2) (Set.range g))) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range P)) ≤ H := by
  have hsub : Submodule.span (ZMod 2) (Set.range P) ≤
      Submodule.map (sa_Psi K T) (Submodule.span (ZMod 2) (Set.range g)) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    exact hP
  have h1 := Submodule.finrank_mono hsub
  have h2 := Submodule.finrank_map_le (sa_Psi K T) (Submodule.span (ZMod 2) (Set.range g))
  have h3 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤
      Fintype.card (Fin H) := finrank_range_le_card (R := ZMod 2) g
  rw [Fintype.card_fin] at h3
  exact h1.trans (h2.trans h3)

theorem sound {k : ℕ} (hk : 0 < k) (m h H s r : ℕ) (hH : H ≤ h)
    (Q : Fin m → Fin k → ZMod 2) (marked : Bool → Fin k → Bool) (M : Fin r → Fin k → ZMod 2)
    (hM : ∀ x : Fin k → ZMod 2, (∀ i, dotProduct (M i) x = 0) → ∀ i, dotProduct (Q i) x = 0)
    (g : Fin H → Fin s → Fin s → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (hv : LValid hk marked g lab) (K : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hK : ∀ x ∈ K, LSol hk marked M lab x) : Adm hk m h Q marked K := by
  unfold Adm
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨τ, h1, -, -⟩ := hK x hx
    exact hM x h1
  · intro name c a
    obtain ⟨T, hT⟩ := sa_exT hk marked M lab K hK
    refine (sa_rank K T g _ ?_).trans hH
    rintro ⟨⟨col, j⟩, hm⟩
    exact sa_edge hk marked M g lab hv K hK T hT col j hm _
      (fun xy => polar_eq hk col (name col) (c col) a xy.1.val xy.2.val j)


theorem cb_lin_add {k : ℕ} (hk : 0 < k) (col : Bool) (x y : Fin k → ZMod 2) (v : Fin k) :
    lin hk col (x + y) v = lin hk col x v + lin hk col y v := by
  have hr : ∀ (s : ℕ) (u w : Fin k → ZMod 2) (i : Fin k),
      rot hk s (u + w) i = rot hk s u i + rot hk s w i := fun _ _ _ _ => rfl
  unfold lin
  simp only [hr]
  ring

theorem cb_lin_smul {k : ℕ} (hk : 0 < k) (col : Bool) (c : ZMod 2) (x : Fin k → ZMod 2)
    (v : Fin k) : lin hk col (c • x) v = c * lin hk col x v := by
  have hr : ∀ (s : ℕ) (u : Fin k → ZMod 2) (i : Fin k),
      rot hk s (c • u) i = c * rot hk s u i := fun _ _ _ => rfl
  unfold lin
  simp only [hr]
  ring

def cb_f {k : ℕ} (hk : 0 < k) (U : Submodule (ZMod 2) (Fin k → ZMod 2)) (cv : Bool × Fin k) :
    U →ₗ[ZMod 2] ZMod 2 where
  toFun x := lin hk cv.1 x.val cv.2
  map_add' x y := cb_lin_add hk cv.1 x.val y.val cv.2
  map_smul' c x := cb_lin_smul hk cv.1 c x.val cv.2

def cb_pol {W : Type*} (a b : W → ZMod 2) : W × W → ZMod 2 :=
  fun xy => a xy.1 * b xy.2 + a xy.2 * b xy.1

theorem cb_sys : ∀ ax0 by0 ay0 bx0 az bz : ZMod 2, ax0 * by0 + ay0 * bx0 ≠ 0 →
    az * bx0 + ax0 * bz = 0 → az * by0 + ay0 * bz = 0 → az = 0 ∧ bz = 0 := by decide

theorem cb_wz {W : Type*} (a b : W → ZMod 2) (h : ∀ x y, a x * b y + a y * b x = 0)
    (hb : b ≠ 0) : a = 0 ∨ a = b := by
  obtain ⟨y0, hy0⟩ : ∃ y, b y ≠ 0 := by
    by_contra hne
    exact hb (funext fun y => not_not.mp (fun hy : ¬ b y = 0 => hne ⟨y, hy⟩))
  have key : ∀ p q r s : ZMod 2, s ≠ 0 → p * s + r * q = 0 → p = r * q := by decide
  have h1 : ∀ x, a x = a y0 * b x := fun x => key _ _ _ _ hy0 (h x y0)
  have h2 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h2 (a y0) with h0 | h0
  · left
    funext x
    rw [h1 x, h0]
    simp
  · right
    funext x
    rw [h1 x, h0]
    simp

theorem cb_contr {W : Type*} {H : ℕ} (Kp : W → Prop) (a' b' : Fin H → W → ZMod 2)
    (hK : ∀ i z, Kp z → a' i z = 0 ∧ b' i z = 0) (a b : W → ZMod 2)
    (hmem : cb_pol a b ∈ Submodule.span (ZMod 2) (Set.range (fun i => cb_pol (a' i) (b' i))))
    (hne : ∃ x y, a x * b y + a y * b x ≠ 0) : ∀ z, Kp z → a z = 0 ∧ b z = 0 := by
  intro z hz
  have hS : ∀ y : W, a z * b y + a y * b z = 0 := by
    intro y
    have hle : Submodule.span (ZMod 2) (Set.range (fun i => cb_pol (a' i) (b' i))) ≤
        LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : W × W => ZMod 2) (z, y)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      show a' i z * b' i y + a' i y * b' i z = 0
      rw [(hK i z hz).1, (hK i z hz).2]
      ring
    exact LinearMap.mem_ker.mp (hle hmem)
  obtain ⟨x0, y0, h0⟩ := hne
  exact cb_sys _ _ _ _ _ _ h0 (hS x0) (hS y0)

theorem cb_tri {W : Type*} (Kp : W → Prop) (a b : W → ZMod 2)
    (hcon : (∃ x y, a x * b y + a y * b x ≠ 0) → ∀ z, Kp z → a z = 0 ∧ b z = 0) :
    ((∀ z, Kp z → a z = 0) → ¬ (∀ z, Kp z → b z = 0) → a = 0) ∧
    (¬ (∀ z, Kp z → a z = 0) → (∀ z, Kp z → b z = 0) → b = 0) ∧
    (¬ (∀ z, Kp z → a z = 0) → ¬ (∀ z, Kp z → b z = 0) → a = b) := by
  have hz : (¬ (∀ z, Kp z → a z = 0) ∨ ¬ (∀ z, Kp z → b z = 0)) →
      ∀ x y, a x * b y + a y * b x = 0 := by
    intro hor x y
    by_contra hxy
    have h2 := hcon ⟨x, y, hxy⟩
    rcases hor with h3 | h3
    · exact h3 (fun z hz => (h2 z hz).1)
    · exact h3 (fun z hz => (h2 z hz).2)
  refine ⟨?_, ?_, ?_⟩
  · intro ha hb
    have hb0 : b ≠ 0 := by
      intro hb0
      apply hb
      intro z _
      simp [hb0]
    rcases cb_wz a b (hz (Or.inr hb)) hb0 with h0 | h0
    · exact h0
    · exfalso
      apply hb
      rw [← h0]
      exact ha
  · intro ha hb
    have ha0 : a ≠ 0 := by
      intro ha0
      apply ha
      intro z _
      simp [ha0]
    have hz' : ∀ x y, b x * a y + b y * a x = 0 := by
      intro x y
      have h4 := hz (Or.inl ha) y x
      rw [mul_comm (b x), mul_comm (b y)]
      exact h4
    rcases cb_wz b a hz' ha0 with h0 | h0
    · exact h0
    · exfalso
      apply ha
      rw [← h0]
      exact hb
  · intro ha hb
    have hb0 : b ≠ 0 := by
      intro hb0
      apply hb
      intro z _
      simp [hb0]
    rcases cb_wz a b (hz (Or.inr hb)) hb0 with h0 | h0
    · exfalso
      apply ha
      intro z _
      simp [h0]
    · exact h0

theorem cb_ginv {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (Phi : V →ₗ[K] W) : ∃ X : W →ₗ[K] V, ∀ x, Phi (X (Phi x)) = Phi x := by
  obtain ⟨g0, hg0⟩ := LinearMap.exists_rightInverse_of_surjective Phi.rangeRestrict
    (LinearMap.range_rangeRestrict Phi)
  obtain ⟨p0, hp0⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range Phi).subtype
    (Submodule.ker_subtype _)
  refine ⟨g0.comp p0, fun x => ?_⟩
  have h1 : p0 (Phi x) = Phi.rangeRestrict x := LinearMap.congr_fun hp0 (Phi.rangeRestrict x)
  have h2 : Phi.rangeRestrict (g0 (Phi.rangeRestrict x)) = Phi.rangeRestrict x :=
    LinearMap.congr_fun hg0 (Phi.rangeRestrict x)
  show Phi (g0 (p0 (Phi x))) = Phi x
  rw [h1]
  exact congrArg Subtype.val h2

theorem cb_select {M ι : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Fintype ι] (P : ι → M)
    (H : ℕ) (h : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range P)) ≤ H) :
    ∃ e : Fin H → Option ι,
      ∀ u, P u ∈ Submodule.span (ZMod 2) (Set.range (fun i => (e i).elim 0 P)) := by
  classical
  obtain ⟨b, hb1, hb2, hb3⟩ := exists_linearIndependent (ZMod 2) (Set.range P)
  have hfin : b.Finite := (Set.finite_range P).subset hb1
  have hft : Fintype b := hfin.fintype
  have hcard : Fintype.card b ≤ H := by
    have h3 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.range (Subtype.val : b → M))) = Fintype.card b := finrank_span_eq_card hb3
    rw [Subtype.range_coe, hb2] at h3
    omega
  choose pre hpre using (fun c : b => hb1 c.property)
  refine ⟨fun i => if hi : i.val < Fintype.card b then
    some (pre ((Fintype.equivFin b).symm ⟨i.val, hi⟩)) else none, ?_⟩
  intro u
  have hu : P u ∈ Submodule.span (ZMod 2) b := by
    rw [hb2]
    exact Submodule.subset_span ⟨u, rfl⟩
  refine Submodule.span_mono ?_ hu
  intro c hc
  refine ⟨⟨(Fintype.equivFin b ⟨c, hc⟩).val,
    lt_of_lt_of_le (Fintype.equivFin b ⟨c, hc⟩).isLt hcard⟩, ?_⟩
  have hlt : (Fintype.equivFin b ⟨c, hc⟩).val < Fintype.card b :=
    (Fintype.equivFin b ⟨c, hc⟩).isLt
  dsimp only
  rw [dite_eq_left hlt]
  simp only [Fin.eta, Equiv.symm_apply_apply]
  exact hpre ⟨c, hc⟩

theorem cb_phi {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (H : ℕ)
    (a' b' : Fin H → W →ₗ[ZMod 2] ZMod 2) :
    ∃ Phi : W →ₗ[ZMod 2] (Fin (2*H) → ZMod 2),
      ∀ z, Phi z = 0 → ∀ i, a' i z = 0 ∧ b' i z = 0 := by
  refine ⟨LinearMap.pi (fun t => if (finProdFinEquiv.symm t).1 = (0 : Fin 2)
    then a' (finProdFinEquiv.symm t).2 else b' (finProdFinEquiv.symm t).2), ?_⟩
  intro z hz i
  have h0 := congrFun hz (finProdFinEquiv ((0 : Fin 2), i))
  have h1 := congrFun hz (finProdFinEquiv ((1 : Fin 2), i))
  simp only [LinearMap.pi_apply, Equiv.symm_apply_apply, Pi.zero_apply] at h0 h1
  simp at h0 h1
  exact ⟨h0, h1⟩

theorem cb_lab {W V : Type} {s : ℕ} [AddCommGroup W] [Module (ZMod 2) W]
    (f : V → W →ₗ[ZMod 2] ZMod 2) (Phi : W →ₗ[ZMod 2] (Fin s → ZMod 2))
    (X : (Fin s → ZMod 2) →ₗ[ZMod 2] W) :
    ∃ lab : V → Option (Fin s → ZMod 2),
      (∀ v α, lab v = some α → (∀ z, Phi z = 0 → f v z = 0) ∧
        α = fun i => f v (X (fun l => if i = l then 1 else 0))) ∧
      (∀ v, lab v = none → ¬ (∀ z, Phi z = 0 → f v z = 0)) := by
  classical
  refine ⟨fun v => if (∀ z, Phi z = 0 → f v z = 0) then
    some (fun i => f v (X (fun l => if i = l then 1 else 0))) else none, ?_, ?_⟩
  · intro v α hα
    by_cases hc : ∀ z, Phi z = 0 → f v z = 0
    · simp only [ite_eq_left hc] at hα
      exact ⟨hc, (Option.some.inj hα).symm⟩
    · simp only [ite_eq_right hc] at hα
      cases hα
  · intro v hv hc
    simp only [ite_eq_left hc] at hv
    cases hv

theorem cb_gen {W : Type*} {s H : ℕ} (ev : Fin s → W) (a' b' : Fin H → W → ZMod 2)
    (a b : W → ZMod 2)
    (hmem : cb_pol a b ∈ Submodule.span (ZMod 2) (Set.range (fun i => cb_pol (a' i) (b' i)))) :
    wedge (fun i => a (ev i)) (fun i => b (ev i)) ∈ Submodule.span (ZMod 2)
      (Set.range (fun i => wedge (fun j => a' i (ev j)) (fun j => b' i (ev j)))) := by
  let E : (W × W → ZMod 2) →ₗ[ZMod 2] (Fin s → Fin s → ZMod 2) :=
    { toFun := fun q i j => q (ev i, ev j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h1 := Submodule.mem_map_of_mem (f := E) hmem
  rw [Submodule.map_span, ← Set.range_comp] at h1
  exact h1

theorem cb_core2 {W V ι : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (f : V → W →ₗ[ZMod 2] ZMod 2) (A B : ι → V) (H : ℕ)
    (a' b' : Fin H → W →ₗ[ZMod 2] ZMod 2)
    (hsel : ∀ u, cb_pol ⇑(f (A u)) ⇑(f (B u)) ∈ Submodule.span (ZMod 2)
      (Set.range (fun i => cb_pol ⇑(a' i) ⇑(b' i)))) :
    ∃ (g : Fin H → Fin (2*H) → Fin (2*H) → ZMod 2) (lab : V → Option (Fin (2*H) → ZMod 2)),
      (∀ u, EdgeOK g (lab (A u)) (lab (B u))) ∧
      ∀ x : W, ∃ τ : Fin (2*H) → ZMod 2,
        (∀ v α, lab v = some α → f v x = dotProduct α τ) ∧
        (∀ u, lab (A u) = none → lab (B u) = none → f (A u) x = f (B u) x) := by
  classical
  obtain ⟨Phi, hPhi⟩ := cb_phi H a' b'
  obtain ⟨X, hX⟩ := cb_ginv Phi
  obtain ⟨lab, hsome, hnone⟩ := cb_lab f Phi X
  have htri := fun u => cb_tri (fun z => Phi z = 0) ⇑(f (A u)) ⇑(f (B u))
    (cb_contr (fun z => Phi z = 0) (fun i => ⇑(a' i)) (fun i => ⇑(b' i))
      (fun i z hz => hPhi z hz i) _ _ (hsel u))
  refine ⟨fun i => wedge (fun j => a' i (X (fun l => if j = l then 1 else 0)))
    (fun j => b' i (X (fun l => if j = l then 1 else 0))), lab, ?_, ?_⟩
  · intro u
    rcases hA : lab (A u) with _ | α <;> rcases hB : lab (B u) with _ | β
    · trivial
    · show β = 0
      obtain ⟨hvB, rfl⟩ := hsome _ _ hB
      have h5 := (htri u).2.1 (hnone _ hA) hvB
      funext i
      exact congrFun h5 _
    · show α = 0
      obtain ⟨hvA, rfl⟩ := hsome _ _ hA
      have h5 := (htri u).1 hvA (hnone _ hB)
      funext i
      exact congrFun h5 _
    · show wedge α β ∈ _
      obtain ⟨hvA, rfl⟩ := hsome _ _ hA
      obtain ⟨hvB, rfl⟩ := hsome _ _ hB
      exact cb_gen (fun i => X (fun l => if i = l then 1 else 0)) (fun i => ⇑(a' i))
        (fun i => ⇑(b' i)) _ _ (hsel u)
  · intro x
    refine ⟨Phi x, ?_, ?_⟩
    · intro v α hα
      obtain ⟨hv, rfl⟩ := hsome v α hα
      have hk0 : Phi (x - X (Phi x)) = 0 := by rw [map_sub, hX, sub_self]
      have h1 := hv _ hk0
      rw [map_sub, sub_eq_zero] at h1
      rw [h1]
      show ((f v).comp X) (Phi x) = _
      rw [LinearMap.pi_apply_eq_sum_univ]
      simp only [dotProduct, LinearMap.comp_apply, smul_eq_mul]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    · intro u hA hB
      exact congrFun ((htri u).2.2 (hnone _ hA) (hnone _ hB)) x

theorem cb_core {W V ι : Type} [AddCommGroup W] [Module (ZMod 2) W] [Fintype ι]
    (f : V → W →ₗ[ZMod 2] ZMod 2) (A B : ι → V) (H : ℕ)
    (hH : Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range (fun u : ι => cb_pol ⇑(f (A u)) ⇑(f (B u))))) ≤ H) :
    ∃ (g : Fin H → Fin (2*H) → Fin (2*H) → ZMod 2) (lab : V → Option (Fin (2*H) → ZMod 2)),
      (∀ u, EdgeOK g (lab (A u)) (lab (B u))) ∧
      ∀ x : W, ∃ τ : Fin (2*H) → ZMod 2,
        (∀ v α, lab v = some α → f v x = dotProduct α τ) ∧
        (∀ u, lab (A u) = none → lab (B u) = none → f (A u) x = f (B u) x) := by
  obtain ⟨e, he⟩ := cb_select (fun u : ι => cb_pol ⇑(f (A u)) ⇑(f (B u))) H hH
  refine cb_core2 f A B H (fun i => (e i).elim 0 (fun u => f (A u)))
    (fun i => (e i).elim 0 (fun u => f (B u))) ?_
  intro u
  have h1 := he u
  have h2 : (fun i => (e i).elim 0 (fun u : ι => cb_pol ⇑(f (A u)) ⇑(f (B u)))) =
      (fun i => cb_pol ⇑((e i).elim 0 (fun u => f (A u)))
        ⇑((e i).elim 0 (fun u => f (B u)))) := by
    funext i
    cases e i with
    | none =>
      funext xy
      simp [cb_pol]
    | some w => rfl
  rw [h2] at h1
  exact h1

theorem complete {k : ℕ} (hk : 0 < k) (m h r : ℕ)
    (Q : Fin m → Fin k → ZMod 2) (marked : Bool → Fin k → Bool) (M : Fin r → Fin k → ZMod 2)
    (hM : ∀ x : Fin k → ZMod 2, (∀ i, dotProduct (Q i) x = 0) → ∀ i, dotProduct (M i) x = 0)
    (U : Submodule (ZMod 2) (Fin k → ZMod 2)) (hU : Adm hk m h Q marked U) :
    ∃ (g : Fin (min h (2*k)) → Fin (2 * min h (2*k)) → Fin (2 * min h (2*k)) → ZMod 2)
      (lab : Bool → Fin k → Option (Fin (2 * min h (2*k)) → ZMod 2)),
      LValid hk marked g lab ∧ ∀ x ∈ U, LSol hk marked M lab x := by
  have hH : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range
      (fun u : {u : Bool × Fin k // marked u.1 u.2 = true} =>
        cb_pol ⇑(cb_f hk U (u.val.1, ix hk (u.val.2.val+1)))
          ⇑(cb_f hk U (u.val.1, ix hk (u.val.2.val+2)))))) ≤ min h (2*k) := by
    apply le_min
    · have hfun : (fun (u : {u : Bool × Fin k // marked u.1 u.2 = true}) (xy : U × U) =>
          run hk u.val.1 0 0 0 u.val.2 +
          run hk u.val.1 0 0 (0+xy.1.val) u.val.2 +
          run hk u.val.1 0 0 (0+xy.2.val) u.val.2 +
          run hk u.val.1 0 0 (0+xy.1.val+xy.2.val) u.val.2) =
          (fun u : {u : Bool × Fin k // marked u.1 u.2 = true} =>
            cb_pol ⇑(cb_f hk U (u.val.1, ix hk (u.val.2.val+1)))
              ⇑(cb_f hk U (u.val.1, ix hk (u.val.2.val+2)))) := by
        funext u xy
        exact polar_eq hk u.val.1 0 0 0 xy.1.val xy.2.val u.val.2
      rw [← hfun]
      exact hU.2 (fun _ => 0) (fun _ => 0) 0
    · have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range
          (fun u : {u : Bool × Fin k // marked u.1 u.2 = true} =>
            cb_pol ⇑(cb_f hk U (u.val.1, ix hk (u.val.2.val+1)))
              ⇑(cb_f hk U (u.val.1, ix hk (u.val.2.val+2)))))) ≤
          Fintype.card {u : Bool × Fin k // marked u.1 u.2 = true} :=
        finrank_range_le_card _
      have h3 : Fintype.card {u : Bool × Fin k // marked u.1 u.2 = true} ≤
          Fintype.card (Bool × Fin k) := Fintype.card_subtype_le _
      have h4 : Fintype.card (Bool × Fin k) = 2 * k := by simp
      omega
  obtain ⟨g, lab, hE, hS⟩ := cb_core (W := U) (V := Bool × Fin k) (cb_f hk U)
    (fun u : {u : Bool × Fin k // marked u.1 u.2 = true} => (u.val.1, ix hk (u.val.2.val+1)))
    (fun u : {u : Bool × Fin k // marked u.1 u.2 = true} => (u.val.1, ix hk (u.val.2.val+2)))
    (min h (2*k)) hH
  refine ⟨g, fun col v => lab (col, v), ?_, ?_⟩
  · intro col j hm
    exact hE ⟨(col, j), hm⟩
  · intro x hx
    obtain ⟨τ, h1, h2⟩ := hS ⟨x, hx⟩
    exact ⟨τ, hM x (hU.1 x hx), fun col v α hα => h1 (col, v) α hα,
      fun col j hm hA hB => h2 ⟨(col, j), hm⟩ hA hB⟩


theorem el_ins_pos {k r : ℕ} (S : Fin (r+1) → Fin k → ZMod 2) (q : Fin k → ZMod 2)
    (h : q ∈ Submodule.span (ZMod 2) (Set.range S)) : ins S q = S := by
  unfold ins
  rw [ite_eq_left h]

theorem el_ins_zero {k r : ℕ} (S : Fin (r+1) → Fin k → ZMod 2) (q : Fin k → ZMod 2)
    (h : q ∉ Submodule.span (ZMod 2) (Set.range S)) : ins S q 0 = q := by
  unfold ins
  rw [ite_eq_right h]
  exact Fin.cons_zero _ _

theorem el_ins_succ {k r : ℕ} (S : Fin (r+1) → Fin k → ZMod 2) (q : Fin k → ZMod 2)
    (h : q ∉ Submodule.span (ZMod 2) (Set.range S)) (i : Fin r) :
    ins S q i.succ = S i.castSucc := by
  unfold ins
  rw [ite_eq_right h]
  exact Fin.cons_succ _ _ _

def el_Inv {k r : ℕ} (S : Fin (r+1) → Fin k → ZMod 2)
    (V : Submodule (ZMod 2) (Fin k → ZMod 2)) : Prop :=
  Submodule.span (ZMod 2) (Set.range S) ≤ V ∧
  (∀ i j : Fin (r+1), i ≤ j → S i = 0 → S j = 0) ∧
  (∀ c : Fin (r+1) → ZMod 2, (∑ j, c j • S j) = 0 → ∀ j, S j ≠ 0 → c j = 0) ∧
  (S (Fin.last r) = 0 → Submodule.span (ZMod 2) (Set.range S) = V)

theorem el_inv_zero {k r : ℕ} :
    el_Inv (0 : Fin (r+1) → Fin k → ZMod 2) ⊥ := by
  have hs : Submodule.span (ZMod 2) (Set.range (0 : Fin (r+1) → Fin k → ZMod 2)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro x ⟨j, rfl⟩
    rfl
  refine ⟨le_of_eq hs, ?_, ?_, fun _ => hs⟩
  · intro i j _ _
    rfl
  · intro c _ j hj
    exact absurd rfl hj

theorem el_step {k r : ℕ} (S : Fin (r+1) → Fin k → ZMod 2)
    (V : Submodule (ZMod 2) (Fin k → ZMod 2)) (q : Fin k → ZMod 2) (h : el_Inv S V) :
    el_Inv (ins S q) (V ⊔ Submodule.span (ZMod 2) {q}) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  by_cases hq : q ∈ Submodule.span (ZMod 2) (Set.range S)
  · rw [el_ins_pos S q hq]
    refine ⟨le_trans h1 le_sup_left, h2, h3, ?_⟩
    intro hl
    have hV := h4 hl
    have hqV : Submodule.span (ZMod 2) {q} ≤ V := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact h1 hq
    rw [sup_eq_left.mpr hqV]
    exact hV
  · have hq0 : q ≠ 0 := by
      intro h0
      apply hq
      rw [h0]
      exact Submodule.zero_mem _
    have e0 := el_ins_zero S q hq
    have es := el_ins_succ S q hq
    have hI1 : Submodule.span (ZMod 2) (Set.range (ins S q)) ≤
        V ⊔ Submodule.span (ZMod 2) {q} := by
      rw [Submodule.span_le]
      rintro x ⟨j, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [e0]
        exact (le_sup_right : Submodule.span (ZMod 2) {q} ≤ V ⊔ Submodule.span (ZMod 2) {q})
          (Submodule.subset_span rfl)
      · rw [es]
        exact (le_sup_left : V ≤ V ⊔ Submodule.span (ZMod 2) {q})
          (h1 (Submodule.subset_span ⟨_, rfl⟩))
    refine ⟨hI1, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · intro _ hz
        rw [e0] at hz
        exact absurd hz hq0
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro hle
          have h' : (i'.succ).val ≤ (0 : Fin (r+1)).val := hle
          simp at h'
        · intro hle hz
          rw [es] at hz ⊢
          exact h2 _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.succ_le_succ_iff.mp hle)) hz
    · intro c hc
      rw [Fin.sum_univ_succ] at hc
      simp only [e0, es] at hc
      have hc0 : c 0 = 0 := by
        by_contra hne
        have hall : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
        have h1' : c 0 = 1 := hall _ hne
        rw [h1', one_smul] at hc
        have hqe : q = -∑ j : Fin r, c j.succ • S j.castSucc := eq_neg_of_add_eq_zero_left hc
        apply hq
        rw [hqe]
        apply Submodule.neg_mem
        apply Submodule.sum_mem
        intro j _
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      rw [hc0, zero_smul, zero_add] at hc
      have hc' : (∑ j, (Fin.snoc (α := fun _ => ZMod 2) (fun j : Fin r => c j.succ) 0 :
          Fin (r+1) → ZMod 2) j • S j) = 0 := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero]
        exact hc
      have h3' := h3 _ hc'
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · intro _
        exact hc0
      · intro hne
        rw [es] at hne
        have h5 := h3' i.castSucc hne
        simpa [Fin.snoc_castSucc] using h5
    · intro hl
      have hSl : S (Fin.last r) = 0 := by
        rcases Fin.eq_zero_or_eq_succ (Fin.last r) with h0 | ⟨i, hi⟩
        · rw [h0, e0] at hl
          exact absurd hl hq0
        · rw [hi, es] at hl
          exact h2 _ _ (Fin.le_last _) hl
      have hV := h4 hSl
      apply le_antisymm hI1
      rw [← hV]
      apply sup_le
      · rw [Submodule.span_le]
        rintro x ⟨j, rfl⟩
        refine Fin.lastCases ?_ (fun i => ?_) j
        · rw [hSl]
          exact Submodule.zero_mem _
        · rw [← es]
          exact Submodule.subset_span ⟨_, rfl⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        have hmem : q ∈ Set.range (ins S q) := ⟨0, e0⟩
        exact Submodule.subset_span hmem

theorem el_fold {k r : ℕ} (L : List (Fin k → ZMod 2)) :
    ∀ (S : Fin (r+1) → Fin k → ZMod 2) (V : Submodule (ZMod 2) (Fin k → ZMod 2)),
      el_Inv S V → el_Inv (L.foldl ins S) (V ⊔ Submodule.span (ZMod 2) {q | q ∈ L}) := by
  induction L with
  | nil =>
    intro S V h
    have he : ({q | q ∈ ([] : List (Fin k → ZMod 2))} : Set (Fin k → ZMod 2)) = ∅ := by
      ext q
      simp
    rw [he, Submodule.span_empty, sup_bot_eq]
    exact h
  | cons a L ih =>
    intro S V h
    have hs : ({q | q ∈ a :: L} : Set (Fin k → ZMod 2)) = insert a {q | q ∈ L} := by
      ext q
      simp
    rw [hs, Submodule.span_insert, ← sup_assoc]
    exact ih _ _ (el_step S V a h)

theorem el_inv_elim {k r m : ℕ} (Q : Fin m → Fin k → ZMod 2) :
    el_Inv (elim Q : Fin (r+1) → Fin k → ZMod 2) (Submodule.span (ZMod 2) (Set.range Q)) := by
  have h := el_fold (r := r) (List.ofFn Q) 0 ⊥ el_inv_zero
  have hs : ({q | q ∈ List.ofFn Q} : Set (Fin k → ZMod 2)) = Set.range Q := by
    ext q
    simp [List.mem_ofFn]
  rw [hs, bot_sup_eq] at h
  exact h

theorem el_dot_span {k : ℕ} {ι : Type} (A : ι → Fin k → ZMod 2) (x : Fin k → ZMod 2) :
    (∀ i, dotProduct (A i) x = 0) ↔
      ∀ v ∈ Submodule.span (ZMod 2) (Set.range A), dotProduct v x = 0 := by
  constructor
  · intro h v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact h i
    | zero => exact zero_dotProduct x
    | add a b _ _ ha hb => rw [add_dotProduct, ha, hb, add_zero]
    | smul c v _ hv => rw [smul_dotProduct, hv, smul_zero]
  · intro h i
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)

theorem elim_spec {k r m : ℕ} (Q : Fin m → Fin k → ZMod 2) :
    ((elim Q : Fin (r+1) → Fin k → ZMod 2) (Fin.last r) = 0 ↔
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Q)) ≤ r) ∧
    ((elim Q : Fin (r+1) → Fin k → ZMod 2) (Fin.last r) = 0 →
      ∀ x : Fin k → ZMod 2,
        (∀ j, dotProduct ((elim Q : Fin (r+1) → Fin k → ZMod 2) j) x = 0) ↔
          (∀ i, dotProduct (Q i) x = 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := el_inv_elim (r := r) Q
  generalize (elim Q : Fin (r+1) → Fin k → ZMod 2) = S at h1 h2 h3 h4 ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hl
    rw [← h4 hl]
    have hle : Submodule.span (ZMod 2) (Set.range S) ≤
        Submodule.span (ZMod 2) (Set.range (fun j : Fin r => S j.castSucc)) := by
      rw [Submodule.span_le]
      rintro v ⟨j, rfl⟩
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [hl]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨i, rfl⟩
    calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range S))
        ≤ Module.finrank (ZMod 2)
            (Submodule.span (ZMod 2) (Set.range (fun j : Fin r => S j.castSucc))) :=
          Submodule.finrank_mono hle
      _ ≤ Fintype.card (Fin r) := finrank_range_le_card _
      _ = r := Fintype.card_fin r
  · intro hf
    by_contra hl
    have hnz : ∀ j, S j ≠ 0 := fun j hj => hl (h2 j _ (Fin.le_last j) hj)
    have hli : LinearIndependent (ZMod 2) S := by
      rw [Fintype.linearIndependent_iff]
      intro c hc j
      exact h3 c hc j (hnz j)
    have hc := finrank_span_eq_card hli
    have hm := Submodule.finrank_mono h1
    rw [hc, Fintype.card_fin] at hm
    omega
  · intro hl x
    rw [el_dot_span S x, el_dot_span Q x, h4 hl]


-- ---------------------------------------------------------------- index facts

theorem sc_ix_add {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ix hk ((ix hk a).val + b) = ix hk (a + b) := by
  apply Fin.ext
  show (a % k + b) % k = (a + b) % k
  exact Nat.mod_add_mod a k b

theorem sc_ix_per {k : ℕ} (hk : 0 < k) (a : ℕ) : ix hk (a + k) = ix hk a := by
  apply Fin.ext
  show (a + k) % k = a % k
  exact Nat.add_mod_right a k

theorem sc_ix_val {k : ℕ} (hk : 0 < k) (t : Fin k) : ix hk t.val = t := by
  apply Fin.ext
  show t.val % k = t.val
  exact Nat.mod_eq_of_lt t.isLt

theorem sc_ix_of_eq {k : ℕ} (hk : 0 < k) (a b c d : ℕ) (h : a + c * k = b + d * k) :
    ix hk a = ix hk b := by
  apply Fin.ext
  show a % k = b % k
  have h1 : (a + c * k) % k = (b + d * k) % k := by rw [h]
  rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at h1

theorem sc_mod_sub {k : ℕ} (hk : 0 < k) (a b s : ℕ) (hs : s ≤ b * k) :
    (a % k + k - s % k) % k = (a + b * k - s) % k := by
  have h1 : s % k < k := Nat.mod_lt _ hk
  have h2 : k * (s / k) + s % k = s := Nat.div_add_mod s k
  apply Nat.ModEq.add_right_cancel' s
  show (a % k + k - s % k + s) % k = (a + b * k - s + s) % k
  have e1 : a % k + k - s % k + s = a % k + k * (s / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have e2 : a + b * k - s + s = a + b * k := by omega
  rw [e1, e2, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem sc_ix_sub {k : ℕ} (hk : 0 < k) (a b s : ℕ) (hs : s ≤ b * k) :
    ix hk ((ix hk a).val + k - s % k) = ix hk (a + b * k - s) := by
  apply Fin.ext
  show (a % k + k - s % k) % k = (a + b * k - s) % k
  exact sc_mod_sub hk a b s hs

theorem sc_rot {k : ℕ} (hk : 0 < k) (x : Fin k → ZMod 2) (a b s : ℕ) (hs : s ≤ b * k) :
    rot hk s x (ix hk a) = x (ix hk (a + b * k - s)) := by
  show x (ix hk ((ix hk a).val + k - s % k)) = x (ix hk (a + b * k - s))
  rw [sc_ix_sub hk a b s hs]

theorem sc_lin_false {k : ℕ} (hk : 0 < k) (x : Fin k → ZMod 2) (v : ℕ) :
    lin hk false x (ix hk v) =
      x (ix hk (v + 5 * k - 2)) + x (ix hk (v + 5 * k - 1)) + x (ix hk v) := by
  have e1 : lin hk false x (ix hk v) = rot hk 1 x (ix hk v) +
      rot hk 1 x (ix hk ((ix hk v).val + 1)) +
      rot hk 1 x (ix hk ((ix hk v).val + k - 1 % k)) := rfl
  rw [e1, sc_ix_add, sc_ix_sub hk v 1 1 (by omega), sc_rot hk x v 5 1 (by omega),
    sc_rot hk x (v + 1) 1 1 (by omega), sc_rot hk x (v + 1 * k - 1) 4 1 (by omega)]
  have i1 : ix hk (v + 1 + 1 * k - 1) = ix hk v := sc_ix_of_eq hk _ _ 0 1 (by omega)
  have i2 : ix hk (v + 1 * k - 1 + 4 * k - 1) = ix hk (v + 5 * k - 2) :=
    sc_ix_of_eq hk _ _ 0 0 (by omega)
  rw [i1, i2]
  ring

theorem sc_lin_true {k : ℕ} (hk : 0 < k) (x : Fin k → ZMod 2) (v : ℕ) :
    lin hk true x (ix hk v) =
      x (ix hk (v + 5 * k - 5)) + x (ix hk (v + 5 * k - 3)) + x (ix hk (v + 5 * k - 1)) := by
  have e1 : lin hk true x (ix hk v) = rot hk 3 x (ix hk v) +
      rot hk 3 x (ix hk ((ix hk v).val + 2)) +
      rot hk 3 x (ix hk ((ix hk v).val + k - 2 % k)) := rfl
  rw [e1, sc_ix_add, sc_ix_sub hk v 2 2 (by omega), sc_rot hk x v 5 3 (by omega),
    sc_rot hk x (v + 2) 5 3 (by omega), sc_rot hk x (v + 2 * k - 2) 3 3 (by omega)]
  have i1 : ix hk (v + 2 + 5 * k - 3) = ix hk (v + 5 * k - 1) :=
    sc_ix_of_eq hk _ _ 0 0 (by omega)
  have i2 : ix hk (v + 2 * k - 2 + 3 * k - 3) = ix hk (v + 5 * k - 5) :=
    sc_ix_of_eq hk _ _ 0 0 (by omega)
  rw [i1, i2]
  ring

-- ---------------------------------------------------------------- ZMod 2 facts

theorem sc_add_eq_zero : ∀ a b : ZMod 2, a + b = 0 ↔ b = a := by decide

theorem sc_add3_eq_zero : ∀ a b c : ZMod 2, a + b + c = 0 ↔ c = a + b := by decide

theorem sc_add4_eq_zero : ∀ a b c d : ZMod 2, a + b + d + c = 0 ↔ a + b + c = d := by decide

-- ---------------------------------------------------------------- sums

theorem sc_bsrc_val {r : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (b : Bool) :
    Src.val mr mc mcol (bsrc b) = if b then 1 else 0 := by
  cases b <;> rfl

theorem sc_sum_idx {r s : ℕ} (f : Idx r s → ZMod 2) :
    ∑ i, f i = (∑ j : Fin 5, f (Sum.inl (Sum.inl j))) + (∑ j : Fin 5, f (Sum.inl (Sum.inr j))) +
      ((∑ i : Fin r, f (Sum.inr (Sum.inl i))) + ∑ i : Fin s, f (Sum.inr (Sum.inr i))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]

theorem sc_holds_cvec {r s : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (fw fp : Fin 5 → Src r) (fa : Fin r → Src r) (fs : Fin s → Src r) (c : Src r)
    (fw' fp' : Fin 5 → Src r) (fa' : Fin r → Src r) (fs' : Fin s → Src r)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    holds mr mc mcol ((cvec fw fp fa fs, c, cvec fw' fp' fa' fs') : SEq r s) Y xt Y' ↔
    ((∑ j : Fin 5, Src.val mr mc mcol (fw j) * Y (Sum.inl (Sum.inl j))) +
      (∑ j : Fin 5, Src.val mr mc mcol (fp j) * Y (Sum.inl (Sum.inr j))) +
      ((∑ i : Fin r, Src.val mr mc mcol (fa i) * Y (Sum.inr (Sum.inl i))) +
        ∑ i : Fin s, Src.val mr mc mcol (fs i) * Y (Sum.inr (Sum.inr i)))) +
     Src.val mr mc mcol c * xt +
     ((∑ j : Fin 5, Src.val mr mc mcol (fw' j) * Y' (Sum.inl (Sum.inl j))) +
      (∑ j : Fin 5, Src.val mr mc mcol (fp' j) * Y' (Sum.inl (Sum.inr j))) +
      ((∑ i : Fin r, Src.val mr mc mcol (fa' i) * Y' (Sum.inr (Sum.inl i))) +
        ∑ i : Fin s, Src.val mr mc mcol (fs' i) * Y' (Sum.inr (Sum.inr i)))) = 0 := by
  unfold holds
  rw [sc_sum_idx, sc_sum_idx]
  exact Iff.rfl

theorem sc_holds_zero {r s : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    holds mr mc mcol (zeroEq : SEq r s) Y xt Y' := by
  unfold holds zeroEq
  simp [Src.val]

theorem sc_sum_zsrc {r : ℕ} {ι : Type} [Fintype ι] (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (y : ι → ZMod 2) :
    ∑ j : ι, Src.val mr mc mcol ((zsrc : ι → Src r) j) * y j = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  show (0 : ZMod 2) * y j = 0
  exact zero_mul _

theorem sc_sum_dec {r n : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (p : Fin n → Prop) [DecidablePred p] (j : Fin n) (hp : ∀ i, p i ↔ i = j)
    (y : Fin n → ZMod 2) :
    ∑ i : Fin n, Src.val mr mc mcol (bsrc (decide (p i))) * y i = y j := by
  rw [Finset.sum_eq_single j]
  · rw [sc_bsrc_val, decide_eq_true ((hp j).2 rfl)]
    simp
  · intro i _ hij
    rw [sc_bsrc_val, decide_eq_false (fun h => hij ((hp i).1 h))]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem sc_sum_bsrc_eq {r n : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (j : Fin n)
    (y : Fin n → ZMod 2) :
    ∑ i : Fin n, Src.val mr mc mcol (bsrc (decide (i = j))) * y i = y j :=
  sc_sum_dec mr mc mcol (fun i => i = j) j (fun _ => Iff.rfl) y

theorem sc_sum_w_succ {r : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (j : Fin 4)
    (y : Fin 5 → ZMod 2) :
    ∑ i : Fin 5, Src.val mr mc mcol (bsrc (decide (i.val = j.val + 1))) * y i = y j.succ :=
  sc_sum_dec mr mc mcol (fun i : Fin 5 => i.val = j.val + 1) j.succ
    (fun i => ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩) y

theorem sc_sum_w_cast {r : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (j : Fin 4)
    (y : Fin 5 → ZMod 2) :
    ∑ i : Fin 5, Src.val mr mc mcol (bsrc (decide (i.val = j.val))) * y i = y j.castSucc :=
  sc_sum_dec mr mc mcol (fun i : Fin 5 => i.val = j.val) j.castSucc
    (fun i => ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩) y

theorem sc_sum_w4 {r : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (y : Fin 5 → ZMod 2) :
    ∑ i : Fin 5, Src.val mr mc mcol (bsrc (decide (i.val = 4))) * y i = y 4 :=
  sc_sum_dec mr mc mcol (fun i : Fin 5 => i.val = 4) 4
    (fun i => ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩) y

theorem sc_sum_w34 {r : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (y : Fin 5 → ZMod 2) :
    ∑ i : Fin 5, Src.val mr mc mcol (bsrc (decide (i.val = 3 ∨ i.val = 4))) * y i = y 3 + y 4 := by
  rw [Fin.sum_univ_five]
  simp [sc_bsrc_val]

theorem sc_sum_w13 {r : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (y : Fin 5 → ZMod 2) :
    ∑ i : Fin 5, Src.val mr mc mcol (bsrc (decide (i.val = 1 ∨ i.val = 3))) * y i = y 1 + y 3 := by
  rw [Fin.sum_univ_five]
  simp [sc_bsrc_val]

theorem sc_sum_mr {r : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (y : Fin 5 → ZMod 2) :
    ∑ i : Fin 5, Src.val mr mc mcol (if i.val = 2 then Src.mr else Src.c0) * y i =
      (if mr then 1 else 0) * y 2 := by
  rw [Fin.sum_univ_five]
  simp [Src.val]

theorem sc_sum_mc {r : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (y : Fin 5 → ZMod 2) :
    ∑ i : Fin 5, Src.val mr mc mcol (Src.mc : Src r) * y i =
      (if mc then 1 else 0) * (y 0 + y 1 + y 2 + y 3 + y 4) := by
  rw [Fin.sum_univ_five]
  simp only [Src.val]
  ring

theorem sc_sum_sh {r s : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2) (α : Fin s → ZMod 2)
    (y : Fin s → ZMod 2) :
    ∑ i : Fin s, Src.val mr mc mcol (bsrc (decide (α i ≠ 0))) * y i = dotProduct α y := by
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [sc_bsrc_val]
  have h : ∀ a : ZMod 2, (if decide (a ≠ 0) = true then (1 : ZMod 2) else 0) = a := by decide
  rw [h]

-- ---------------------------------------------------------------- the equations, one group at a time

theorem sc_p1 {r s : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    (∀ j : Fin 4, holds mr mc mcol
      ((cvec (fun i => bsrc (decide (i.val = j.val+1))) zsrc zsrc zsrc, Src.c0,
        cvec (fun i => bsrc (decide (i.val = j.val))) zsrc zsrc zsrc) : SEq r s) Y xt Y') ↔
    ∀ j : Fin 4, Y' (Sum.inl (Sum.inl j.castSucc)) = Y (Sum.inl (Sum.inl j.succ)) := by
  refine forall_congr' (fun j => ?_)
  rw [sc_holds_cvec]
  simp only [sc_sum_zsrc, sc_sum_w_succ, sc_sum_w_cast]
  simp only [Src.val, zero_mul, add_zero, zero_add]
  exact sc_add_eq_zero _ _

theorem sc_p2 {r s : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    holds mr mc mcol
      ((cvec zsrc zsrc zsrc zsrc, Src.c1,
        cvec (fun i => bsrc (decide (i.val = 4))) zsrc zsrc zsrc) : SEq r s) Y xt Y' ↔
    Y' (Sum.inl (Sum.inl 4)) = xt := by
  rw [sc_holds_cvec]
  simp only [sc_sum_zsrc, sc_sum_w4]
  simp only [Src.val, zero_mul, one_mul, add_zero, zero_add]
  exact sc_add_eq_zero _ _

theorem sc_p3 {r s : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    (∀ j : Fin 5, holds mr mc mcol
      ((cvec zsrc (fun i => bsrc (decide (i = j))) zsrc zsrc, Src.c0,
        cvec zsrc (fun i => bsrc (decide (i = j))) zsrc zsrc) : SEq r s) Y xt Y') ↔
    ∀ j : Fin 5, Y' (Sum.inl (Sum.inr j)) = Y (Sum.inl (Sum.inr j)) := by
  refine forall_congr' (fun j => ?_)
  rw [sc_holds_cvec]
  simp only [sc_sum_zsrc, sc_sum_bsrc_eq]
  simp only [Src.val, zero_mul, add_zero, zero_add]
  exact sc_add_eq_zero _ _

theorem sc_p4 {r s : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    (∀ j : Fin r, holds mr mc mcol
      ((cvec zsrc zsrc (fun i => bsrc (decide (i = j))) zsrc, Src.mb j,
        cvec zsrc zsrc (fun i => bsrc (decide (i = j))) zsrc) : SEq r s) Y xt Y') ↔
    ∀ i : Fin r, Y' (Sum.inr (Sum.inl i)) = Y (Sum.inr (Sum.inl i)) + mcol i * xt := by
  refine forall_congr' (fun j => ?_)
  rw [sc_holds_cvec]
  simp only [sc_sum_zsrc, sc_sum_bsrc_eq]
  simp only [Src.val, zero_mul, add_zero, zero_add]
  exact sc_add3_eq_zero _ _ _

theorem sc_p5 {r s : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    (∀ j : Fin s, holds mr mc mcol
      ((cvec zsrc zsrc zsrc (fun i => bsrc (decide (i = j))), Src.c0,
        cvec zsrc zsrc zsrc (fun i => bsrc (decide (i = j)))) : SEq r s) Y xt Y') ↔
    ∀ i : Fin s, Y' (Sum.inr (Sum.inr i)) = Y (Sum.inr (Sum.inr i)) := by
  refine forall_congr' (fun j => ?_)
  rw [sc_holds_cvec]
  simp only [sc_sum_zsrc, sc_sum_bsrc_eq]
  simp only [Src.val, zero_mul, add_zero, zero_add]
  exact sc_add_eq_zero _ _

theorem sc_p6 {r s : ℕ} (t : ℕ) (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    (∀ q ∈ (if t = 0 then
        List.ofFn (fun j : Fin 5 =>
          ((cvec (fun i => bsrc (decide (i = j))) (fun i => bsrc (decide (i = j))) zsrc zsrc, Src.c0,
            cvec zsrc zsrc zsrc zsrc) : SEq r s)) ++
        List.ofFn (fun j : Fin r =>
          ((cvec zsrc zsrc (fun i => bsrc (decide (i = j))) zsrc, Src.c0,
            cvec zsrc zsrc zsrc zsrc) : SEq r s))
       else []), holds mr mc mcol q Y xt Y') ↔
    (t = 0 → (∀ j : Fin 5, Y (Sum.inl (Sum.inl j)) = Y (Sum.inl (Sum.inr j))) ∧
      ∀ i : Fin r, Y (Sum.inr (Sum.inl i)) = 0) := by
  by_cases h : t = 0
  · rw [if_pos h]
    simp only [List.forall_mem_append, List.forall_mem_ofFn_iff, sc_holds_cvec, sc_sum_zsrc, sc_sum_bsrc_eq]
    simp only [Src.val, zero_mul, add_zero, zero_add]
    constructor
    · rintro ⟨h1, h2⟩ _
      exact ⟨fun j => ((sc_add_eq_zero _ _).1 (h1 j)).symm, h2⟩
    · intro h1
      exact ⟨fun j => (sc_add_eq_zero _ _).2 ((h1 h).1 j).symm, (h1 h).2⟩
  · rw [if_neg h]
    constructor
    · intro _ h0
      exact absurd h0 h
    · intro _ q hq
      exact absurd hq (List.not_mem_nil)

theorem sc_p7 {r s : ℕ} (k t : ℕ) (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    (∀ q ∈ (if t + 1 = k then
        List.ofFn (fun j : Fin 5 =>
          ((cvec zsrc zsrc zsrc zsrc, Src.c0,
            cvec (fun i => bsrc (decide (i = j))) (fun i => bsrc (decide (i = j))) zsrc zsrc) :
              SEq r s)) ++
        List.ofFn (fun j : Fin r =>
          ((cvec zsrc zsrc zsrc zsrc, Src.c0,
            cvec zsrc zsrc (fun i => bsrc (decide (i = j))) zsrc) : SEq r s))
       else []), holds mr mc mcol q Y xt Y') ↔
    (t + 1 = k → (∀ j : Fin 5, Y' (Sum.inl (Sum.inl j)) = Y' (Sum.inl (Sum.inr j))) ∧
      ∀ i : Fin r, Y' (Sum.inr (Sum.inl i)) = 0) := by
  by_cases h : t + 1 = k
  · rw [if_pos h]
    simp only [List.forall_mem_append, List.forall_mem_ofFn_iff, sc_holds_cvec, sc_sum_zsrc, sc_sum_bsrc_eq]
    simp only [Src.val, zero_mul, add_zero, zero_add]
    constructor
    · rintro ⟨h1, h2⟩ _
      exact ⟨fun j => ((sc_add_eq_zero _ _).1 (h1 j)).symm, h2⟩
    · intro h1
      exact ⟨fun j => (sc_add_eq_zero _ _).2 ((h1 h).1 j).symm, (h1 h).2⟩
  · rw [if_neg h]
    constructor
    · intro _ h0
      exact absurd h0 h
    · intro _ q hq
      exact absurd hq (List.not_mem_nil)

theorem sc_p8 {r s : ℕ} (cr : Option (Fin s → ZMod 2)) (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    holds mr mc mcol
      (match cr with
        | some α => ((cvec (fun i => bsrc (decide (i.val = 3 ∨ i.val = 4))) zsrc zsrc
            (fun i => bsrc (decide (α i ≠ 0))), Src.c1, cvec zsrc zsrc zsrc zsrc) : SEq r s)
        | none => zeroEq) Y xt Y' ↔
    (∀ α, cr = some α → Y (Sum.inl (Sum.inl 3)) + Y (Sum.inl (Sum.inl 4)) + xt =
      dotProduct α (fun i => Y (Sum.inr (Sum.inr i)))) := by
  cases cr with
  | none =>
    constructor
    · intro _ α h
      exact absurd h (by simp)
    · intro _
      exact sc_holds_zero mr mc mcol Y xt Y'
  | some α =>
    show holds mr mc mcol ((cvec (fun i => bsrc (decide (i.val = 3 ∨ i.val = 4))) zsrc zsrc
            (fun i => bsrc (decide (α i ≠ 0))), Src.c1, cvec zsrc zsrc zsrc zsrc) : SEq r s)
            Y xt Y' ↔ _
    rw [sc_holds_cvec]
    simp only [sc_sum_zsrc, sc_sum_w34, sc_sum_sh]
    simp only [Src.val, zero_mul, one_mul, add_zero, zero_add]
    constructor
    · intro h β hβ
      obtain rfl : α = β := Option.some.inj hβ
      exact (sc_add4_eq_zero _ _ _ _).1 h
    · intro h
      exact (sc_add4_eq_zero _ _ _ _).2 (h α rfl)

theorem sc_p9 {r s : ℕ} (cc : Option (Fin s → ZMod 2)) (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    holds mr mc mcol
      (match cc with
        | some β => ((cvec (fun i => bsrc (decide (i.val = 1 ∨ i.val = 3))) zsrc zsrc
            (fun i => bsrc (decide (β i ≠ 0))), Src.c1, cvec zsrc zsrc zsrc zsrc) : SEq r s)
        | none => zeroEq) Y xt Y' ↔
    (∀ β, cc = some β → Y (Sum.inl (Sum.inl 1)) + Y (Sum.inl (Sum.inl 3)) + xt =
      dotProduct β (fun i => Y (Sum.inr (Sum.inr i)))) := by
  cases cc with
  | none =>
    constructor
    · intro _ α h
      exact absurd h (by simp)
    · intro _
      exact sc_holds_zero mr mc mcol Y xt Y'
  | some α =>
    show holds mr mc mcol ((cvec (fun i => bsrc (decide (i.val = 1 ∨ i.val = 3))) zsrc zsrc
            (fun i => bsrc (decide (α i ≠ 0))), Src.c1, cvec zsrc zsrc zsrc zsrc) : SEq r s)
            Y xt Y' ↔ _
    rw [sc_holds_cvec]
    simp only [sc_sum_zsrc, sc_sum_w13, sc_sum_sh]
    simp only [Src.val, zero_mul, one_mul, add_zero, zero_add]
    constructor
    · intro h β hβ
      obtain rfl : α = β := Option.some.inj hβ
      exact (sc_add4_eq_zero _ _ _ _).1 h
    · intro h
      exact (sc_add4_eq_zero _ _ _ _).2 (h α rfl)

theorem sc_p10 {r s : ℕ} (pr cr : Option (Fin s → ZMod 2)) (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    holds mr mc mcol
      (if pr.isNone && cr.isNone then
        ((cvec (fun i => if i.val = 2 then Src.mr else Src.c0) zsrc zsrc zsrc, Src.mr,
          cvec zsrc zsrc zsrc zsrc) : SEq r s)
       else zeroEq) Y xt Y' ↔
    (pr = none → cr = none → mr = true → Y (Sum.inl (Sum.inl 2)) = xt) := by
  by_cases h : (pr.isNone && cr.isNone) = true
  · rw [if_pos h, sc_holds_cvec]
    simp only [sc_sum_zsrc, sc_sum_mr]
    simp only [Src.val, zero_mul, add_zero, zero_add]
    have h1 : pr = none := by
      cases pr with
      | none => rfl
      | some a => simp at h
    have h2 : cr = none := by
      cases cr with
      | none => rfl
      | some a => simp at h
    cases mr with
    | false => simp
    | true =>
      simp only [ite_true, one_mul]
      constructor
      · intro h3 _ _ _
        exact ((sc_add_eq_zero _ _).1 h3).symm
      · intro h3
        exact (sc_add_eq_zero _ _).2 (h3 h1 h2 trivial).symm
  · rw [if_neg h]
    constructor
    · intro _ h1 h2 _
      subst h1
      subst h2
      exact absurd rfl h
    · intro _
      exact sc_holds_zero mr mc mcol Y xt Y'

theorem sc_p11 {r s : ℕ} (pc cc : Option (Fin s → ZMod 2)) (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    holds mr mc mcol
      (if pc.isNone && cc.isNone then
        ((cvec (fun _ => Src.mc) zsrc zsrc zsrc, Src.mc, cvec zsrc zsrc zsrc zsrc) : SEq r s)
       else zeroEq) Y xt Y' ↔
    (pc = none → cc = none → mc = true →
      Y (Sum.inl (Sum.inl 0)) + Y (Sum.inl (Sum.inl 1)) + Y (Sum.inl (Sum.inl 2)) +
        Y (Sum.inl (Sum.inl 3)) + Y (Sum.inl (Sum.inl 4)) = xt) := by
  by_cases h : (pc.isNone && cc.isNone) = true
  · rw [if_pos h, sc_holds_cvec]
    simp only [sc_sum_zsrc, sc_sum_mc, zero_mul, add_zero, zero_add]
    have h1 : pc = none := by
      cases pc with
      | none => rfl
      | some a => simp at h
    have h2 : cc = none := by
      cases cc with
      | none => rfl
      | some a => simp at h
    cases mc with
    | false => simp [Src.val]
    | true =>
      simp only [Src.val, ite_true, one_mul]
      constructor
      · intro h3 _ _ _
        exact ((sc_add_eq_zero _ _).1 h3).symm
      · intro h3
        exact (sc_add_eq_zero _ _).2 (h3 h1 h2 trivial).symm
  · rw [if_neg h]
    constructor
    · intro _ h1 h2 _
      subst h1
      subst h2
      exact absurd rfl h
    · intro _
      exact sc_holds_zero mr mc mcol Y xt Y'

theorem sc_holds_all {r s : ℕ} (k t : ℕ) (pr pc cr cc : Option (Fin s → ZMod 2))
    (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    (∀ q ∈ (eqs k t pr pc cr cc : List (SEq r s)), holds mr mc mcol q Y xt Y') ↔
    ((∀ j : Fin 4, Y' (Sum.inl (Sum.inl j.castSucc)) = Y (Sum.inl (Sum.inl j.succ))) ∧
     Y' (Sum.inl (Sum.inl 4)) = xt ∧
     (∀ j : Fin 5, Y' (Sum.inl (Sum.inr j)) = Y (Sum.inl (Sum.inr j))) ∧
     (∀ i : Fin r, Y' (Sum.inr (Sum.inl i)) = Y (Sum.inr (Sum.inl i)) + mcol i * xt) ∧
     (∀ i : Fin s, Y' (Sum.inr (Sum.inr i)) = Y (Sum.inr (Sum.inr i))) ∧
     (t = 0 → (∀ j : Fin 5, Y (Sum.inl (Sum.inl j)) = Y (Sum.inl (Sum.inr j))) ∧
       ∀ i : Fin r, Y (Sum.inr (Sum.inl i)) = 0) ∧
     (t + 1 = k → (∀ j : Fin 5, Y' (Sum.inl (Sum.inl j)) = Y' (Sum.inl (Sum.inr j))) ∧
       ∀ i : Fin r, Y' (Sum.inr (Sum.inl i)) = 0) ∧
     (∀ α, cr = some α → Y (Sum.inl (Sum.inl 3)) + Y (Sum.inl (Sum.inl 4)) + xt =
       dotProduct α (fun i => Y (Sum.inr (Sum.inr i)))) ∧
     (∀ β, cc = some β → Y (Sum.inl (Sum.inl 1)) + Y (Sum.inl (Sum.inl 3)) + xt =
       dotProduct β (fun i => Y (Sum.inr (Sum.inr i)))) ∧
     (pr = none → cr = none → mr = true → Y (Sum.inl (Sum.inl 2)) = xt) ∧
     (pc = none → cc = none → mc = true →
       Y (Sum.inl (Sum.inl 0)) + Y (Sum.inl (Sum.inl 1)) + Y (Sum.inl (Sum.inl 2)) +
         Y (Sum.inl (Sum.inl 3)) + Y (Sum.inl (Sum.inl 4)) = xt)) := by
  unfold eqs
  simp only [List.forall_mem_append, List.forall_mem_ofFn_iff, List.forall_mem_singleton]
  refine Iff.trans (and_congr (and_congr (and_congr (and_congr (and_congr (and_congr (and_congr
    (and_congr (and_congr (and_congr
      (sc_p1 mr mc mcol Y xt Y') (sc_p2 mr mc mcol Y xt Y')) (sc_p3 mr mc mcol Y xt Y'))
      (sc_p4 mr mc mcol Y xt Y')) (sc_p5 mr mc mcol Y xt Y')) (sc_p6 t mr mc mcol Y xt Y'))
      (sc_p7 k t mr mc mcol Y xt Y')) (sc_p8 cr mr mc mcol Y xt Y'))
      (sc_p9 cc mr mc mcol Y xt Y')) (sc_p10 pr cr mr mc mcol Y xt Y'))
      (sc_p11 pc cc mr mc mcol Y xt Y')) ?_
  simp only [and_assoc]

-- ---------------------------------------------------------------- one scan step, unpacked

def sc_Step {k : ℕ} (hk : 0 < k) {r s : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) (t : ℕ) (Y Y' : Idx r s → ZMod 2) : Prop :=
  (∀ j : Fin 4, Y' (Sum.inl (Sum.inl j.castSucc)) = Y (Sum.inl (Sum.inl j.succ))) ∧
  Y' (Sum.inl (Sum.inl 4)) = x (ix hk t) ∧
  (∀ j : Fin 5, Y' (Sum.inl (Sum.inr j)) = Y (Sum.inl (Sum.inr j))) ∧
  (∀ i : Fin r, Y' (Sum.inr (Sum.inl i)) =
    Y (Sum.inr (Sum.inl i)) + M i (ix hk t) * x (ix hk t)) ∧
  (∀ i : Fin s, Y' (Sum.inr (Sum.inr i)) = Y (Sum.inr (Sum.inr i))) ∧
  (t = 0 → (∀ j : Fin 5, Y (Sum.inl (Sum.inl j)) = Y (Sum.inl (Sum.inr j))) ∧
    ∀ i : Fin r, Y (Sum.inr (Sum.inl i)) = 0) ∧
  (t + 1 = k → (∀ j : Fin 5, Y' (Sum.inl (Sum.inl j)) = Y' (Sum.inl (Sum.inr j))) ∧
    ∀ i : Fin r, Y' (Sum.inr (Sum.inl i)) = 0) ∧
  (∀ α, lab false (ix hk t) = some α →
    Y (Sum.inl (Sum.inl 3)) + Y (Sum.inl (Sum.inl 4)) + x (ix hk t) =
      dotProduct α (fun i => Y (Sum.inr (Sum.inr i)))) ∧
  (∀ β, lab true (ix hk (t+1)) = some β →
    Y (Sum.inl (Sum.inl 1)) + Y (Sum.inl (Sum.inl 3)) + x (ix hk t) =
      dotProduct β (fun i => Y (Sum.inr (Sum.inr i)))) ∧
  (lab false (ix hk (t+k-1)) = none → lab false (ix hk t) = none →
    marked false (ix hk (t+2*k-2)) = true → Y (Sum.inl (Sum.inl 2)) = x (ix hk t)) ∧
  (lab true (ix hk t) = none → lab true (ix hk (t+1)) = none →
    marked true (ix hk (t+k-1)) = true →
    Y (Sum.inl (Sum.inl 0)) + Y (Sum.inl (Sum.inl 1)) + Y (Sum.inl (Sum.inl 2)) +
      Y (Sum.inl (Sum.inl 3)) + Y (Sum.inl (Sum.inl 4)) = x (ix hk t))

theorem sc_step_iff {k : ℕ} (hk : 0 < k) {r s : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) (t : Fin k) (Y Y' : Idx r s → ZMod 2) :
    (∀ q ∈ (eqs k t.val (lab false (ix hk (t.val+k-1))) (lab true (ix hk t.val))
          (lab false (ix hk t.val)) (lab true (ix hk (t.val+1))) : List (SEq r s)),
        holds (marked false (ix hk (t.val+2*k-2))) (marked true (ix hk (t.val+k-1)))
          (fun i => M i t) q Y (x t) Y') ↔
    sc_Step hk marked M lab x t.val Y Y' := by
  rw [sc_holds_all]
  unfold sc_Step
  rw [sc_ix_val hk t]

-- ---------------------------------------------------------------- window facts

theorem sc_row_lab {k : ℕ} (hk : 0 < k) (x : Fin k → ZMod 2) (t : ℕ) :
    x (ix hk (t+5*k-5+3)) + x (ix hk (t+5*k-5+4)) + x (ix hk t) =
      lin hk false x (ix hk t) := by
  rw [sc_lin_false]
  have e1 : t+5*k-5+3 = t+5*k-2 := by omega
  have e2 : t+5*k-5+4 = t+5*k-1 := by omega
  rw [e1, e2]

theorem sc_col_lab {k : ℕ} (hk : 0 < k) (x : Fin k → ZMod 2) (t : ℕ) :
    x (ix hk (t+5*k-5+1)) + x (ix hk (t+5*k-5+3)) + x (ix hk t) =
      lin hk true x (ix hk (t+1)) := by
  rw [sc_lin_true]
  have e1 : t+1+5*k-5 = t+5*k-5+1 := by omega
  have e2 : t+1+5*k-3 = t+5*k-5+3 := by omega
  have e3 : ix hk (t+1+5*k-1) = ix hk t := sc_ix_of_eq hk _ _ 0 5 (by omega)
  rw [e1, e2, e3]

theorem sc_row_free {k : ℕ} (hk : 0 < k) (x : Fin k → ZMod 2) (t : ℕ) :
    (x (ix hk (t+5*k-5+2)) = x (ix hk t)) ↔
      lin hk false x (ix hk (t+k-1)) = lin hk false x (ix hk t) := by
  rw [sc_lin_false, sc_lin_false]
  have e1 : ix hk (t+k-1+5*k-2) = ix hk (t+5*k-5+2) := sc_ix_of_eq hk _ _ 0 1 (by omega)
  have e2 : ix hk (t+k-1+5*k-1) = ix hk (t+5*k-2) := sc_ix_of_eq hk _ _ 0 1 (by omega)
  have e3 : ix hk (t+k-1) = ix hk (t+5*k-1) := sc_ix_of_eq hk _ _ 4 0 (by omega)
  rw [e1, e2, e3]
  have h : ∀ a b c d : ZMod 2, (a = d) ↔ (a + b + c = b + c + d) := by decide
  exact h _ _ _ _

theorem sc_col_free {k : ℕ} (hk : 0 < k) (x : Fin k → ZMod 2) (t : ℕ) :
    (x (ix hk (t+5*k-5+0)) + x (ix hk (t+5*k-5+1)) + x (ix hk (t+5*k-5+2)) +
      x (ix hk (t+5*k-5+3)) + x (ix hk (t+5*k-5+4)) = x (ix hk t)) ↔
      lin hk true x (ix hk t) = lin hk true x (ix hk (t+1)) := by
  rw [← sc_col_lab hk x t, sc_lin_true]
  have e0 : t+5*k-5+0 = t+5*k-5 := rfl
  have e2 : t+5*k-5+2 = t+5*k-3 := by omega
  have e4 : t+5*k-5+4 = t+5*k-1 := by omega
  rw [e0, e2, e4]
  have h : ∀ a b c d e f : ZMod 2, (a + b + c + d + e = f) ↔ (a + c + e = b + d + f) := by
    decide
  exact h _ _ _ _ _ _

theorem sc_ix_add_sub {k : ℕ} (hk : 0 < k) (a b c : ℕ) (h : c ≤ b) :
    ix hk ((ix hk a).val + b - c) = ix hk (a + b - c) := by
  have e1 : (ix hk a).val + b - c = (ix hk a).val + (b - c) := by omega
  have e2 : a + b - c = a + (b - c) := by omega
  rw [e1, e2, sc_ix_add]

theorem sc_psum_succ {k : ℕ} (hk : 0 < k) (a b : Fin k → ZMod 2) (t : ℕ) (ht : t < k) :
    (∑ t' : Fin k, if t'.val < t + 1 then a t' * b t' else 0) =
    (∑ t' : Fin k, if t'.val < t then a t' * b t' else 0) + a (ix hk t) * b (ix hk t) := by
  have hix : (ix hk t).val = t := Nat.mod_eq_of_lt ht
  have h1 : ∀ t' : Fin k, (if t'.val < t + 1 then a t' * b t' else 0) =
      (if t'.val < t then a t' * b t' else 0) + (if t' = ix hk t then a t' * b t' else 0) := by
    intro t'
    by_cases h : t'.val < t
    · have hne : t' ≠ ix hk t := by
        intro e
        rw [e, hix] at h
        exact lt_irrefl _ h
      rw [if_pos h, if_pos (by omega), if_neg hne, add_zero]
    · by_cases h2 : t'.val = t
      · have he : t' = ix hk t := Fin.ext (by rw [hix]; exact h2)
        rw [if_neg h, if_pos (by omega), if_pos he, zero_add]
      · have hne : t' ≠ ix hk t := by
          intro e
          apply h2
          rw [e, hix]
        rw [if_neg h, if_neg (by omega), if_neg hne, add_zero]
  rw [Finset.sum_congr rfl (fun t' _ => h1 t'), Finset.sum_add_distrib]
  simp

-- ---------------------------------------------------------------- direction: from Y to LSol

theorem sc_const {k : ℕ} (hk : 0 < k) {r s : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) (Z : ℕ → Idx r s → ZMod 2)
    (hZ : ∀ t, t < k → sc_Step hk marked M lab x t (Z t) (Z (t+1))) :
    ∀ t, t ≤ k → (∀ j : Fin 5, Z t (Sum.inl (Sum.inr j)) = Z 0 (Sum.inl (Sum.inr j))) ∧
      (∀ i : Fin s, Z t (Sum.inr (Sum.inr i)) = Z 0 (Sum.inr (Sum.inr i))) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ t ih =>
    intro ht
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨_, _, h3, _, h5, _⟩ := hZ t (by omega)
    exact ⟨fun j => (h3 j).trans (h1 j), fun i => (h5 i).trans (h2 i)⟩

theorem sc_acc {k : ℕ} (hk : 0 < k) {r s : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) (Z : ℕ → Idx r s → ZMod 2)
    (hZ : ∀ t, t < k → sc_Step hk marked M lab x t (Z t) (Z (t+1))) :
    ∀ t, t ≤ k → ∀ i : Fin r, Z t (Sum.inr (Sum.inl i)) =
      ∑ t' : Fin k, if t'.val < t then M i t' * x t' else 0 := by
  intro t
  induction t with
  | zero =>
    intro _ i
    obtain ⟨_, _, _, _, _, h6, _⟩ := hZ 0 hk
    rw [(h6 rfl).2 i]
    exact (Finset.sum_eq_zero (fun t' _ => if_neg (Nat.not_lt_zero _))).symm
  | succ t ih =>
    intro ht i
    obtain ⟨_, _, _, h4, _⟩ := hZ t (by omega)
    rw [h4 i, ih (by omega) i, sc_psum_succ hk (M i) x t (by omega)]

def sc_e {k : ℕ} (hk : 0 < k) (x : Fin k → ZMod 2) (w0 : Fin 5 → ZMod 2) (n : ℕ) : ZMod 2 :=
  if h : n < 5 then w0 ⟨n, h⟩ else x (ix hk (n - 5))

theorem sc_e_E {k : ℕ} (hk : 0 < k) (x : Fin k → ZMod 2) (w0 : Fin 5 → ZMod 2)
    (hper : ∀ j : Fin 5, sc_e hk x w0 (k + j.val) = w0 j) :
    ∀ m n : ℕ, k + 5 - n ≤ m → n < k + 5 →
      sc_e hk x w0 n = x (ix hk (n + 5 * k - 5)) := by
  intro m
  induction m with
  | zero =>
    intro n h1 h2
    omega
  | succ m ih =>
    intro n h1 h2
    by_cases h : n < 5
    · have e1 : sc_e hk x w0 n = w0 ⟨n, h⟩ := dif_pos h
      have hp : sc_e hk x w0 (k + n) = w0 ⟨n, h⟩ := hper ⟨n, h⟩
      rw [e1, ← hp, ih (k + n) (by omega) (by omega)]
      exact congrArg x (sc_ix_of_eq hk _ _ 0 1 (by omega))
    · have e1 : sc_e hk x w0 n = x (ix hk (n - 5)) := dif_neg h
      rw [e1]
      exact congrArg x (sc_ix_of_eq hk _ _ 5 0 (by omega))

theorem sc_win_e {k : ℕ} (hk : 0 < k) {r s : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) (Z : ℕ → Idx r s → ZMod 2)
    (hZ : ∀ t, t < k → sc_Step hk marked M lab x t (Z t) (Z (t+1))) :
    ∀ t, t ≤ k → ∀ j : Fin 5, Z t (Sum.inl (Sum.inl j)) =
      sc_e hk x (fun j => Z 0 (Sum.inl (Sum.inl j))) (t + j.val) := by
  intro t
  induction t with
  | zero =>
    intro _ j
    have e : sc_e hk x (fun j => Z 0 (Sum.inl (Sum.inl j))) j.val =
        Z 0 (Sum.inl (Sum.inl j)) := by
      unfold sc_e
      rw [dif_pos j.isLt]
    rw [Nat.zero_add, e]
  | succ t ih =>
    intro ht j
    obtain ⟨h1, h2, _⟩ := hZ t (by omega)
    obtain ⟨j, hj⟩ := j
    by_cases h4 : j < 4
    · have e1 := h1 ⟨j, h4⟩
      have e2 := ih (by omega) (Fin.succ ⟨j, h4⟩)
      have e3 : t + 1 + j = t + (j + 1) := by omega
      show Z (t+1) (Sum.inl (Sum.inl (Fin.castSucc ⟨j, h4⟩))) =
        sc_e hk x (fun j => Z 0 (Sum.inl (Sum.inl j))) (t + 1 + j)
      rw [e1, e2, e3]
      rfl
    · have hj4 : j = 4 := by omega
      subst hj4
      have e1 : sc_e hk x (fun j => Z 0 (Sum.inl (Sum.inl j))) (t + 1 + 4) =
          x (ix hk (t + 1 + 4 - 5)) := dif_neg (by omega)
      have e2 : t + 1 + 4 - 5 = t := by omega
      show Z (t+1) (Sum.inl (Sum.inl 4)) =
        sc_e hk x (fun j => Z 0 (Sum.inl (Sum.inl j))) (t + 1 + 4)
      rw [e1, e2]
      exact h2

theorem sc_win {k : ℕ} (hk : 0 < k) {r s : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) (Z : ℕ → Idx r s → ZMod 2)
    (hZ : ∀ t, t < k → sc_Step hk marked M lab x t (Z t) (Z (t+1))) :
    ∀ t, t ≤ k → ∀ j : Fin 5, Z t (Sum.inl (Sum.inl j)) =
      x (ix hk (t + 5 * k - 5 + j.val)) := by
  intro t ht j
  have hc := sc_const hk marked M lab x Z hZ
  have hw := sc_win_e hk marked M lab x Z hZ
  have hper : ∀ j : Fin 5, sc_e hk x (fun j => Z 0 (Sum.inl (Sum.inl j))) (k + j.val) =
      Z 0 (Sum.inl (Sum.inl j)) := by
    intro j
    rw [← hw k (le_refl k) j]
    obtain ⟨_, _, _, _, _, h6, _⟩ := hZ 0 hk
    obtain ⟨_, _, _, _, _, _, h7, _⟩ := hZ (k-1) (by omega)
    have hk1 : k - 1 + 1 = k := by omega
    have h7' := (h7 hk1).1 j
    rw [hk1] at h7'
    rw [h7', (hc k (le_refl k)).1 j, (h6 rfl).1 j]
  rw [hw t ht j, sc_e_E hk x _ hper (k+5) (t + j.val) (by omega) (by omega)]
  exact congrArg x (congrArg (ix hk) (by omega))

theorem sc_fwdN {k : ℕ} (hk : 0 < k) {r s : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) (Z : ℕ → Idx r s → ZMod 2)
    (hZ : ∀ t, t < k → sc_Step hk marked M lab x t (Z t) (Z (t+1))) :
    LSol hk marked M lab x := by
  have hc := sc_const hk marked M lab x Z hZ
  have hw := sc_win hk marked M lab x Z hZ
  have ha := sc_acc hk marked M lab x Z hZ
  have hw0 : ∀ t, t ≤ k → Z t (Sum.inl (Sum.inl 0)) = x (ix hk (t + 5 * k - 5 + 0)) :=
    fun t ht => hw t ht 0
  have hw1 : ∀ t, t ≤ k → Z t (Sum.inl (Sum.inl 1)) = x (ix hk (t + 5 * k - 5 + 1)) :=
    fun t ht => hw t ht 1
  have hw2 : ∀ t, t ≤ k → Z t (Sum.inl (Sum.inl 2)) = x (ix hk (t + 5 * k - 5 + 2)) :=
    fun t ht => hw t ht 2
  have hw3 : ∀ t, t ≤ k → Z t (Sum.inl (Sum.inl 3)) = x (ix hk (t + 5 * k - 5 + 3)) :=
    fun t ht => hw t ht 3
  have hw4 : ∀ t, t ≤ k → Z t (Sum.inl (Sum.inl 4)) = x (ix hk (t + 5 * k - 5 + 4)) :=
    fun t ht => hw t ht 4
  have hdot : ∀ (t : ℕ), t < k → ∀ α : Fin s → ZMod 2,
      dotProduct α (fun i => Z t (Sum.inr (Sum.inr i))) =
        dotProduct α (fun i => Z 0 (Sum.inr (Sum.inr i))) := by
    intro t ht α
    have e : (fun i => Z t (Sum.inr (Sum.inr i))) = (fun i => Z 0 (Sum.inr (Sum.inr i))) :=
      funext (fun i => (hc t (by omega)).2 i)
    rw [e]
  unfold LSol
  refine ⟨fun i => Z 0 (Sum.inr (Sum.inr i)), ?_, ?_, ?_⟩
  · intro i
    obtain ⟨_, _, _, _, _, _, h7, _⟩ := hZ (k-1) (by omega)
    have hk1 : k - 1 + 1 = k := by omega
    have h7' := (h7 hk1).2 i
    rw [hk1, ha k (le_refl k) i] at h7'
    refine Eq.trans ?_ h7'
    exact Finset.sum_congr rfl (fun t' _ => (if_pos t'.isLt).symm)
  · intro col v α hα
    cases col with
    | false =>
      obtain ⟨_, _, _, _, _, _, _, h8, _⟩ := hZ v.val v.isLt
      have h := h8 α (by rw [sc_ix_val]; exact hα)
      rw [hw3 v.val (by omega), hw4 v.val (by omega), hdot v.val v.isLt α,
        sc_row_lab hk x v.val, sc_ix_val] at h
      exact h
    | true =>
      obtain ⟨t, ht, hv⟩ : ∃ t, t < k ∧ ix hk (t + 1) = v := by
        refine ⟨(ix hk (v.val + k - 1)).val, Fin.isLt _, ?_⟩
        rw [sc_ix_add]
        have e : ix hk (v.val + k - 1 + 1) = ix hk v.val := sc_ix_of_eq hk _ _ 0 1 (by omega)
        rw [e, sc_ix_val]
      obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := hZ t ht
      have h := h9 α (by rw [hv]; exact hα)
      rw [hw1 t (by omega), hw3 t (by omega), hdot t ht α, sc_col_lab hk x t, hv] at h
      exact h
  · intro col j hm h1 h2
    cases col with
    | false =>
      obtain ⟨t, ht, e1, e2, e3⟩ : ∃ t, t < k ∧ ix hk (t + k - 1) = ix hk (j.val + 1) ∧
          ix hk t = ix hk (j.val + 2) ∧ ix hk (t + 2 * k - 2) = j := by
        refine ⟨(ix hk (j.val + 2)).val, Fin.isLt _, ?_, sc_ix_val hk _, ?_⟩
        · rw [sc_ix_add_sub hk _ _ _ (by omega)]
          exact sc_ix_of_eq hk _ _ 0 1 (by omega)
        · rw [sc_ix_add_sub hk _ _ _ (by omega)]
          have e : ix hk (j.val + 2 + 2 * k - 2) = ix hk j.val :=
            sc_ix_of_eq hk _ _ 0 2 (by omega)
          rw [e, sc_ix_val]
      obtain ⟨_, _, _, _, _, _, _, _, _, h10, _⟩ := hZ t ht
      have h := h10 (by rw [e1]; exact h1) (by rw [e2]; exact h2) (by rw [e3]; exact hm)
      rw [hw2 t (by omega), sc_row_free hk x t, e1, e2] at h
      exact h
    | true =>
      obtain ⟨t, ht, e1, e2, e3⟩ : ∃ t, t < k ∧ ix hk t = ix hk (j.val + 1) ∧
          ix hk (t + 1) = ix hk (j.val + 2) ∧ ix hk (t + k - 1) = j := by
        refine ⟨(ix hk (j.val + 1)).val, Fin.isLt _, sc_ix_val hk _, ?_, ?_⟩
        · rw [sc_ix_add]
        · rw [sc_ix_add_sub hk _ _ _ (by omega)]
          have e : ix hk (j.val + 1 + k - 1) = ix hk j.val :=
            sc_ix_of_eq hk _ _ 0 1 (by omega)
          rw [e, sc_ix_val]
      obtain ⟨_, _, _, _, _, _, _, _, _, _, h11⟩ := hZ t ht
      have h := h11 (by rw [e1]; exact h1) (by rw [e2]; exact h2) (by rw [e3]; exact hm)
      rw [hw0 t (by omega), hw1 t (by omega), hw2 t (by omega), hw3 t (by omega),
        hw4 t (by omega), sc_col_free hk x t, e1, e2] at h
      exact h

theorem sc_fwd {k : ℕ} (hk : 0 < k) {r s : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) (Y : Fin (k+1) → Idx r s → ZMod 2)
    (hY : ∀ t : Fin k, sc_Step hk marked M lab x t.val (Y t.castSucc) (Y t.succ)) :
    LSol hk marked M lab x := by
  apply sc_fwdN hk marked M lab x (fun n => if h : n < k + 1 then Y ⟨n, h⟩ else 0)
  intro t ht
  show sc_Step hk marked M lab x t (if h : t < k + 1 then Y ⟨t, h⟩ else 0)
    (if h : t + 1 < k + 1 then Y ⟨t + 1, h⟩ else 0)
  rw [dif_pos (show t < k + 1 by omega), dif_pos (show t + 1 < k + 1 by omega)]
  exact hY ⟨t, ht⟩

-- ---------------------------------------------------------------- direction: from LSol to Y

def sc_Y {k : ℕ} (hk : 0 < k) {r s : ℕ} (M : Fin r → Fin k → ZMod 2) (x : Fin k → ZMod 2)
    (τ : Fin s → ZMod 2) (n : ℕ) : Idx r s → ZMod 2
  | Sum.inl (Sum.inl j) => x (ix hk (n + 5 * k - 5 + j.val))
  | Sum.inl (Sum.inr j) => x (ix hk (5 * k - 5 + j.val))
  | Sum.inr (Sum.inl i) => ∑ t' : Fin k, if t'.val < n then M i t' * x t' else 0
  | Sum.inr (Sum.inr i) => τ i

theorem sc_bwdN {k : ℕ} (hk : 0 < k) {r s : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) (τ : Fin s → ZMod 2)
    (hM : ∀ i, dotProduct (M i) x = 0)
    (hlab : ∀ (col : Bool) (v : Fin k) (α : Fin s → ZMod 2), lab col v = some α →
      lin hk col x v = dotProduct α τ)
    (hfree : ∀ (col : Bool) (j : Fin k), marked col j = true →
      lab col (ix hk (j.val+1)) = none → lab col (ix hk (j.val+2)) = none →
      lin hk col x (ix hk (j.val+1)) = lin hk col x (ix hk (j.val+2)))
    (t : ℕ) (ht : t < k) :
    sc_Step hk marked M lab x t (sc_Y hk M x τ t) (sc_Y hk M x τ (t+1)) := by
  unfold sc_Step
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show x (ix hk (t + 1 + 5 * k - 5 + j.val)) = x (ix hk (t + 5 * k - 5 + (j.val + 1)))
    exact congrArg x (congrArg (ix hk) (by omega))
  · show x (ix hk (t + 1 + 5 * k - 5 + 4)) = x (ix hk t)
    exact congrArg x (sc_ix_of_eq hk _ _ 0 5 (by omega))
  · intro j
    rfl
  · intro i
    show (∑ t' : Fin k, if t'.val < t + 1 then M i t' * x t' else 0) =
      (∑ t' : Fin k, if t'.val < t then M i t' * x t' else 0) + M i (ix hk t) * x (ix hk t)
    exact sc_psum_succ hk (M i) x t ht
  · intro i
    rfl
  · intro h0
    subst h0
    refine ⟨fun j => ?_, fun i => ?_⟩
    · show x (ix hk (0 + 5 * k - 5 + j.val)) = x (ix hk (5 * k - 5 + j.val))
      rw [Nat.zero_add]
    · show (∑ t' : Fin k, if t'.val < 0 then M i t' * x t' else 0) = 0
      exact Finset.sum_eq_zero (fun t' _ => if_neg (Nat.not_lt_zero _))
  · intro hk1
    refine ⟨fun j => ?_, fun i => ?_⟩
    · show x (ix hk (t + 1 + 5 * k - 5 + j.val)) = x (ix hk (5 * k - 5 + j.val))
      exact congrArg x (sc_ix_of_eq hk _ _ 0 1 (by omega))
    · show (∑ t' : Fin k, if t'.val < t + 1 then M i t' * x t' else 0) = 0
      refine Eq.trans ?_ (hM i)
      exact Finset.sum_congr rfl (fun t' _ => if_pos (by have := t'.isLt; omega))
  · intro α hα
    show x (ix hk (t+5*k-5+3)) + x (ix hk (t+5*k-5+4)) + x (ix hk t) = dotProduct α τ
    rw [sc_row_lab]
    exact hlab false _ α hα
  · intro β hβ
    show x (ix hk (t+5*k-5+1)) + x (ix hk (t+5*k-5+3)) + x (ix hk t) = dotProduct β τ
    rw [sc_col_lab]
    exact hlab true _ β hβ
  · intro h1 h2 hm
    show x (ix hk (t+5*k-5+2)) = x (ix hk t)
    rw [sc_row_free]
    have e1 : ix hk ((ix hk (t+2*k-2)).val + 1) = ix hk (t+k-1) := by
      rw [sc_ix_add]
      exact sc_ix_of_eq hk _ _ 0 1 (by omega)
    have e2 : ix hk ((ix hk (t+2*k-2)).val + 2) = ix hk t := by
      rw [sc_ix_add]
      exact sc_ix_of_eq hk _ _ 0 2 (by omega)
    have h := hfree false (ix hk (t+2*k-2)) hm (by rw [e1]; exact h1) (by rw [e2]; exact h2)
    rw [e1, e2] at h
    exact h
  · intro h1 h2 hm
    show x (ix hk (t+5*k-5+0)) + x (ix hk (t+5*k-5+1)) + x (ix hk (t+5*k-5+2)) +
      x (ix hk (t+5*k-5+3)) + x (ix hk (t+5*k-5+4)) = x (ix hk t)
    rw [sc_col_free]
    have e1 : ix hk ((ix hk (t+k-1)).val + 1) = ix hk t := by
      rw [sc_ix_add]
      exact sc_ix_of_eq hk _ _ 0 1 (by omega)
    have e2 : ix hk ((ix hk (t+k-1)).val + 2) = ix hk (t+1) := by
      rw [sc_ix_add]
      exact sc_ix_of_eq hk _ _ 0 1 (by omega)
    have h := hfree true (ix hk (t+k-1)) hm (by rw [e1]; exact h1) (by rw [e2]; exact h2)
    rw [e1, e2] at h
    exact h

-- ---------------------------------------------------------------- target

theorem scan_iff {k : ℕ} (hk : 0 < k) {r s : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2))
    (x : Fin k → ZMod 2) :
    (∃ Y : Fin (k+1) → Idx r s → ZMod 2, ∀ t : Fin k,
      ∀ q ∈ (eqs k t.val (lab false (ix hk (t.val+k-1))) (lab true (ix hk t.val))
          (lab false (ix hk t.val)) (lab true (ix hk (t.val+1))) : List (SEq r s)),
        holds (marked false (ix hk (t.val+2*k-2))) (marked true (ix hk (t.val+k-1)))
          (fun i => M i t) q (Y t.castSucc) (x t) (Y t.succ)) ↔
    LSol hk marked M lab x := by
  constructor
  · rintro ⟨Y, hY⟩
    exact sc_fwd hk marked M lab x Y
      (fun t => (sc_step_iff hk marked M lab x t _ _).1 (hY t))
  · rintro ⟨τ, hM, hlab, hfree⟩
    refine ⟨fun t => sc_Y hk M x τ t.val, fun t => ?_⟩
    exact (sc_step_iff hk marked M lab x t _ _).2
      (sc_bwdN hk marked M lab x τ hM hlab hfree t.val t.isLt)


section PlumbC1

open PEqualNP.CircuitLowerBounds

theorem pl_copyGates_append (l : List ℕ) (u : ℕ) :
    copyGates (l ++ [u]) = copyGates l ++ [⟨GateOp.or, [u, u]⟩] := by
  simp [copyGates]

theorem pl_or_self (b : Bool) : GateOp.or.eval [b, b] = b := by
  cases b <;> rfl

theorem pl_shiftGates_cons (P : ℕ) (g : Gate) (gs : List Gate) :
    shiftGates P (g :: gs) = ⟨g.op, g.inputs.map (fun i => i + P)⟩ :: shiftGates P gs := rfl

theorem pl_shift_fold (pre : List Bool) (gates : List Gate) (acc : List Bool) :
    (shiftGates pre.length gates).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (pre ++ acc) =
      pre ++ gates.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc := by
  induction gates generalizing acc with
  | nil => rfl
  | cons g gates ih =>
    rw [pl_shiftGates_cons, List.foldl_cons, List.foldl_cons]
    have hmap : (g.inputs.map (fun i => i + pre.length)).map (fun i => (pre ++ acc).getD i false)
        = g.inputs.map (fun i => acc.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      show (pre ++ acc).getD (i + pre.length) false = acc.getD i false
      rw [getD_append_ge _ _ (by omega)]
      have e : i + pre.length - pre.length = i := by omega
      rw [e]
    have hstep : (pre ++ acc) ++ [g.op.eval
          ((g.inputs.map (fun i => i + pre.length)).map (fun i => (pre ++ acc).getD i false))] =
        pre ++ (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) := by
      rw [hmap, List.append_assoc]
    show (shiftGates pre.length gates).foldl _ ((pre ++ acc) ++ [g.op.eval
          ((g.inputs.map (fun i => i + pre.length)).map (fun i => (pre ++ acc).getD i false))]) =
        pre ++ gates.foldl _ (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
    rw [hstep]
    exact ih _

theorem pl_good_append {I : ℕ} {gs ext : List Gate} (hG : Good I gs)
    (hE : Good (I + gs.length) ext) : Good I (gs ++ ext) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h1 | h2
    · exact hG.1 g h1
    · exact hE.1 g h2
  · intro j hj i hi
    simp only [List.length_append] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    dsimp only at hi
    by_cases hlt : j < gs.length
    · rw [getD_append_lt _ _ hlt] at hi
      exact hG.2 j hlt i hi
    · rw [getD_append_ge _ _ (by omega)] at hi
      have hj2 : j - gs.length < ext.length := by omega
      have h3 := hE.2 (j - gs.length) hj2 i hi
      omega

theorem pl_shift_getD (P : ℕ) (gates : List Gate) (j : ℕ) :
    (shiftGates P gates).getD j ⟨GateOp.or, []⟩ =
      ⟨(gates.getD j ⟨GateOp.or, []⟩).op,
        (gates.getD j ⟨GateOp.or, []⟩).inputs.map (fun i => i + P)⟩ := by
  induction gates generalizing j with
  | nil => simp [shiftGates]
  | cons g gates ih =>
    cases j with
    | zero => rfl
    | succ j =>
      rw [pl_shiftGates_cons, List.getD_cons_succ, List.getD_cons_succ]
      exact ih j

theorem pl_shift_good {N P M : ℕ} (A : Circuit)
    (hA1 : PEqualNP.MetaComplexity.FanInTwo A)
    (hA2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack N A) (hM : N + P ≤ M) :
    Good M (shiftGates P A.gates) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    have hg2 : g ∈ List.map (fun g : Gate => (⟨g.op, g.inputs.map (fun i => i + P)⟩ : Gate))
        A.gates := hg
    rcases List.mem_map.mp hg2 with ⟨g0, hg0, rfl⟩
    refine ⟨(hA1 g0 hg0).1, ?_⟩
    have h2 := (hA1 g0 hg0).2
    simpa using h2
  · intro j hj i hi
    have hj1 : j < (shiftGates P A.gates).length := hj
    have hj2 : j < A.gates.length := by
      simpa [shiftGates] using hj1
    have hi2 : i ∈ ((shiftGates P A.gates).getD j ⟨GateOp.or, []⟩).inputs := hi
    rw [pl_shift_getD] at hi2
    dsimp only at hi2
    rcases List.mem_map.mp hi2 with ⟨i0, hi0, rfl⟩
    have h3 := hA2 j hj2 i0 hi0
    omega

theorem copy_spec {I : ℕ} (gs : List Gate) (hG : Good I gs) (srcs : List ℕ)
    (hs : ∀ u ∈ srcs, u < I + gs.length) :
    Good I (gs ++ copyGates srcs) ∧ ∀ x : List Bool, x.length = I →
      evalWires (gs ++ copyGates srcs) x = evalWires gs x ++ srcs.map (wireAt gs x) := by
  induction srcs using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_⟩
    · simpa [copyGates] using hG
    · intro x _
      simp [copyGates]
  | append_singleton l u ih =>
    have ih2 := ih (fun v hv => hs v (List.mem_append_left _ hv))
    have hu : u < I + gs.length :=
      hs u (List.mem_append_right _ (List.mem_singleton_self u))
    rw [pl_copyGates_append, ← List.append_assoc]
    refine ⟨?_, ?_⟩
    · refine good_append_one ih2.1 _ (by simp) (by simp) ?_
      intro i hi
      simp at hi
      subst hi
      rw [List.length_append]
      omega
    · intro x hx
      rw [evalWires_append_one, ih2.2 x hx]
      have hw : wireAt (gs ++ copyGates l) x u = wireAt gs x u :=
        wireAt_extends ⟨copyGates l, rfl⟩ x (by omega)
      simp only [List.map_cons, List.map_nil, hw, pl_or_self, List.map_append,
        List.append_assoc]

theorem shift_spec {I N : ℕ} (gs : List Gate) (hG : Good I gs) (A : Circuit)
    (hA1 : PEqualNP.MetaComplexity.FanInTwo A)
    (hA2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack N A) (hN : N ≤ I + gs.length) :
    Good I (gs ++ shiftGates (I + gs.length - N) A.gates) ∧
    ∀ (x : List Bool), x.length = I → ∀ (pre blk : List Bool), evalWires gs x = pre ++ blk →
      blk.length = N →
      evalWires (gs ++ shiftGates (I + gs.length - N) A.gates) x = pre ++ A.wires blk := by
  refine ⟨pl_good_append hG (pl_shift_good A hA1 hA2 (by omega)), ?_⟩
  intro x hx pre blk h hblk
  have hlen := evalWires_length gs x
  rw [h, List.length_append, hx, hblk] at hlen
  have hP : I + gs.length - N = pre.length := by omega
  rw [evalWires_append, h, hP]
  exact pl_shift_fold pre A.gates blk

theorem shift_wire {I N : ℕ} (gs : List Gate) (A : Circuit) (x pre blk : List Bool)
    (h : evalWires (gs ++ shiftGates (I + gs.length - N) A.gates) x = pre ++ A.wires blk)
    (hpre : pre.length = I + gs.length - N) (i : ℕ) :
    wireAt (gs ++ shiftGates (I + gs.length - N) A.gates) x (I + gs.length - N + i) =
      (A.wires blk).getD i false := by
  unfold wireAt
  rw [h, getD_append_ge _ _ (by omega)]
  have e : I + gs.length - N + i - pre.length = i := by omega
  rw [e]

theorem wire_ext {I : ℕ} {gs1 gs2 : List Gate} (he : Extends gs1 gs2) (x : List Bool) (hx : x.length = I)
    {w : ℕ} (hw : w < I + gs1.length) : wireAt gs2 x w = wireAt gs1 x w :=
  wireAt_extends he x (by omega)

end PlumbC1


section ElimCkt

open PEqualNP.CircuitLowerBounds

-- input shape helpers
theorem ec_inp_eq {m k : ℕ} (Q : Fin m → Fin k → ZMod 2) :
    (List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten =
      (List.finRange m).flatMap (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0))) := by
  rw [List.ofFn_eq_map, List.flatMap_def]

theorem ec_idx_lt {m k i t : ℕ} (hi : i < m) (ht : t < k) : i * k + t < m * k := by
  have h := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at h
  omega

theorem ec_inp_len {m k : ℕ} (Q : Fin m → Fin k → ZMod 2) (rest : List Bool)
    (hr : rest.length = 2 * k) :
    ((List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten ++ rest).length =
      (m + 2) * k := by
  rw [ec_inp_eq, List.length_append, b_flat_len m k _ (fun i => List.length_ofFn), hr]
  ring

theorem ec_inp_bit {m k : ℕ} (Q : Fin m → Fin k → ZMod 2) (rest : List Bool) (i : Fin m)
    (t : Fin k) :
    ((List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten ++ rest).getD
      (i.val * k + t.val) false = decide (Q i t ≠ 0) := by
  have h : t.val < (List.ofFn (fun c : Fin k => decide (Q i c ≠ 0))).length := by
    rw [List.length_ofFn]
    exact t.isLt
  rw [ec_inp_eq, getD_append_lt _ _ (by
      rw [b_flat_len m k _ (fun i => List.length_ofFn)]
      exact ec_idx_lt i.isLt t.isLt),
    b_flat_getD m k _ (fun i => List.length_ofFn) i t.val t.isLt,
    List.getD_eq_getElem _ _ h, List.getElem_ofFn]

-- pure lemmas
theorem ec_mem_iff {k r : ℕ} (S : Fin (r + 1) → Fin k → ZMod 2) (q : Fin k → ZMod 2) :
    q ∈ Submodule.span (ZMod 2) (Set.range S) ↔
      ∃ c : Fin (r + 1) → Bool, ∀ t, q t = ∑ j, S j t * d0_bz (c j) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => decide (c j ≠ 0), fun t => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, d0_bz_decide]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · rintro ⟨c, hc⟩
    refine ⟨fun j => d0_bz (c j), ?_⟩
    funext t
    rw [hc t]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem ec_comb {k r : ℕ} (V : ℕ → Bool) (S : Fin (r + 1) → Fin k → ZMod 2)
    (sw : Fin (r + 1) → Fin k → ℕ) (h : ∀ j t, V (sw j t) = decide (S j t ≠ 0))
    (c : Fin (r + 1) → Bool) (t : Fin k) :
    d0_bz (xorVal V (((List.finRange (r + 1)).filter (fun j => c j)).map (fun j => sw j t))) =
      ∑ j, S j t * d0_bz (c j) := by
  rw [Fin.sum_univ_def]
  exact d0_xor_filter V (fun j => S j t) (fun j => d0_bz (c j)) (fun j => sw j t) (fun j => c j)
    (fun j => by
      show c j = true ↔ d0_bz (c j) ≠ 0
      cases c j <;> decide)
    (fun j => h j t) (List.finRange (r + 1))

theorem ec_xor2 (V : ℕ → Bool) (a b : ℕ) :
    d0_bz (xorVal V [a, b]) = d0_bz (V a) + d0_bz (V b) := by
  show d0_bz (xor (V a) (xor (V b) false)) = _
  rw [Bool.xor_false, d0_bz_xor]

theorem ec_bz_false (b : Bool) : b = false ↔ d0_bz b = 0 := by
  cases b <;> decide

theorem ec_z2_add : ∀ a q : ZMod 2, a + q = 0 ↔ q = a := by decide

theorem ec_allfalse {k : ℕ} (V : ℕ → Bool) (f : Fin k → ℕ) :
    dnfVal V [(List.finRange k).map (fun t => (f t, false))] = true ↔ ∀ t, V (f t) = false := by
  simp [dnfVal, litVal]

theorem ec_anytrue {ι : Type} [Finite ι] (V : ℕ → Bool) (f : ι → ℕ) :
    dnfVal V ((enumF ι).map (fun c => [(f c, true)])) = true ↔ ∃ c, V (f c) = true := by
  simp [dnfVal, litVal, mem_enumF]

theorem ec_mux (V : ℕ → Bool) (a b c : ℕ) :
    dnfVal V [[(a, true), (b, true)], [(a, false), (c, true)]] =
      (if V a = true then V b else V c) := by
  simp only [dnfVal, litVal, List.any_cons, List.all_cons, List.any_nil, List.all_nil]
  cases V a <;> cases V b <;> cases V c <;> decide

theorem ec_ins_bit {k r : ℕ} (S : Fin (r + 1) → Fin k → ZMod 2) (q : Fin k → ZMod 2)
    (V : ℕ → Bool) (sw : Fin (r + 1) → Fin k → ℕ) (qw : Fin k → ℕ) (mw : ℕ)
    (hS : ∀ j t, V (sw j t) = decide (S j t ≠ 0)) (hq : ∀ t, V (qw t) = decide (q t ≠ 0))
    (hm : V mw = true ↔ q ∈ Submodule.span (ZMod 2) (Set.range S))
    (j : Fin (r + 1)) (t : Fin k) :
    (if V mw = true then V (sw j t)
      else V (Fin.cons (α := fun _ => ℕ) (qw t) (fun j' : Fin r => sw j'.castSucc t) j)) =
      decide (ins S q j t ≠ 0) := by
  unfold ins
  by_cases h : q ∈ Submodule.span (ZMod 2) (Set.range S)
  · rw [ite_eq_left (hm.mpr h), ite_eq_left h, hS]
  · rw [ite_eq_right (fun h' => h (hm.mp h')), ite_eq_right h]
    refine Fin.cases ?_ (fun j' => ?_) j
    · rw [Fin.cons_zero, Fin.cons_zero, hq]
    · rw [Fin.cons_succ, Fin.cons_succ, hS]

theorem ec_card1 (k r : ℕ) : Nat.card ((Fin (r + 1) → Bool) × Fin k) = 2 ^ (r + 1) * k := by
  simp [Nat.card_eq_fintype_card]

theorem ec_card2 (r : ℕ) : Nat.card (Fin (r + 1) → Bool) = 2 ^ (r + 1) := by
  simp [Nat.card_eq_fintype_card]

theorem ec_card3 (k r : ℕ) : Nat.card (Fin (r + 1) × Fin k) = (r + 1) * k := by
  simp [Nat.card_eq_fintype_card]

theorem ec_arith (k m r P : ℕ) (hP : 1 ≤ P) :
    1 + m * (P * k * (4 * (r + 1) + 1) + P * k * 9 + P * (2 * k + 3) + (1 + P * 4) +
      (r + 1) * k * 13) ≤ 40 * (m + 1) * (k + 1) * (r + 2) * P := by
  have h1 : r * k ≤ P * (r * k) := Nat.le_mul_of_pos_left _ hP
  have h2 : k ≤ P * k := Nat.le_mul_of_pos_left _ hP
  have hc : P * k * (4 * (r + 1) + 1) + P * k * 9 + P * (2 * k + 3) + (1 + P * 4) +
      (r + 1) * k * 13 ≤ 40 * (k + 1) * (r + 2) * P := by
    nlinarith [h1, h2, hP, Nat.zero_le (P * k * r), Nat.zero_le (P * k), Nat.zero_le (P * r)]
  have h3 : 1 ≤ 40 * (k + 1) * (r + 2) * P := by
    nlinarith [hP, Nat.zero_le (P * k * r), Nat.zero_le (P * k), Nat.zero_le (P * r)]
  calc 1 + m * (P * k * (4 * (r + 1) + 1) + P * k * 9 + P * (2 * k + 3) + (1 + P * 4) +
        (r + 1) * k * 13)
      ≤ 40 * (k + 1) * (r + 2) * P + m * (40 * (k + 1) * (r + 2) * P) :=
        Nat.add_le_add h3 (Nat.mul_le_mul_left m hc)
    _ = 40 * (m + 1) * (k + 1) * (r + 2) * P := by ring

-- the five tables of one insertion step
noncomputable def ec_s1 (I : ℕ) {k r : ℕ} (sw : Fin (r + 1) → Fin k → ℕ) (gs : List Gate) :
    List Gate × ((Fin (r + 1) → Bool) × Fin k → ℕ) :=
  mkXorTab I ((Fin (r + 1) → Bool) × Fin k)
    (fun ct => ((List.finRange (r + 1)).filter (fun j => ct.1 j)).map (fun j => sw j ct.2)) gs

noncomputable def ec_s2 (I : ℕ) {k r : ℕ} (qw : Fin k → ℕ) (sw : Fin (r + 1) → Fin k → ℕ)
    (gs : List Gate) : List Gate × ((Fin (r + 1) → Bool) × Fin k → ℕ) :=
  mkXorTab I ((Fin (r + 1) → Bool) × Fin k)
    (fun ct => [(ec_s1 I sw gs).2 ct, qw ct.2]) (ec_s1 I sw gs).1

noncomputable def ec_s3 (I : ℕ) {k r : ℕ} (qw : Fin k → ℕ) (sw : Fin (r + 1) → Fin k → ℕ)
    (gs : List Gate) : List Gate × ((Fin (r + 1) → Bool) → ℕ) :=
  mkDnfTab I (Fin (r + 1) → Bool)
    (fun c => [(List.finRange k).map (fun t => ((ec_s2 I qw sw gs).2 (c, t), false))])
    (ec_s2 I qw sw gs).1

noncomputable def ec_s4 (I : ℕ) {k r : ℕ} (qw : Fin k → ℕ) (sw : Fin (r + 1) → Fin k → ℕ)
    (gs : List Gate) : List Gate × (Unit → ℕ) :=
  mkDnfTab I Unit
    (fun _ => (enumF (Fin (r + 1) → Bool)).map (fun c => [((ec_s3 I qw sw gs).2 c, true)]))
    (ec_s3 I qw sw gs).1

noncomputable def ec_s5 (I : ℕ) {k r : ℕ} (qw : Fin k → ℕ) (sw : Fin (r + 1) → Fin k → ℕ)
    (gs : List Gate) : List Gate × (Fin (r + 1) × Fin k → ℕ) :=
  mkDnfTab I (Fin (r + 1) × Fin k)
    (fun jt => [[((ec_s4 I qw sw gs).2 (), true), (sw jt.1 jt.2, true)],
      [((ec_s4 I qw sw gs).2 (), false),
        (Fin.cons (α := fun _ => ℕ) (qw jt.2) (fun j' : Fin r => sw j'.castSucc jt.2) jt.1,
          true)]])
    (ec_s4 I qw sw gs).1

theorem ec_s1_spec (I : ℕ) {k r : ℕ} (sw : Fin (r + 1) → Fin k → ℕ) (gs : List Gate)
    (hG : Good I gs) (hsw : ∀ j t, sw j t < I + gs.length) :
    Extends gs (ec_s1 I sw gs).1 ∧
    (ec_s1 I sw gs).1.length ≤ gs.length + 2 ^ (r + 1) * k * (4 * (r + 1) + 1) ∧
    Good I (ec_s1 I sw gs).1 ∧
    (∀ i, (ec_s1 I sw gs).2 i < I + (ec_s1 I sw gs).1.length) ∧
    ∀ gs', Extends (ec_s1 I sw gs).1 gs' → ∀ x : List Bool, x.length = I → ∀ c t,
      wireAt gs' x ((ec_s1 I sw gs).2 (c, t)) = xorVal (wireAt gs' x)
        (((List.finRange (r + 1)).filter (fun j => c j)).map (fun j => sw j t)) := by
  have h := mkXorTab_spec (I := I) (4 * (r + 1) + 1) ((Fin (r + 1) → Bool) × Fin k)
    (fun ct => ((List.finRange (r + 1)).filter (fun j => ct.1 j)).map (fun j => sw j ct.2)) gs hG
    (fun i u hu => by
      rcases List.mem_map.mp hu with ⟨j, _, rfl⟩
      exact hsw _ _)
    (fun i => by
      have h1 : (((List.finRange (r + 1)).filter (fun j => i.1 j)).map
          (fun j => sw j i.2)).length ≤ r + 1 := by
        rw [List.length_map]
        exact (List.length_filter_le _ _).trans (by simp)
      omega)
  rw [ec_card1] at h
  obtain ⟨e, l, g, v, q⟩ := h
  exact ⟨e, l, g, v, fun gs' he x hx c t => q gs' he x hx (c, t)⟩

theorem ec_s2_spec (I : ℕ) {k r : ℕ} (qw : Fin k → ℕ) (sw : Fin (r + 1) → Fin k → ℕ)
    (gs : List Gate) (hG : Good I gs) (hsw : ∀ j t, sw j t < I + gs.length)
    (hqw : ∀ t, qw t < I + gs.length) :
    Extends (ec_s1 I sw gs).1 (ec_s2 I qw sw gs).1 ∧
    (ec_s2 I qw sw gs).1.length ≤ (ec_s1 I sw gs).1.length + 2 ^ (r + 1) * k * 9 ∧
    Good I (ec_s2 I qw sw gs).1 ∧
    (∀ i, (ec_s2 I qw sw gs).2 i < I + (ec_s2 I qw sw gs).1.length) ∧
    ∀ gs', Extends (ec_s2 I qw sw gs).1 gs' → ∀ x : List Bool, x.length = I → ∀ c t,
      wireAt gs' x ((ec_s2 I qw sw gs).2 (c, t)) = xorVal (wireAt gs' x)
        [(ec_s1 I sw gs).2 (c, t), qw t] := by
  obtain ⟨e1, _, g1, v1, _⟩ := ec_s1_spec I sw gs hG hsw
  have hl1 := extends_length_le e1
  have h := mkXorTab_spec (I := I) 9 ((Fin (r + 1) → Bool) × Fin k)
    (fun ct => [(ec_s1 I sw gs).2 ct, qw ct.2]) (ec_s1 I sw gs).1 g1
    (fun i u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact v1 _
      · have := hqw i.2
        omega)
    (fun i => by simp)
  rw [ec_card1] at h
  obtain ⟨e, l, g, v, q⟩ := h
  exact ⟨e, l, g, v, fun gs' he x hx c t => q gs' he x hx (c, t)⟩

theorem ec_s3_spec (I : ℕ) {k r : ℕ} (qw : Fin k → ℕ) (sw : Fin (r + 1) → Fin k → ℕ)
    (gs : List Gate) (hG : Good I gs) (hsw : ∀ j t, sw j t < I + gs.length)
    (hqw : ∀ t, qw t < I + gs.length) :
    Extends (ec_s2 I qw sw gs).1 (ec_s3 I qw sw gs).1 ∧
    (ec_s3 I qw sw gs).1.length ≤ (ec_s2 I qw sw gs).1.length + 2 ^ (r + 1) * (2 * k + 3) ∧
    Good I (ec_s3 I qw sw gs).1 ∧
    (∀ i, (ec_s3 I qw sw gs).2 i < I + (ec_s3 I qw sw gs).1.length) ∧
    ∀ gs', Extends (ec_s3 I qw sw gs).1 gs' → ∀ x : List Bool, x.length = I → ∀ c,
      wireAt gs' x ((ec_s3 I qw sw gs).2 c) = dnfVal (wireAt gs' x)
        [(List.finRange k).map (fun t => ((ec_s2 I qw sw gs).2 (c, t), false))] := by
  obtain ⟨_, _, g2, v2, _⟩ := ec_s2_spec I qw sw gs hG hsw hqw
  have h := mkDnfTab_spec (I := I) (2 * k + 3) (Fin (r + 1) → Bool)
    (fun c => [(List.finRange k).map (fun t => ((ec_s2 I qw sw gs).2 (c, t), false))])
    (ec_s2 I qw sw gs).1 g2
    (fun i t ht l hl => by
      simp only [List.mem_singleton] at ht
      subst ht
      rcases List.mem_map.mp hl with ⟨e, _, rfl⟩
      exact v2 _)
    (fun i => by
      simp only [dnfCost, List.length_map, List.length_finRange]
      omega)
  rw [ec_card2] at h
  exact h

theorem ec_s4_spec (I : ℕ) {k r : ℕ} (qw : Fin k → ℕ) (sw : Fin (r + 1) → Fin k → ℕ)
    (gs : List Gate) (hG : Good I gs) (hsw : ∀ j t, sw j t < I + gs.length)
    (hqw : ∀ t, qw t < I + gs.length) :
    Extends (ec_s3 I qw sw gs).1 (ec_s4 I qw sw gs).1 ∧
    (ec_s4 I qw sw gs).1.length ≤ (ec_s3 I qw sw gs).1.length + (1 + 2 ^ (r + 1) * 4) ∧
    Good I (ec_s4 I qw sw gs).1 ∧
    (ec_s4 I qw sw gs).2 () < I + (ec_s4 I qw sw gs).1.length ∧
    ∀ gs', Extends (ec_s4 I qw sw gs).1 gs' → ∀ x : List Bool, x.length = I →
      wireAt gs' x ((ec_s4 I qw sw gs).2 ()) = dnfVal (wireAt gs' x)
        ((enumF (Fin (r + 1) → Bool)).map (fun c => [((ec_s3 I qw sw gs).2 c, true)])) := by
  obtain ⟨_, _, g3, v3, _⟩ := ec_s3_spec I qw sw gs hG hsw hqw
  have h := mkDnfTab_spec (I := I) (1 + 2 ^ (r + 1) * 4) Unit
    (fun _ => (enumF (Fin (r + 1) → Bool)).map (fun c => [((ec_s3 I qw sw gs).2 c, true)]))
    (ec_s3 I qw sw gs).1 g3
    (fun i t ht l hl => by
      rcases List.mem_map.mp ht with ⟨c, _, rfl⟩
      simp only [List.mem_singleton] at hl
      subst hl
      exact v3 _)
    (fun i => by
      have := bs_m_cost (ι := Fin (r + 1) → Bool) (fun c => [((ec_s3 I qw sw gs).2 c, true)]) 1 4
        (fun a => by simp) (by norm_num)
      rw [ec_card2] at this
      exact this)
  have hc : Nat.card Unit = 1 := by simp
  rw [hc, Nat.one_mul] at h
  obtain ⟨e, l, g, v, q⟩ := h
  exact ⟨e, l, g, v (), fun gs' he x hx => q gs' he x hx ()⟩

theorem ec_s5_spec (I : ℕ) {k r : ℕ} (qw : Fin k → ℕ) (sw : Fin (r + 1) → Fin k → ℕ)
    (gs : List Gate) (hG : Good I gs) (hsw : ∀ j t, sw j t < I + gs.length)
    (hqw : ∀ t, qw t < I + gs.length) :
    Extends (ec_s4 I qw sw gs).1 (ec_s5 I qw sw gs).1 ∧
    (ec_s5 I qw sw gs).1.length ≤ (ec_s4 I qw sw gs).1.length + (r + 1) * k * 13 ∧
    Good I (ec_s5 I qw sw gs).1 ∧
    (∀ i, (ec_s5 I qw sw gs).2 i < I + (ec_s5 I qw sw gs).1.length) ∧
    ∀ gs', Extends (ec_s5 I qw sw gs).1 gs' → ∀ x : List Bool, x.length = I → ∀ j t,
      wireAt gs' x ((ec_s5 I qw sw gs).2 (j, t)) = dnfVal (wireAt gs' x)
        [[((ec_s4 I qw sw gs).2 (), true), (sw j t, true)],
          [((ec_s4 I qw sw gs).2 (), false),
            (Fin.cons (α := fun _ => ℕ) (qw t) (fun j' : Fin r => sw j'.castSucc t) j,
              true)]] := by
  obtain ⟨e1, _, _, _, _⟩ := ec_s1_spec I sw gs hG hsw
  obtain ⟨e2, _, _, _, _⟩ := ec_s2_spec I qw sw gs hG hsw hqw
  obtain ⟨e3, _, _, _, _⟩ := ec_s3_spec I qw sw gs hG hsw hqw
  obtain ⟨e4, _, g4, v4, _⟩ := ec_s4_spec I qw sw gs hG hsw hqw
  have hl := extends_length_le (extends_trans e1 (extends_trans e2 (extends_trans e3 e4)))
  have h := mkDnfTab_spec (I := I) 13 (Fin (r + 1) × Fin k)
    (fun jt => [[((ec_s4 I qw sw gs).2 (), true), (sw jt.1 jt.2, true)],
      [((ec_s4 I qw sw gs).2 (), false),
        (Fin.cons (α := fun _ => ℕ) (qw jt.2) (fun j' : Fin r => sw j'.castSucc jt.2) jt.1,
          true)]])
    (ec_s4 I qw sw gs).1 g4
    (fun i t ht l hl' => by
      have hc : Fin.cons (α := fun _ => ℕ) (qw i.2) (fun j' : Fin r => sw j'.castSucc i.2) i.1 <
          I + gs.length := by
        refine Fin.cases ?_ (fun j' => ?_) i.1
        · rw [Fin.cons_zero]
          exact hqw _
        · rw [Fin.cons_succ]
          exact hsw _ _
      have hs := hsw i.1 i.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
        rcases hl' with rfl | rfl
        · exact v4
        · show sw i.1 i.2 < _
          omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
        rcases hl' with rfl | rfl
        · exact v4
        · show Fin.cons (α := fun _ => ℕ) (qw i.2) (fun j' : Fin r => sw j'.castSucc i.2) i.1 < _
          omega)
    (fun i => by simp [dnfCost])
  rw [ec_card3] at h
  obtain ⟨e, l, g, v, q⟩ := h
  exact ⟨e, l, g, v, fun gs' he x hx j t => q gs' he x hx (j, t)⟩


noncomputable def ec_step (I : ℕ) {k r : ℕ} (qw : Fin k → ℕ) (sw : Fin (r + 1) → Fin k → ℕ) :
    CG (Fin (r + 1) → Fin k → ℕ) :=
  fun gs => ((ec_s5 I qw sw gs).1, fun j t => (ec_s5 I qw sw gs).2 (j, t))

def ec_cost (k r : ℕ) : ℕ :=
  2 ^ (r + 1) * k * (4 * (r + 1) + 1) + 2 ^ (r + 1) * k * 9 + 2 ^ (r + 1) * (2 * k + 3) +
    (1 + 2 ^ (r + 1) * 4) + (r + 1) * k * 13

theorem ec_step_spec (I : ℕ) {k r : ℕ} (qw : Fin k → ℕ) (sw : Fin (r + 1) → Fin k → ℕ)
    (gs : List Gate) (hG : Good I gs) (hsw : ∀ j t, sw j t < I + gs.length)
    (hqw : ∀ t, qw t < I + gs.length) :
    Extends gs (ec_step I qw sw gs).1 ∧
    (ec_step I qw sw gs).1.length ≤ gs.length + ec_cost k r ∧
    Good I (ec_step I qw sw gs).1 ∧
    (∀ j t, (ec_step I qw sw gs).2 j t < I + (ec_step I qw sw gs).1.length) ∧
    ∀ gs', Extends (ec_step I qw sw gs).1 gs' → ∀ x : List Bool, x.length = I →
      ∀ (S : Fin (r + 1) → Fin k → ZMod 2) (q : Fin k → ZMod 2),
      (∀ j t, wireAt gs' x (sw j t) = decide (S j t ≠ 0)) →
      (∀ t, wireAt gs' x (qw t) = decide (q t ≠ 0)) →
      ∀ j t, wireAt gs' x ((ec_step I qw sw gs).2 j t) = decide (ins S q j t ≠ 0) := by
  obtain ⟨e1, l1, _, _, q1⟩ := ec_s1_spec I sw gs hG hsw
  obtain ⟨e2, l2, _, _, q2⟩ := ec_s2_spec I qw sw gs hG hsw hqw
  obtain ⟨e3, l3, _, _, q3⟩ := ec_s3_spec I qw sw gs hG hsw hqw
  obtain ⟨e4, l4, _, _, q4⟩ := ec_s4_spec I qw sw gs hG hsw hqw
  obtain ⟨e5, l5, g5, v5, q5⟩ := ec_s5_spec I qw sw gs hG hsw hqw
  refine ⟨extends_trans e1 (extends_trans e2 (extends_trans e3 (extends_trans e4 e5))), ?_, g5,
    fun j t => v5 (j, t), fun gs' he x hx S q hS hq j t => ?_⟩
  · show (ec_s5 I qw sw gs).1.length ≤ gs.length + ec_cost k r
    unfold ec_cost
    omega
  · have he5 : Extends (ec_s5 I qw sw gs).1 gs' := he
    have he4 := extends_trans e5 he5
    have he3 := extends_trans e4 he4
    have he2 := extends_trans e3 he3
    have he1 := extends_trans e2 he2
    have c1 : ∀ c t, d0_bz (wireAt gs' x ((ec_s1 I sw gs).2 (c, t))) =
        ∑ j, S j t * d0_bz (c j) := by
      intro c t
      rw [q1 gs' he1 x hx c t]
      exact ec_comb (wireAt gs' x) S sw hS c t
    have c2 : ∀ c t, d0_bz (wireAt gs' x ((ec_s2 I qw sw gs).2 (c, t))) =
        (∑ j, S j t * d0_bz (c j)) + q t := by
      intro c t
      rw [q2 gs' he2 x hx c t, ec_xor2, c1, hq, d0_bz_decide]
    have c3 : ∀ c, wireAt gs' x ((ec_s3 I qw sw gs).2 c) = true ↔
        ∀ t, q t = ∑ j, S j t * d0_bz (c j) := by
      intro c
      rw [q3 gs' he3 x hx c, ec_allfalse]
      refine forall_congr' (fun t => ?_)
      rw [ec_bz_false, c2, ec_z2_add]
    have c4 : wireAt gs' x ((ec_s4 I qw sw gs).2 ()) = true ↔
        q ∈ Submodule.span (ZMod 2) (Set.range S) := by
      rw [q4 gs' he4 x hx, ec_anytrue, ec_mem_iff]
      exact exists_congr c3
    show wireAt gs' x ((ec_s5 I qw sw gs).2 (j, t)) = _
    rw [q5 gs' he5 x hx j t, ec_mux]
    exact ec_ins_bit S q (wireAt gs' x) sw qw _ hS hq c4 j t

def ec_Inv (k m r : ℕ) (n : ℕ) (gs : List Gate) (sw : Fin (r + 1) → Fin k → ℕ) : Prop :=
  (∀ j t, sw j t < (m + 2) * k + gs.length) ∧
  ∀ gs', Extends gs gs' → ∀ (Q : Fin m → Fin k → ZMod 2) (rest : List Bool),
    rest.length = 2 * k → ∀ j t,
    wireAt gs'
      ((List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten ++ rest)
      (sw j t) =
      decide ((((List.ofFn Q).take n).foldl ins 0 : Fin (r + 1) → Fin k → ZMod 2) j t ≠ 0)

theorem ec_iter_step (k m r : ℕ) (n : ℕ) (sw : Fin (r + 1) → Fin k → ℕ) (gs : List Gate)
    (hn : n < m) (hG : Good ((m + 2) * k) gs) (hI : ec_Inv k m r n gs sw) :
    Extends gs (ec_step ((m + 2) * k) (fun t : Fin k => n * k + t.val) sw gs).1 ∧
    (ec_step ((m + 2) * k) (fun t : Fin k => n * k + t.val) sw gs).1.length ≤
      gs.length + ec_cost k r ∧
    Good ((m + 2) * k) (ec_step ((m + 2) * k) (fun t : Fin k => n * k + t.val) sw gs).1 ∧
    ec_Inv k m r (n + 1) (ec_step ((m + 2) * k) (fun t : Fin k => n * k + t.val) sw gs).1
      (ec_step ((m + 2) * k) (fun t : Fin k => n * k + t.val) sw gs).2 := by
  unfold ec_Inv at hI
  obtain ⟨hsw, hval⟩ := hI
  have h2 : (m + 2) * k = m * k + 2 * k := by ring
  have hqw : ∀ t : Fin k, n * k + t.val < (m + 2) * k + gs.length := by
    intro t
    have h1 := ec_idx_lt hn t.isLt
    omega
  obtain ⟨e, l, g, v, q⟩ :=
    ec_step_spec ((m + 2) * k) (fun t : Fin k => n * k + t.val) sw gs hG hsw hqw
  refine ⟨e, l, g, ?_⟩
  unfold ec_Inv
  refine ⟨v, fun gs' he Q rest hr j t => ?_⟩
  have hx := ec_inp_len Q rest hr
  have hgs := extends_trans e he
  have hq : ∀ t : Fin k, wireAt gs'
      ((List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten ++ rest)
      (n * k + t.val) = decide (Q ⟨n, hn⟩ t ≠ 0) := by
    intro t
    rw [wireAt_input gs' _ (by
      rw [hx]
      have h1 := ec_idx_lt hn t.isLt
      omega)]
    exact ec_inp_bit Q rest ⟨n, hn⟩ t
  have h := q gs' he _ hx (((List.ofFn Q).take n).foldl ins 0) (Q ⟨n, hn⟩)
    (fun j t => hval gs' hgs Q rest hr j t) hq j t
  have hlen : n < (List.ofFn Q).length := by
    rw [List.length_ofFn]
    exact hn
  rw [List.take_succ_eq_append_getElem hlen, List.foldl_append, List.getElem_ofFn,
    List.foldl_cons, List.foldl_nil]
  exact h

theorem elim_circuit (k m r : ℕ) :
    ∃ (gs : List Gate) (sw : Fin (r+1) → Fin k → ℕ),
      Good ((m+2)*k) gs ∧ gs.length ≤ 40 * (m+1) * (k+1) * (r+2) * 2^(r+1) ∧
      (∀ j t, sw j t < (m+2)*k + gs.length) ∧
      ∀ gs', Extends gs gs' → ∀ (Q : Fin m → Fin k → ZMod 2) (rest : List Bool),
        rest.length = 2*k → ∀ j t,
        wireAt gs' ((List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten ++ rest)
          (sw j t) = decide ((elim Q : Fin (r+1) → Fin k → ZMod 2) j t ≠ 0) := by
  obtain ⟨e0, l0, g0, v0, q0⟩ :=
    mkConst_spec (inputs := (m + 2) * k) false (good_nil ((m + 2) * k))
  have h0 : ec_Inv k m r 0 (mkConst ((m + 2) * k) false []).1
      (fun _ _ => (mkConst ((m + 2) * k) false []).2) := by
    unfold ec_Inv
    refine ⟨fun _ _ => v0, fun gs' he Q rest hr j t => ?_⟩
    have hx := ec_inp_len Q rest hr
    rw [wireAt_extends he _ (by rw [hx]; exact v0), q0 _ hx]
    simp
  have h := iterCG_spec (I := (m + 2) * k)
    (fun n sw => ec_step ((m + 2) * k) (fun t : Fin k => n * k + t.val) sw)
    (ec_Inv k m r) (ec_cost k r) m
    (fun n sw gs hn hG hI => ec_iter_step k m r n sw gs hn hG hI)
    (fun _ _ => (mkConst ((m + 2) * k) false []).2) (mkConst ((m + 2) * k) false []).1 g0 h0
    m le_rfl
  obtain ⟨_, l, g, hI⟩ := h
  unfold ec_Inv at hI
  obtain ⟨hsw, hval⟩ := hI
  refine ⟨_, _, g, ?_, hsw, fun gs' he Q rest hr j t => ?_⟩
  · have ha := ec_arith k m r (2 ^ (r + 1)) Nat.one_le_two_pow
    unfold ec_cost at l
    simp only [List.length_nil] at l0
    omega
  · have h := hval gs' he Q rest hr j t
    rw [List.take_of_length_le (by rw [List.length_ofFn])] at h
    exact h

end ElimCkt


section CtCount

open PEqualNP.CircuitLowerBounds

-- number of indices i below t whose wire is true under the valuation v
def ct_N {k : ℕ} (v : ℕ → Bool) (nzw : Fin k → ℕ) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => i.val < t ∧ v (nzw i) = true)).card

lemma ct_N_zero {k : ℕ} (v : ℕ → Bool) (nzw : Fin k → ℕ) : ct_N v nzw 0 = 0 := by
  simp [ct_N]

lemma ct_N_succ {k : ℕ} (v : ℕ → Bool) (nzw : Fin k → ℕ) (t : ℕ) (h : t < k) :
    ct_N v nzw (t+1) = ct_N v nzw t + (if v (nzw ⟨t, h⟩) = true then 1 else 0) := by
  unfold ct_N
  by_cases hb : v (nzw ⟨t, h⟩) = true
  · have hset : (Finset.univ.filter (fun i : Fin k => i.val < t + 1 ∧ v (nzw i) = true)) =
        insert ⟨t, h⟩ (Finset.univ.filter (fun i : Fin k => i.val < t ∧ v (nzw i) = true)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hi : i.val = t
        · left
          exact Fin.ext hi
        · right
          exact ⟨by omega, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Nat.lt_succ_self t, hb⟩
        · exact ⟨by omega, h2⟩
    rw [hset, Finset.card_insert_of_notMem (by simp), ite_eq_left hb]
  · have hset : (Finset.univ.filter (fun i : Fin k => i.val < t + 1 ∧ v (nzw i) = true)) =
        (Finset.univ.filter (fun i : Fin k => i.val < t ∧ v (nzw i) = true)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_contra hlt
        have hi : i = ⟨t, h⟩ := Fin.ext (by simp only; omega)
        subst hi
        exact hb h2
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    rw [hset, ite_eq_right hb, Nat.add_zero]

lemma ct_N_le {k : ℕ} (v : ℕ → Bool) (nzw : Fin k → ℕ) (t : ℕ) : ct_N v nzw t ≤ k := by
  unfold ct_N
  have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin k))
    (fun i : Fin k => i.val < t ∧ v (nzw i) = true)
  have h2 : (Finset.univ : Finset (Fin k)).card = k := by simp
  omega

lemma ct_N_full {k : ℕ} (v : ℕ → Bool) (nzw : Fin k → ℕ) :
    ct_N v nzw k = (Finset.univ.filter (fun i : Fin k => v (nzw i) = true)).card := by
  unfold ct_N
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨i.isLt, h⟩⟩

-- terms of a single counter step
def ct_terms {k : ℕ} (nzw : Fin k → ℕ) (t : ℕ) (h : t < k) (cnt : Fin (k+1) → ℕ)
    (c : Fin (k+1)) : List (List (ℕ × Bool)) :=
  [[(cnt c, true), (nzw ⟨t, h⟩, false)]] ++
    (if 0 < c.val then
      [[(cnt ⟨c.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) c.isLt⟩, true), (nzw ⟨t, h⟩, true)]]
    else [])

lemma ct_terms_val {k : ℕ} (v : ℕ → Bool) (nzw : Fin k → ℕ) (t : ℕ) (h : t < k)
    (cnt : Fin (k+1) → ℕ)
    (hcnt : ∀ c : Fin (k+1), v (cnt c) = decide (ct_N v nzw t = c.val)) (c : Fin (k+1)) :
    dnfVal v (ct_terms nzw t h cnt c) = decide (ct_N v nzw (t+1) = c.val) := by
  rw [ct_N_succ v nzw t h]
  unfold ct_terms
  rw [Bool.eq_iff_iff]
  by_cases hc : 0 < c.val
  · rw [ite_eq_left hc]
    simp only [dnfVal, litVal, List.any_cons, List.all_cons, List.any_nil, List.all_nil,
      List.cons_append, List.nil_append, Bool.and_true, Bool.or_false, hcnt]
    cases hb : v (nzw ⟨t, h⟩)
    · simp
    · simp
      omega
  · rw [ite_eq_right hc]
    simp only [dnfVal, litVal, List.any_cons, List.all_cons, List.any_nil, List.all_nil,
      List.append_nil, Bool.and_true, Bool.or_false, hcnt]
    cases hb : v (nzw ⟨t, h⟩)
    · simp
    · simp
      omega

lemma ct_terms_cost {k : ℕ} (nzw : Fin k → ℕ) (t : ℕ) (h : t < k) (cnt : Fin (k+1) → ℕ)
    (c : Fin (k+1)) : dnfCost (ct_terms nzw t h cnt c) ≤ 13 := by
  unfold ct_terms
  by_cases hc : 0 < c.val
  · rw [ite_eq_left hc]
    simp [dnfCost]
  · rw [ite_eq_right hc]
    simp [dnfCost]

lemma ct_terms_wires {k : ℕ} (nzw : Fin k → ℕ) (t : ℕ) (h : t < k) (cnt : Fin (k+1) → ℕ)
    (B : ℕ) (hn : ∀ i, nzw i < B) (hcnt : ∀ c, cnt c < B) (c : Fin (k+1)) :
    ∀ u ∈ ct_terms nzw t h cnt c, ∀ l ∈ u, l.1 < B := by
  unfold ct_terms
  by_cases hc : 0 < c.val
  · rw [ite_eq_left hc]
    intro u hu l hl
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hu
    rcases hu with rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact hcnt _
      · exact hn _
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact hcnt _
      · exact hn _
  · rw [ite_eq_right hc]
    intro u hu l hl
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact hcnt _
    · exact hn _

-- terms of the output table
def ct_out {k : ℕ} (cnt : Fin (k+1) → ℕ) (j : ℕ) : List (List (ℕ × Bool)) :=
  ((List.finRange (k+1)).filter (fun c => c.val.testBit j)).map (fun c => [(cnt c, true)])

lemma ct_out_val {k : ℕ} (v : ℕ → Bool) (cnt : Fin (k+1) → ℕ) (N : ℕ) (hN : N ≤ k)
    (hcnt : ∀ c : Fin (k+1), v (cnt c) = decide (N = c.val)) (j : ℕ) :
    dnfVal v (ct_out cnt j) = N.testBit j := by
  unfold ct_out dnfVal
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨u, ⟨c, hc, rfl⟩, hu⟩
    simp only [List.all_cons, List.all_nil, Bool.and_true, litVal, hcnt c, beq_true,
      decide_eq_true_eq] at hu
    rw [hu]
    exact hc
  · intro hj
    refine ⟨_, ⟨⟨N, by omega⟩, hj, rfl⟩, ?_⟩
    simp [litVal, hcnt]

lemma ct_out_cost {k : ℕ} (cnt : Fin (k+1) → ℕ) (j : ℕ) :
    dnfCost (ct_out cnt j) ≤ 4 * k + 5 := by
  have h1 := dnfCost_le 1 (ct_out cnt j) (by
    intro u hu
    unfold ct_out at hu
    simp only [List.mem_map] at hu
    obtain ⟨c, _, rfl⟩ := hu
    simp)
  have hl : (ct_out cnt j).length ≤ k + 1 := by
    unfold ct_out
    rw [List.length_map]
    have h2 := List.length_filter_le (fun c : Fin (k+1) => c.val.testBit j) (List.finRange (k+1))
    rw [List.length_finRange] at h2
    exact h2
  nlinarith

lemma ct_out_wires {k : ℕ} (cnt : Fin (k+1) → ℕ) (B : ℕ) (hcnt : ∀ c, cnt c < B) (j : ℕ) :
    ∀ u ∈ ct_out cnt j, ∀ l ∈ u, l.1 < B := by
  intro u hu l hl
  unfold ct_out at hu
  simp only [List.mem_map] at hu
  obtain ⟨c, _, rfl⟩ := hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  subst hl
  exact hcnt c

noncomputable def ct_step (I : ℕ) {k : ℕ} (nzw : Fin k → ℕ) (t : ℕ) (cnt : Fin (k+1) → ℕ) :
    CG (Fin (k+1) → ℕ) :=
  if h : t < k then mkDnfTab I (Fin (k+1)) (ct_terms nzw t h cnt) else fun gs => (gs, cnt)

def ct_Inv (I : ℕ) {k : ℕ} (nzw : Fin k → ℕ) (L : ℕ) (t : ℕ) (gs : List Gate)
    (cnt : Fin (k+1) → ℕ) : Prop :=
  L ≤ gs.length ∧ (∀ c, cnt c < I + gs.length) ∧
  ∀ gs', Extends gs gs' → ∀ x : List Bool, x.length = I → ∀ c : Fin (k+1),
    wireAt gs' x (cnt c) = decide (ct_N (wireAt gs' x) nzw t = c.val)

lemma ct_step_spec {I k : ℕ} (nzw : Fin k → ℕ) (L : ℕ) (hw : ∀ i, nzw i < I + L)
    (t : ℕ) (cnt : Fin (k+1) → ℕ) (gs : List Gate) (ht : t < k) (hG : Good I gs)
    (hI : ct_Inv I nzw L t gs cnt) :
    Extends gs (ct_step I nzw t cnt gs).1 ∧
    (ct_step I nzw t cnt gs).1.length ≤ gs.length + (k+1) * 13 ∧
    Good I (ct_step I nzw t cnt gs).1 ∧
    ct_Inv I nzw L (t+1) (ct_step I nzw t cnt gs).1 (ct_step I nzw t cnt gs).2 := by
  obtain ⟨hL, hb, hv⟩ := hI
  have hs : ct_step I nzw t cnt = mkDnfTab I (Fin (k+1)) (ct_terms nzw t ht cnt) := by
    unfold ct_step
    rw [dite_eq_left ht]
  rw [hs]
  have s := mkDnfTab_spec (I := I) 13 (Fin (k+1)) (ct_terms nzw t ht cnt) gs hG
    (fun c => ct_terms_wires nzw t ht cnt (I + gs.length)
      (fun i => by have := hw i; omega) hb c)
    (fun c => ct_terms_cost nzw t ht cnt c)
  obtain ⟨e, len, g, wv, ev⟩ := s
  have hlen := extends_length_le e
  rw [Nat.card_fin] at len
  refine ⟨e, len, g, by omega, wv, fun gs' he x hx c => ?_⟩
  rw [ev gs' he x hx c]
  exact ct_terms_val _ nzw t ht cnt (fun c' => hv gs' (extends_trans e he) x hx c') c

lemma ct_arith (k l : ℕ) (hl : l ≤ k) :
    2 + k * ((k+1) * 13) + (l + 1) * (4 * k + 5) ≤ 40 * (k+2)^3 := by
  have h1 : (l + 1) * (4 * k + 5) ≤ (k + 1) * (4 * k + 5) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : 40 * (k+2)^3 = 40 * (k * k * k) + 240 * (k * k) + 480 * k + 320 := by ring
  have h3 : k * ((k+1) * 13) = 13 * (k * k) + 13 * k := by ring
  have h4 : (k + 1) * (4 * k + 5) = 4 * (k * k) + 9 * k + 5 := by ring
  have h5 : 0 ≤ k * k * k := Nat.zero_le _
  omega

theorem count_circuit {I : ℕ} (k : ℕ) (gs : List Gate) (hG : Good I gs) (nzw : Fin k → ℕ)
    (hw : ∀ i, nzw i < I + gs.length) :
    ∃ (gs2 : List Gate) (dw : Fin (Nat.log2 k + 1) → ℕ),
      Extends gs gs2 ∧ gs2.length ≤ gs.length + 40 * (k+2)^3 ∧ Good I gs2 ∧
      (∀ j, dw j < I + gs2.length) ∧
      ∀ gs', Extends gs2 gs' → ∀ x : List Bool, x.length = I → ∀ j,
        wireAt gs' x (dw j) =
          ((Finset.univ.filter (fun i : Fin k => wireAt gs' x (nzw i) = true)).card).testBit j.val := by
  -- constants
  rcases h1 : mkConst I true gs with ⟨gsa, ow⟩
  have s1 := mkConst_spec true hG
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1, w1, ev1⟩
  rcases h2 : mkConst I false gsa with ⟨gsb, zw⟩
  have s2 := mkConst_spec false g1
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2, w2, ev2⟩
  -- the counter
  have hinv0 : ct_Inv I nzw gs.length 0 gsb
      (fun c : Fin (k+1) => if c.val = 0 then ow else zw) := by
    refine ⟨by omega, fun c => ?_, fun gs' he x hx c => ?_⟩
    · by_cases hc : c.val = 0
      · simp only [ite_eq_left hc]
        omega
      · simp only [ite_eq_right hc]
        exact w2
    · rw [ct_N_zero]
      by_cases hc : c.val = 0
      · simp only [ite_eq_left hc]
        rw [wireAt_extends (extends_trans e2 he) x (by omega), ev1 x hx]
        simp [hc]
      · simp only [ite_eq_right hc]
        rw [wireAt_extends he x (by omega), ev2 x hx]
        have hc' : ¬ (0 = c.val) := fun h => hc h.symm
        simp [hc']
  have hit := iterCG_spec (I := I) (ct_step I nzw) (ct_Inv I nzw gs.length) ((k+1) * 13) k
    (fun t a gs' ht hG' hI => ct_step_spec nzw gs.length hw t a gs' ht hG' hI)
    (fun c : Fin (k+1) => if c.val = 0 then ow else zw) gsb g2 hinv0 k le_rfl
  rcases h3 : iterCG (ct_step I nzw) k
    (fun c : Fin (k+1) => if c.val = 0 then ow else zw) gsb with ⟨gsc, cnt⟩
  simp only [h3] at hit
  obtain ⟨e3, l3, g3, hL, hb, hv⟩ := hit
  -- output table
  have s4 := mkDnfTab_spec (I := I) (4 * k + 5) (Fin (Nat.log2 k + 1))
    (fun j => ct_out cnt j.val) gsc g3
    (fun j => ct_out_wires cnt (I + gsc.length) hb j.val)
    (fun j => ct_out_cost cnt j.val)
  rcases h4 : mkDnfTab I (Fin (Nat.log2 k + 1)) (fun j => ct_out cnt j.val) gsc with ⟨gsd, dw⟩
  simp only [h4] at s4
  obtain ⟨e4, l4, g4, w4, ev4⟩ := s4
  rw [Nat.card_fin] at l4
  refine ⟨gsd, dw, extends_trans e1 (extends_trans e2 (extends_trans e3 e4)), ?_, g4, w4,
    fun gs' he x hx j => ?_⟩
  · have ha := ct_arith k (Nat.log2 k) (Nat.log2_le_self k)
    omega
  · rw [ev4 gs' he x hx j, ← ct_N_full (wireAt gs' x) nzw]
    exact ct_out_val (wireAt gs' x) cnt _ (ct_N_le _ nzw k)
      (fun c => hv gs' (extends_trans e4 he) x hx c) j.val

end CtCount


section Sem

open PEqualNP.CircuitLowerBounds

theorem ix_eq {k : ℕ} (hk : 0 < k) {a b : ℕ} (c d : ℕ) (h : a + k*c = b + k*d) :
    ix hk a = ix hk b := by
  apply Fin.ext
  show a % k = b % k
  have h1 : (a + k*c) % k = a % k := Nat.add_mul_mod_self_left a k c
  have h2 : (b + k*d) % k = b % k := Nat.add_mul_mod_self_left b k d
  rw [← h1, ← h2, h]

theorem ix_val {k : ℕ} (hk : 0 < k) (t : Fin k) : ix hk t.val = t :=
  Fin.ext (Nat.mod_eq_of_lt t.2)

theorem ix_md {k : ℕ} (hk : 0 < k) (a : ℕ) : (ix hk a).val + k * (a / k) = a :=
  Nat.mod_add_div a k

abbrev LNode (H s : ℕ) := (Fin H → Fin s → Fin s → ZMod 2) ×
  (Option (Fin s → ZMod 2) × Option (Fin s → ZMod 2)) ×
  (Option (Fin s → ZMod 2) × Option (Fin s → ZMod 2))

def NLegal {k : ℕ} (hk : 0 < k) {H s : ℕ} (marked : Bool → Fin k → Bool)
    (P : Fin (k+1) → LNode H s) : Prop :=
  (P 0).2.2 = (P 0).2.1 ∧ (P (Fin.last k)).2.2 = (P (Fin.last k)).2.1 ∧
  ∀ t : Fin k, (P t.succ).1 = (P t.castSucc).1 ∧ (P t.succ).2.1 = (P t.castSucc).2.1 ∧
    (marked false (ix hk (t.val+2*k-2)) = true →
      EdgeOK (P t.castSucc).1 (P t.castSucc).2.2.1 (P t.succ).2.2.1) ∧
    (marked true (ix hk (t.val+k-1)) = true →
      EdgeOK (P t.castSucc).1 (P t.castSucc).2.2.2 (P t.succ).2.2.2)

def NPoss {k : ℕ} (hk : 0 < k) {H s r : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (P : Fin (k+1) → LNode H s) (x : Fin k → ZMod 2) : Prop :=
  ∃ Y : Fin (k+1) → Idx r s → ZMod 2, ∀ t : Fin k,
    ∀ q ∈ (eqs k t.val (P t.castSucc).2.2.1 (P t.castSucc).2.2.2 (P t.succ).2.2.1
        (P t.succ).2.2.2 : List (SEq r s)),
      holds (marked false (ix hk (t.val+2*k-2))) (marked true (ix hk (t.val+k-1)))
        (fun i => M i t) q (Y t.castSucc) (x t) (Y t.succ)

theorem path_sound {k : ℕ} (hk : 0 < k) {H s r : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (P : Fin (k+1) → LNode H s) (hP : NLegal hk marked P) :
    ∃ (g : Fin H → Fin s → Fin s → ZMod 2) (lab : Bool → Fin k → Option (Fin s → ZMod 2)),
      LValid hk marked g lab ∧ ∀ x, NPoss hk marked M P x → LSol hk marked M lab x := by
  obtain ⟨hst, hsp, hed⟩ := hP
  have hconst : ∀ t : Fin (k+1), (P t).1 = (P 0).1 ∧ (P t).2.1 = (P 0).2.1 := by
    intro t
    induction t using Fin.induction with
    | zero => exact ⟨rfl, rfl⟩
    | succ i ih => exact ⟨(hed i).1.trans ih.1, (hed i).2.1.trans ih.2⟩
  let lab : Bool → Fin k → Option (Fin s → ZMod 2) := fun col v =>
    match col with
    | true => (P v.castSucc).2.2.2
    | false => (P v.succ).2.2.1
  have h3 : ∀ t : Fin k, lab false (ix hk t.val) = (P t.succ).2.2.1 := by
    intro t; rw [ix_val]
  have h2 : ∀ t : Fin k, lab true (ix hk t.val) = (P t.castSucc).2.2.2 := by
    intro t; rw [ix_val]
  have h1 : ∀ t : Fin k, lab false (ix hk (t.val+k-1)) = (P t.castSucc).2.2.1 := by
    intro t
    by_cases ht : t.val = 0
    · have e1 : (ix hk (t.val+k-1)).succ = Fin.last k := by
        apply Fin.ext
        show (t.val+k-1) % k + 1 = k
        rw [ht, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
        omega
      have e2 : t.castSucc = 0 := Fin.ext ht
      show (P (ix hk (t.val+k-1)).succ).2.2.1 = (P t.castSucc).2.2.1
      rw [e1, e2, hsp, hst, (hconst (Fin.last k)).2]
    · have e1 : (ix hk (t.val+k-1)).succ = t.castSucc := by
        apply Fin.ext
        show (t.val+k-1) % k + 1 = t.val
        have e : t.val + k - 1 = (t.val - 1) + k := by omega
        rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      show (P (ix hk (t.val+k-1)).succ).2.2.1 = (P t.castSucc).2.2.1
      rw [e1]
  have h4 : ∀ t : Fin k, lab true (ix hk (t.val+1)) = (P t.succ).2.2.2 := by
    intro t
    by_cases ht : t.val + 1 = k
    · have e1 : (ix hk (t.val+1)).castSucc = 0 := by
        apply Fin.ext
        show (t.val+1) % k = 0
        rw [ht, Nat.mod_self]
      have e2 : t.succ = Fin.last k := Fin.ext ht
      show (P (ix hk (t.val+1)).castSucc).2.2.2 = (P t.succ).2.2.2
      rw [e1, e2, hsp, hst, (hconst (Fin.last k)).2]
    · have e1 : (ix hk (t.val+1)).castSucc = t.succ := by
        apply Fin.ext
        show (t.val+1) % k = t.val + 1
        exact Nat.mod_eq_of_lt (by omega)
      show (P (ix hk (t.val+1)).castSucc).2.2.2 = (P t.succ).2.2.2
      rw [e1]
  refine ⟨(P 0).1, lab, ?_, ?_⟩
  · intro col j hm
    cases col with
    | false =>
      have hq := ix_md hk (j.val+2)
      have e1 : ix hk ((ix hk (j.val+2)).val + 2*k - 2) = j :=
        (ix_eq hk ((j.val+2)/k) 2 (by omega)).trans (ix_val hk j)
      have e2 : ix hk ((ix hk (j.val+2)).val + k - 1) = ix hk (j.val+1) :=
        ix_eq hk ((j.val+2)/k) 1 (by omega)
      have hE := (hed (ix hk (j.val+2))).2.2.1 (by rw [e1]; exact hm)
      rw [(hconst _).1, ← h1, ← h3, e2, ix_val] at hE
      exact hE
    | true =>
      have hq := ix_md hk (j.val+1)
      have e1 : ix hk ((ix hk (j.val+1)).val + k - 1) = j :=
        (ix_eq hk ((j.val+1)/k) 1 (by omega)).trans (ix_val hk j)
      have e2 : ix hk ((ix hk (j.val+1)).val + 1) = ix hk (j.val+2) :=
        ix_eq hk ((j.val+1)/k) 0 (by omega)
      have hE := (hed (ix hk (j.val+1))).2.2.2 (by rw [e1]; exact hm)
      rw [(hconst _).1, ← h2, ← h4, e2, ix_val] at hE
      exact hE
  · rintro x ⟨Y, hY⟩
    refine (scan_iff hk marked M lab x).mp ⟨Y, fun t q hq => hY t q ?_⟩
    rw [h1, h2, h3, h4] at hq
    exact hq

theorem path_complete {k : ℕ} (hk : 0 < k) {H s r : ℕ} (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (g : Fin H → Fin s → Fin s → ZMod 2)
    (lab : Bool → Fin k → Option (Fin s → ZMod 2)) (hv : LValid hk marked g lab) :
    ∃ P : Fin (k+1) → LNode H s, NLegal hk marked P ∧
      ∀ x, LSol hk marked M lab x → NPoss hk marked M P x := by
  refine ⟨fun t => (g, (lab false (ix hk (k-1)), lab true (ix hk 0)),
    (lab false (ix hk (t.val+k-1)), lab true (ix hk t.val))), ⟨?_, ?_, ?_⟩, ?_⟩
  · show (lab false (ix hk ((0 : Fin (k+1)).val+k-1)), lab true (ix hk (0 : Fin (k+1)).val)) =
      (lab false (ix hk (k-1)), lab true (ix hk 0))
    simp
  · show (lab false (ix hk ((Fin.last k).val+k-1)), lab true (ix hk (Fin.last k).val)) =
      (lab false (ix hk (k-1)), lab true (ix hk 0))
    have e1 : ix hk ((Fin.last k).val+k-1) = ix hk (k-1) :=
      ix_eq hk 0 1 (by simp only [Fin.val_last]; omega)
    have e2 : ix hk (Fin.last k).val = ix hk 0 :=
      ix_eq hk 0 1 (by simp only [Fin.val_last]; omega)
    rw [e1, e2]
  · intro t
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro hm
      have hq := ix_md hk (t.val+2*k-2)
      have e1 : ix hk ((ix hk (t.val+2*k-2)).val + 1) = ix hk (t.castSucc.val+k-1) :=
        ix_eq hk ((t.val+2*k-2)/k) 1 (by simp only [Fin.val_castSucc]; omega)
      have e2 : ix hk ((ix hk (t.val+2*k-2)).val + 2) = ix hk (t.succ.val+k-1) :=
        ix_eq hk ((t.val+2*k-2)/k) 1 (by simp only [Fin.val_succ]; omega)
      have hE := hv false (ix hk (t.val+2*k-2)) hm
      rw [e1, e2] at hE
      exact hE
    · intro hm
      have hq := ix_md hk (t.val+k-1)
      have e1 : ix hk ((ix hk (t.val+k-1)).val + 1) = ix hk t.castSucc.val :=
        ix_eq hk ((t.val+k-1)/k) 1 (by simp only [Fin.val_castSucc]; omega)
      have e2 : ix hk ((ix hk (t.val+k-1)).val + 2) = ix hk t.succ.val :=
        ix_eq hk ((t.val+k-1)/k) 1 (by simp only [Fin.val_succ]; omega)
      have hE := hv true (ix hk (t.val+k-1)) hm
      rw [e1, e2] at hE
      exact hE
  · intro x hx
    obtain ⟨Y, hY⟩ := (scan_iff hk marked M lab x).mpr hx
    refine ⟨Y, fun t q hq => hY t q ?_⟩
    have e1 : ix hk (t.succ.val+k-1) = ix hk t.val :=
      ix_eq hk 0 1 (by simp only [Fin.val_succ]; omega)
    have hq' : q ∈ (eqs k t.val (lab false (ix hk (t.castSucc.val+k-1)))
        (lab true (ix hk t.castSucc.val)) (lab false (ix hk (t.succ.val+k-1)))
        (lab true (ix hk t.succ.val)) : List (SEq r s)) := hq
    rw [e1] at hq'
    exact hq'

theorem eqs_length {r s : ℕ} (k t : ℕ) (pr pc cr cc : Option (Fin s → ZMod 2)) :
    (eqs k t pr pc cr cc : List (SEq r s)).length ≤ 3*r + s + 24 := by
  unfold eqs
  simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
  split_ifs <;> simp <;> omega

theorem holds_zero {r s : ℕ} (mr mc : Bool) (mcol : Fin r → ZMod 2)
    (Y : Idx r s → ZMod 2) (xt : ZMod 2) (Y' : Idx r s → ZMod 2) :
    holds mr mc mcol (zeroEq : SEq r s) Y xt Y' := by
  simp [holds, zeroEq, Src.val]

noncomputable def eq807 {r s d w : ℕ} (eI : Idx r s ≃ Fin w) (L : List (SEq r s))
    (mr mc : Bool) (mcol : Fin r → ZMod 2) (e : Fin d) :
    (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2) :=
  ((fun l => ((L.getD e.val zeroEq).1 (eI.symm l)).val mr mc mcol),
    (L.getD e.val zeroEq).2.1.val mr mc mcol,
    (fun l => ((L.getD e.val zeroEq).2.2 (eI.symm l)).val mr mc mcol))

theorem eq807_holds {r s d w : ℕ} (eI : Idx r s ≃ Fin w) (L : List (SEq r s))
    (mr mc : Bool) (mcol : Fin r → ZMod 2) (e : Fin d) (y y' : Fin w → ZMod 2) (xt : ZMod 2) :
    (dotProduct (eq807 eI L mr mc mcol e).1 y + (eq807 eI L mr mc mcol e).2.1 * xt +
      dotProduct (eq807 eI L mr mc mcol e).2.2 y' = 0) ↔
    holds mr mc mcol (L.getD e.val zeroEq) (fun i => y (eI i)) xt (fun i => y' (eI i)) := by
  unfold holds eq807 dotProduct
  have h1 : (∑ l : Fin w, Src.val mr mc mcol ((L.getD e.val zeroEq).1 (eI.symm l)) * y l) =
      ∑ i : Idx r s, Src.val mr mc mcol ((L.getD e.val zeroEq).1 i) * y (eI i) :=
    Fintype.sum_equiv eI.symm _ _ (fun l => by simp)
  have h2 : (∑ l : Fin w, Src.val mr mc mcol ((L.getD e.val zeroEq).2.2 (eI.symm l)) * y' l) =
      ∑ i : Idx r s, Src.val mr mc mcol ((L.getD e.val zeroEq).2.2 i) * y' (eI i) :=
    Fintype.sum_equiv eI.symm _ _ (fun l => by simp)
  show (∑ l : Fin w, Src.val mr mc mcol ((L.getD e.val zeroEq).1 (eI.symm l)) * y l) +
      Src.val mr mc mcol (L.getD e.val zeroEq).2.1 * xt +
      (∑ l : Fin w, Src.val mr mc mcol ((L.getD e.val zeroEq).2.2 (eI.symm l)) * y' l) = 0 ↔ _
  rw [h1, h2]

theorem holds_all_iff {r s d : ℕ} (L : List (SEq r s)) (hL : L.length ≤ d)
    (mr mc : Bool) (mcol : Fin r → ZMod 2) (Y : Idx r s → ZMod 2) (xt : ZMod 2)
    (Y' : Idx r s → ZMod 2) :
    (∀ e : Fin d, holds mr mc mcol (L.getD e.val zeroEq) Y xt Y') ↔
      ∀ q ∈ L, holds mr mc mcol q Y xt Y' := by
  constructor
  · intro h q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    have := h ⟨i, by omega⟩
    rwa [List.getD_eq_getElem _ _ hi] at this
  · intro h e
    by_cases he : e.val < L.length
    · rw [List.getD_eq_getElem _ _ he]
      exact h _ (List.getElem_mem he)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact holds_zero mr mc mcol Y xt Y'

def Legal807 {n s8 : ℕ} (start stop : Fin s8 → Bool) (edge : Fin n → Fin s8 → Fin s8 → Bool)
    (p : Fin (n+1) → Fin s8) : Prop :=
  start (p 0) = true ∧ stop (p (Fin.last n)) = true ∧
    ∀ t : Fin n, edge t (p t.castSucc) (p t.succ) = true

def Poss807 {n s8 d w : ℕ}
    (equation : Fin n → Fin s8 → Fin s8 → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (p : Fin (n+1) → Fin s8) (x : Fin n → ZMod 2) : Prop :=
  ∃ y : Fin (n+1) → (Fin w → ZMod 2), ∀ (t : Fin n) (j : Fin d),
    dotProduct (equation t (p t.castSucc) (p t.succ) j).1 (y t.castSucc) +
      (equation t (p t.castSucc) (p t.succ) j).2.1 * x t +
      dotProduct (equation t (p t.castSucc) (p t.succ) j).2.2 (y t.succ) = 0

open Classical in
noncomputable def stS {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8) (i : Fin s8) : Bool :=
  decide ((eN.symm i).2.2 = (eN.symm i).2.1)

open Classical in
noncomputable def edS {k : ℕ} (hk : 0 < k) {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8)
    (marked : Bool → Fin k → Bool) (t : Fin k) (i j : Fin s8) : Bool :=
  decide ((eN.symm j).1 = (eN.symm i).1 ∧ (eN.symm j).2.1 = (eN.symm i).2.1 ∧
    (marked false (ix hk (t.val+2*k-2)) = true →
      EdgeOK (eN.symm i).1 (eN.symm i).2.2.1 (eN.symm j).2.2.1) ∧
    (marked true (ix hk (t.val+k-1)) = true →
      EdgeOK (eN.symm i).1 (eN.symm i).2.2.2 (eN.symm j).2.2.2))

noncomputable def eqS {k : ℕ} (hk : 0 < k) {H s r s8 d w : ℕ} (eN : LNode H s ≃ Fin s8)
    (eI : Idx r s ≃ Fin w) (marked : Bool → Fin k → Bool) (M : Fin r → Fin k → ZMod 2)
    (t : Fin k) (i j : Fin s8) (e : Fin d) : (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2) :=
  eq807 eI (eqs k t.val (eN.symm i).2.2.1 (eN.symm i).2.2.2 (eN.symm j).2.2.1
      (eN.symm j).2.2.2)
    (marked false (ix hk (t.val+2*k-2))) (marked true (ix hk (t.val+k-1))) (fun a => M a t) e

theorem legal_iff {k : ℕ} (hk : 0 < k) {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8)
    (marked : Bool → Fin k → Bool) (p : Fin (k+1) → Fin s8) :
    Legal807 (stS eN) (stS eN) (edS hk eN marked) p ↔
      NLegal hk marked (fun t => eN.symm (p t)) := by
  unfold Legal807 NLegal stS edS
  simp only [decide_eq_true_eq]

theorem poss_iff807 {k : ℕ} (hk : 0 < k) {H s r s8 d w : ℕ} (eN : LNode H s ≃ Fin s8)
    (eI : Idx r s ≃ Fin w) (marked : Bool → Fin k → Bool) (M : Fin r → Fin k → ZMod 2)
    (hd : 3*r + s + 24 ≤ d) (p : Fin (k+1) → Fin s8) (x : Fin k → ZMod 2) :
    Poss807 (eqS hk eN eI marked M (d := d)) p x ↔
      NPoss hk marked M (fun t => eN.symm (p t)) x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun t i => y t (eI i), fun t => ?_⟩
    refine (holds_all_iff (d := d) _ (le_trans (eqs_length _ _ _ _ _ _) hd) _ _ _ _ _ _).mp ?_
    intro e
    exact (eq807_holds eI _ _ _ _ e (y t.castSucc) (y t.succ) (x t)).mp (hy t e)
  · rintro ⟨Y, hY⟩
    refine ⟨fun t l => Y t (eI.symm l), fun t e => ?_⟩
    refine (eq807_holds eI _ _ _ _ e _ _ (x t)).mpr ?_
    have h := (holds_all_iff (d := d) _ (le_trans (eqs_length _ _ _ _ _ _) hd) _ _ _ _ _ _).mpr
      (hY t) e
    simpa using h

theorem sem_core {k : ℕ} (hk : 0 < k) (m h r s8 d w : ℕ) (Q : Fin m → Fin k → ZMod 2)
    (marked : Bool → Fin k → Bool) (M : Fin r → Fin k → ZMod 2)
    (hMQ : ∀ x : Fin k → ZMod 2, (∀ i, dotProduct (M i) x = 0) ↔ (∀ i, dotProduct (Q i) x = 0))
    (eN : LNode (min h (2*k)) (2 * min h (2*k)) ≃ Fin s8)
    (eI : Idx r (2 * min h (2*k)) ≃ Fin w) (hd : 3*r + 2 * min h (2*k) + 24 ≤ d) :
    (∃ p, Legal807 (stS eN) (stS eN) (edS hk eN marked) p) ∧
    ∀ p, Legal807 (stS eN) (stS eN) (edS hk eN marked) p →
      ∀ K : Submodule (ZMod 2) (Fin k → ZMod 2),
      (∀ x, x ∈ K ↔ Poss807 (eqS hk eN eI marked M (d := d)) p x) →
      (∀ q, Legal807 (stS eN) (stS eN) (edS hk eN marked) q →
        Nat.card {x : Fin k → ZMod 2 // Poss807 (eqS hk eN eI marked M (d := d)) q x} ≤
          2^(Module.finrank (ZMod 2) K)) →
      Adm hk m h Q marked K ∧ ∀ U : Submodule (ZMod 2) (Fin k → ZMod 2),
        Adm hk m h Q marked U → Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) K := by
  constructor
  · obtain ⟨P, hP, -⟩ := path_complete hk (H := min h (2*k)) (s := 2 * min h (2*k)) marked M
      (fun _ _ _ => 0) (fun _ _ => none) (by intro col j _; simp [EdgeOK])
    refine ⟨fun t => eN (P t), (legal_iff hk eN marked _).mpr ?_⟩
    simpa using hP
  · intro p hp K hK hmax
    have hP := (legal_iff hk eN marked p).mp hp
    obtain ⟨g, lab, hv, hsol⟩ := path_sound hk marked M _ hP
    refine ⟨sound hk m h _ _ r (Nat.min_le_left _ _) Q marked M (fun x hx => (hMQ x).mp hx) g lab hv K
      (fun x hx => hsol x ((poss_iff807 hk eN eI marked M hd p x).mp ((hK x).mp hx))), ?_⟩
    intro U hU
    obtain ⟨g2, lab2, hv2, hU2⟩ := complete hk m h r Q marked M (fun x hx => (hMQ x).mpr hx) U hU
    obtain ⟨P2, hP2, hposs2⟩ := path_complete hk marked M g2 lab2 hv2
    have hq : Legal807 (stS eN) (stS eN) (edS hk eN marked) (fun t => eN (P2 t)) := by
      refine (legal_iff hk eN marked _).mpr ?_
      simpa using hP2
    have hcard := hmax _ hq
    have hin : ∀ x : {x : Fin k → ZMod 2 // x ∈ U},
        Poss807 (eqS hk eN eI marked M (d := d)) (fun t => eN (P2 t)) x.val := by
      intro x
      refine (poss_iff807 hk eN eI marked M hd _ x.val).mpr ?_
      have := hposs2 x.val (hU2 x.val x.property)
      simpa using this
    have hle : Nat.card {x : Fin k → ZMod 2 // x ∈ U} ≤
        Nat.card {x : Fin k → ZMod 2 // Poss807 (eqS hk eN eI marked M (d := d))
          (fun t => eN (P2 t)) x} :=
      Nat.card_le_card_of_injective (fun x => ⟨x.val, hin x⟩)
        (fun a b hab => by
          have h := congrArg (fun z => z.val) hab
          exact Subtype.ext h)
    rw [m2_card_sub] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (le_trans hle hcard)

end Sem


section Front

open PEqualNP.CircuitLowerBounds

-- input layout facts
theorem fr_qlen {α : Type} (m k : ℕ) (f : Fin m → Fin k → α) :
    (List.ofFn (fun i => List.ofFn (fun c : Fin k => f i c))).flatten.length = m * k := by
  rw [List.ofFn_eq_map, ← List.flatMap_def]
  exact b_flat_len m k _ (fun i => List.length_ofFn)

theorem fr_input {α : Type} (A : List α) (n : ℕ) (hA : A.length = n) (k : ℕ)
    (f g : Fin k → α) (d : α) :
    (A ++ List.ofFn f ++ List.ofFn g).length = n + k + k ∧
    (∀ j : Fin k, (A ++ List.ofFn f ++ List.ofFn g).getD (n + j.val) d = f j) ∧
    (∀ j : Fin k, (A ++ List.ofFn f ++ List.ofFn g).getD (n + k + j.val) d = g j) := by
  refine ⟨by simp only [List.length_append, List.length_ofFn, hA], fun j => ?_, fun j => ?_⟩
  · rw [getD_append_lt _ _ (by simp [hA]), getD_append_ge _ _ (by simp [hA])]
    simp [hA, List.getD_eq_getElem?_getD]
  · rw [getD_append_ge _ _ (by simp [hA])]
    simp [hA, List.getD_eq_getElem?_getD]

def fr_mrW {k : ℕ} (hk : 0 < k) (m : ℕ) (t : Fin k) : ℕ := m*k + (ix hk (t.val+2*k-2)).val

def fr_mcW {k : ℕ} (hk : 0 < k) (m : ℕ) (t : Fin k) : ℕ := m*k + k + (ix hk (t.val+k-1)).val

theorem fr_mrW_lt {k : ℕ} (hk : 0 < k) (m : ℕ) (t : Fin k) : fr_mrW hk m t < (m+2)*k := by
  have h : (m+2)*k = m*k + k + k := by ring
  have h2 := (ix hk (t.val+2*k-2)).isLt
  unfold fr_mrW
  omega

theorem fr_mcW_lt {k : ℕ} (hk : 0 < k) (m : ℕ) (t : Fin k) : fr_mcW hk m t < (m+2)*k := by
  have h : (m+2)*k = m*k + k + k := by ring
  have h2 := (ix hk (t.val+k-1)).isLt
  unfold fr_mcW
  omega

-- the DNF of a source
def fr_srcTerms {r : ℕ} (a b : ℕ) (sw : Fin r → ℕ) : Src r → List (List (ℕ × Bool))
  | Src.c0 => []
  | Src.c1 => [[]]
  | Src.mr => [[(a, true)]]
  | Src.mc => [[(b, true)]]
  | Src.mb i => [[(sw i, true)]]

theorem fr_srcTerms_val {r : ℕ} (V : ℕ → Bool) (a b : ℕ) (sw : Fin r → ℕ) (mrb mcb : Bool)
    (mcol : Fin r → ZMod 2) (ha : V a = mrb) (hb : V b = mcb)
    (hs : ∀ i, V (sw i) = decide (mcol i ≠ 0)) (src : Src r) :
    dnfVal V (fr_srcTerms a b sw src) = decide (Src.val mrb mcb mcol src ≠ 0) := by
  cases src with
  | c0 => simp [fr_srcTerms, dnfVal, Src.val]
  | c1 => simp [fr_srcTerms, dnfVal, Src.val]
  | mr => cases mrb <;> simp [fr_srcTerms, dnfVal, litVal, Src.val, ha]
  | mc => cases mcb <;> simp [fr_srcTerms, dnfVal, litVal, Src.val, hb]
  | mb i =>
    rw [show dnfVal V (fr_srcTerms a b sw (Src.mb i)) = V (sw i) from by
      simp [fr_srcTerms, dnfVal, litVal], hs]
    rfl

theorem fr_srcTerms_lits {r : ℕ} (a b B : ℕ) (sw : Fin r → ℕ) (ha : a < B) (hb : b < B)
    (hs : ∀ i, sw i < B) (src : Src r) :
    ∀ t ∈ fr_srcTerms a b sw src, ∀ l ∈ t, l.1 < B := by
  intro t ht l hl
  cases src with
  | c0 => simp [fr_srcTerms] at ht
  | c1 =>
    simp only [fr_srcTerms, List.mem_singleton] at ht
    subst ht
    simp at hl
  | mr =>
    simp only [fr_srcTerms, List.mem_singleton] at ht
    subst ht
    simp only [List.mem_singleton] at hl
    subst hl
    exact ha
  | mc =>
    simp only [fr_srcTerms, List.mem_singleton] at ht
    subst ht
    simp only [List.mem_singleton] at hl
    subst hl
    exact hb
  | mb i =>
    simp only [fr_srcTerms, List.mem_singleton] at ht
    subst ht
    simp only [List.mem_singleton] at hl
    subst hl
    exact hs i

theorem fr_srcTerms_cost {r : ℕ} (a b : ℕ) (sw : Fin r → ℕ) (src : Src r) :
    dnfCost (fr_srcTerms a b sw src) ≤ 7 := by
  cases src <;> simp [fr_srcTerms, dnfCost]

-- table 1: start / stop bits
noncomputable def fr_stTerms {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8) (i : Fin s8) :
    List (List (ℕ × Bool)) :=
  if stS eN i = true then [[]] else []

theorem fr_stTerms_val {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8) (V : ℕ → Bool) (i : Fin s8) :
    dnfVal V (fr_stTerms eN i) = stS eN i := by
  unfold fr_stTerms
  cases stS eN i <;> simp [dnfVal]

theorem fr_stTerms_lits {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8) (B : ℕ) (i : Fin s8) :
    ∀ t ∈ fr_stTerms eN i, ∀ l ∈ t, l.1 < B := by
  intro t ht l hl
  unfold fr_stTerms at ht
  split_ifs at ht
  · simp only [List.mem_singleton] at ht
    subst ht
    simp at hl
  · simp at ht

theorem fr_stTerms_cost {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8) (i : Fin s8) :
    dnfCost (fr_stTerms eN i) ≤ 7 := by
  unfold fr_stTerms
  split_ifs <;> simp [dnfCost]

-- table 2: edge bits
def fr_edT (P E1 E2 : Prop) [Decidable P] [Decidable E1] [Decidable E2] (a b : ℕ) :
    List (List (ℕ × Bool)) :=
  if P then [(if E1 then [] else [(a, false)]) ++ (if E2 then [] else [(b, false)])] else []

theorem fr_edT_val (P E1 E2 : Prop) [Decidable P] [Decidable E1] [Decidable E2] (a b : ℕ)
    (V : ℕ → Bool) :
    dnfVal V (fr_edT P E1 E2 a b) = true ↔ P ∧ (V a = true → E1) ∧ (V b = true → E2) := by
  unfold fr_edT
  by_cases hP : P <;> by_cases h1 : E1 <;> by_cases h2 : E2 <;>
    simp [dnfVal, litVal, hP, h1, h2]

theorem fr_edT_lits (P E1 E2 : Prop) [Decidable P] [Decidable E1] [Decidable E2] (a b B : ℕ)
    (ha : a < B) (hb : b < B) :
    ∀ t ∈ fr_edT P E1 E2 a b, ∀ l ∈ t, l.1 < B := by
  intro t ht l hl
  unfold fr_edT at ht
  by_cases hP : P
  · simp only [hP, ↓reduceIte, List.mem_singleton] at ht
    subst ht
    rw [List.mem_append] at hl
    rcases hl with hl | hl
    · by_cases h1 : E1
      · simp only [h1, ↓reduceIte, List.not_mem_nil] at hl
      · simp only [h1, ↓reduceIte, List.mem_singleton] at hl
        subst hl
        exact ha
    · by_cases h2 : E2
      · simp only [h2, ↓reduceIte, List.not_mem_nil] at hl
      · simp only [h2, ↓reduceIte, List.mem_singleton] at hl
        subst hl
        exact hb
  · simp only [hP, ↓reduceIte, List.not_mem_nil] at ht

theorem fr_edT_cost (P E1 E2 : Prop) [Decidable P] [Decidable E1] [Decidable E2] (a b : ℕ) :
    dnfCost (fr_edT P E1 E2 a b) ≤ 7 := by
  unfold fr_edT
  by_cases hP : P <;> by_cases h1 : E1 <;> by_cases h2 : E2 <;>
    simp [dnfCost, hP, h1, h2]

open Classical in
noncomputable def fr_edTerms {k : ℕ} (hk : 0 < k) (m : ℕ) {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8)
    (p : Fin k × Fin s8 × Fin s8) : List (List (ℕ × Bool)) :=
  fr_edT ((eN.symm p.2.2).1 = (eN.symm p.2.1).1 ∧ (eN.symm p.2.2).2.1 = (eN.symm p.2.1).2.1)
    (EdgeOK (eN.symm p.2.1).1 (eN.symm p.2.1).2.2.1 (eN.symm p.2.2).2.2.1)
    (EdgeOK (eN.symm p.2.1).1 (eN.symm p.2.1).2.2.2 (eN.symm p.2.2).2.2.2)
    (fr_mrW hk m p.1) (fr_mcW hk m p.1)

theorem fr_edTerms_val {k : ℕ} (hk : 0 < k) (m : ℕ) {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8)
    (marked : Bool → Fin k → Bool) (V : ℕ → Bool) (t : Fin k) (i j : Fin s8)
    (ha : V (fr_mrW hk m t) = marked false (ix hk (t.val+2*k-2)))
    (hb : V (fr_mcW hk m t) = marked true (ix hk (t.val+k-1))) :
    dnfVal V (fr_edTerms hk m eN (t, i, j)) = edS hk eN marked t i j := by
  rw [Bool.eq_iff_iff]
  unfold fr_edTerms edS
  rw [fr_edT_val, ha, hb]
  simp only [decide_eq_true_eq, and_assoc]

open Classical in
theorem fr_edTerms_lits {k : ℕ} (hk : 0 < k) (m : ℕ) {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8)
    (B : ℕ) (hB : (m+2)*k ≤ B) (p : Fin k × Fin s8 × Fin s8) :
    ∀ t ∈ fr_edTerms hk m eN p, ∀ l ∈ t, l.1 < B :=
  fr_edT_lits _ _ _ _ _ B (lt_of_lt_of_le (fr_mrW_lt hk m p.1) hB)
    (lt_of_lt_of_le (fr_mcW_lt hk m p.1) hB)

open Classical in
theorem fr_edTerms_cost {k : ℕ} (hk : 0 < k) (m : ℕ) {H s s8 : ℕ} (eN : LNode H s ≃ Fin s8)
    (p : Fin k × Fin s8 × Fin s8) : dnfCost (fr_edTerms hk m eN p) ≤ 7 :=
  fr_edT_cost _ _ _ _ _

-- table 3: coefficient bits
def fr_coT {r s w : ℕ} (eI : Idx r s ≃ Fin w) (a b : ℕ) (sw : Fin r → ℕ) (q : SEq r s) :
    Fin w ⊕ Unit ⊕ Fin w → List (List (ℕ × Bool))
  | Sum.inl l => fr_srcTerms a b sw (q.1 (eI.symm l))
  | Sum.inr (Sum.inl _) => fr_srcTerms a b sw q.2.1
  | Sum.inr (Sum.inr l) => fr_srcTerms a b sw (q.2.2 (eI.symm l))

def fr_coTerms {k : ℕ} (hk : 0 < k) (m : ℕ) {H s r s8 d w : ℕ} (eN : LNode H s ≃ Fin s8)
    (eI : Idx r s ≃ Fin w) (sw : Fin r → Fin k → ℕ)
    (p : Fin k × Fin s8 × Fin s8 × Fin d × (Fin w ⊕ Unit ⊕ Fin w)) : List (List (ℕ × Bool)) :=
  fr_coT eI (fr_mrW hk m p.1) (fr_mcW hk m p.1) (fun a => sw a p.1)
    ((eqs k p.1.val (eN.symm p.2.1).2.2.1 (eN.symm p.2.1).2.2.2 (eN.symm p.2.2.1).2.2.1
      (eN.symm p.2.2.1).2.2.2 : List (SEq r s)).getD p.2.2.2.1.val zeroEq) p.2.2.2.2

theorem fr_coTerms_lits {k : ℕ} (hk : 0 < k) (m : ℕ) {H s r s8 d w : ℕ} (eN : LNode H s ≃ Fin s8)
    (eI : Idx r s ≃ Fin w) (sw : Fin r → Fin k → ℕ) (B : ℕ) (hB : (m+2)*k ≤ B)
    (hsw : ∀ j t, sw j t < B)
    (p : Fin k × Fin s8 × Fin s8 × Fin d × (Fin w ⊕ Unit ⊕ Fin w)) :
    ∀ t ∈ fr_coTerms hk m eN eI sw p, ∀ l ∈ t, l.1 < B := by
  obtain ⟨t, i, j, e, z⟩ := p
  have ha := lt_of_lt_of_le (fr_mrW_lt hk m t) hB
  have hb := lt_of_lt_of_le (fr_mcW_lt hk m t) hB
  rcases z with l | u | l
  · exact fr_srcTerms_lits _ _ B _ ha hb (fun a => hsw a t) _
  · exact fr_srcTerms_lits _ _ B _ ha hb (fun a => hsw a t) _
  · exact fr_srcTerms_lits _ _ B _ ha hb (fun a => hsw a t) _

theorem fr_coTerms_cost {k : ℕ} (hk : 0 < k) (m : ℕ) {H s r s8 d w : ℕ} (eN : LNode H s ≃ Fin s8)
    (eI : Idx r s ≃ Fin w) (sw : Fin r → Fin k → ℕ)
    (p : Fin k × Fin s8 × Fin s8 × Fin d × (Fin w ⊕ Unit ⊕ Fin w)) :
    dnfCost (fr_coTerms hk m eN eI sw p) ≤ 7 := by
  obtain ⟨t, i, j, e, z⟩ := p
  rcases z with l | u | l
  · exact fr_srcTerms_cost _ _ _ _
  · exact fr_srcTerms_cost _ _ _ _
  · exact fr_srcTerms_cost _ _ _ _

theorem fr_coTerms_val {k : ℕ} (hk : 0 < k) (m : ℕ) {H s r s8 d w : ℕ} (eN : LNode H s ≃ Fin s8)
    (eI : Idx r s ≃ Fin w) (sw : Fin r → Fin k → ℕ) (marked : Bool → Fin k → Bool)
    (M : Fin r → Fin k → ZMod 2) (V : ℕ → Bool) (t : Fin k) (i j : Fin s8) (e : Fin d)
    (ha : V (fr_mrW hk m t) = marked false (ix hk (t.val+2*k-2)))
    (hb : V (fr_mcW hk m t) = marked true (ix hk (t.val+k-1)))
    (hs : ∀ a, V (sw a t) = decide (M a t ≠ 0)) :
    (∀ l : Fin w, dnfVal V (fr_coTerms hk m eN eI sw (t, i, j, e, Sum.inl l)) =
      decide ((eqS hk eN eI marked M t i j e).1 l ≠ 0)) ∧
    dnfVal V (fr_coTerms hk m eN eI sw (t, i, j, e, Sum.inr (Sum.inl ()))) =
      decide ((eqS hk eN eI marked M t i j e).2.1 ≠ 0) ∧
    (∀ l : Fin w, dnfVal V (fr_coTerms hk m eN eI sw (t, i, j, e, Sum.inr (Sum.inr l))) =
      decide ((eqS hk eN eI marked M t i j e).2.2 l ≠ 0)) := by
  refine ⟨fun l => ?_, ?_, fun l => ?_⟩
  · exact fr_srcTerms_val V _ _ _ _ _ (fun a => M a t) ha hb hs _
  · exact fr_srcTerms_val V _ _ _ _ _ (fun a => M a t) ha hb hs _
  · exact fr_srcTerms_val V _ _ _ _ _ (fun a => M a t) ha hb hs _

-- the block of copied wires
def fr_srcs (k s8 d w : ℕ) (stW : Fin s8 → ℕ) (edW : Fin k × Fin s8 × Fin s8 → ℕ)
    (coW : Fin k × Fin s8 × Fin s8 × Fin d × (Fin w ⊕ Unit ⊕ Fin w) → ℕ) : List ℕ :=
  List.ofFn stW ++ List.ofFn stW ++
    (List.finRange k).flatMap (fun t => (List.finRange s8).flatMap (fun i =>
      (List.finRange s8).flatMap (fun j => [edW (t, i, j)] ++
        (List.finRange d).flatMap (fun e =>
          List.ofFn (fun l => coW (t, i, j, e, Sum.inl l)) ++
            [coW (t, i, j, e, Sum.inr (Sum.inl ()))] ++
            List.ofFn (fun l => coW (t, i, j, e, Sum.inr (Sum.inr l)))))))

theorem fr_srcs_map (k s8 d w : ℕ) (stW : Fin s8 → ℕ) (edW : Fin k × Fin s8 × Fin s8 → ℕ)
    (coW : Fin k × Fin s8 × Fin s8 × Fin d × (Fin w ⊕ Unit ⊕ Fin w) → ℕ) (f : ℕ → Bool)
    (start : Fin s8 → Bool) (edge : Fin k → Fin s8 → Fin s8 → Bool)
    (equation : Fin k → Fin s8 → Fin s8 → Fin d → (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2))
    (h1 : ∀ i, f (stW i) = start i) (h2 : ∀ t i j, f (edW (t, i, j)) = edge t i j)
    (h3 : ∀ t i j e l, f (coW (t, i, j, e, Sum.inl l)) = decide ((equation t i j e).1 l ≠ 0))
    (h4 : ∀ t i j e, f (coW (t, i, j, e, Sum.inr (Sum.inl ()))) =
      decide ((equation t i j e).2.1 ≠ 0))
    (h5 : ∀ t i j e l, f (coW (t, i, j, e, Sum.inr (Sum.inr l))) =
      decide ((equation t i j e).2.2 l ≠ 0)) :
    (fr_srcs k s8 d w stW edW coW).map f = b_bits k s8 d w start start edge equation := by
  simp only [fr_srcs, b_bits, List.map_append, List.map_flatMap, List.map_ofFn, List.map_cons,
    List.map_nil, Function.comp_def, h1, h2, h3, h4, h5]

theorem fr_srcs_len (k s8 d w : ℕ) (stW : Fin s8 → ℕ) (edW : Fin k × Fin s8 × Fin s8 → ℕ)
    (coW : Fin k × Fin s8 × Fin s8 × Fin d × (Fin w ⊕ Unit ⊕ Fin w) → ℕ) :
    (fr_srcs k s8 d w stW edW coW).length = 2*s8 + k*s8*s8*(1+d*(2*w+1)) := by
  have h := fr_srcs_map k s8 d w stW edW coW (fun _ => false) (fun _ => false)
    (fun _ _ _ => false) (fun _ _ _ _ => (0, 0, 0)) (fun _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (fun _ _ _ _ _ => by simp)
  have h2 := congrArg List.length h
  rw [List.length_map, b_length] at h2
  exact h2

theorem fr_srcs_lt (k s8 d w : ℕ) (stW : Fin s8 → ℕ) (edW : Fin k × Fin s8 × Fin s8 → ℕ)
    (coW : Fin k × Fin s8 × Fin s8 × Fin d × (Fin w ⊕ Unit ⊕ Fin w) → ℕ) (B : ℕ)
    (h1 : ∀ i, stW i < B) (h2 : ∀ p, edW p < B) (h3 : ∀ p, coW p < B) :
    ∀ u ∈ fr_srcs k s8 d w stW edW coW, u < B := by
  intro u hu
  simp only [fr_srcs, List.mem_append, List.mem_flatMap, List.mem_ofFn,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_finRange, true_and] at hu
  rcases hu with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨t, i, j, rfl | ⟨e, (⟨l, rfl⟩ | rfl) | ⟨l, rfl⟩⟩⟩
  · exact h1 i
  · exact h1 i
  · exact h2 _
  · exact h3 _
  · exact h3 _
  · exact h3 _

theorem fr_tab {I : ℕ} (c : ℕ) (ι : Type) [Finite ι] (terms : ι → List (List (ℕ × Bool)))
    (gs : List Gate) (hG : Good I gs)
    (hw : ∀ i, ∀ t ∈ terms i, ∀ l ∈ t, l.1 < I + gs.length)
    (hc : ∀ i, dnfCost (terms i) ≤ c) :
    ∃ (gs2 : List Gate) (W : ι → ℕ), Extends gs gs2 ∧ gs2.length ≤ gs.length + Nat.card ι * c ∧
      Good I gs2 ∧ (∀ i, W i < I + gs2.length) ∧
      ∀ gs', Extends gs2 gs' → ∀ x : List Bool, x.length = I → ∀ i,
        wireAt gs' x (W i) = dnfVal (wireAt gs' x) (terms i) :=
  ⟨_, _, mkDnfTab_spec c ι terms gs hG hw hc⟩

theorem fr_card2 (k s8 : ℕ) : Nat.card (Fin k × Fin s8 × Fin s8) = k*s8*s8 := by
  simp [Nat.card_eq_fintype_card]
  ring

theorem fr_card3 (k s8 d w : ℕ) :
    Nat.card (Fin k × Fin s8 × Fin s8 × Fin d × (Fin w ⊕ Unit ⊕ Fin w)) =
      k*s8*s8*(d*(2*w+1)) := by
  simp [Nat.card_eq_fintype_card]
  ring

theorem front_circuit {k : ℕ} (hk : 0 < k) (m r H s s8 d w : ℕ)
    (eN : LNode H s ≃ Fin s8) (eI : Idx r s ≃ Fin w)
    (gs1 : List Gate) (hG : Good ((m+2)*k) gs1) (sw : Fin r → Fin k → ℕ)
    (hsw : ∀ j t, sw j t < (m+2)*k + gs1.length) :
    ∃ gs3 : List Gate, Extends gs1 gs3 ∧ Good ((m+2)*k) gs3 ∧
      gs3.length ≤ gs1.length + 8 * (2*s8 + k*s8*s8*(1+d*(2*w+1))) ∧
      ∀ (Q : Fin m → Fin k → ZMod 2) (marked : Bool → Fin k → Bool)
        (M : Fin r → Fin k → ZMod 2),
        (∀ j t, wireAt gs1
            ((List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten ++
              List.ofFn (marked false) ++ List.ofFn (marked true)) (sw j t) =
            decide (M j t ≠ 0)) →
        ∃ pre : List Bool,
          evalWires gs3
            ((List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten ++
              List.ofFn (marked false) ++ List.ofFn (marked true)) =
          pre ++ b_bits k s8 d w (stS eN) (stS eN) (edS hk eN marked)
            (eqS hk eN eI marked M) := by
  obtain ⟨gsA, stW, eA, lA, gA, wA, evA⟩ := fr_tab (I := (m+2)*k) 7 (Fin s8) (fr_stTerms eN) gs1 hG
    (fun i => fr_stTerms_lits eN _ i) (fun i => fr_stTerms_cost eN i)
  obtain ⟨gsB, edW, eB, lB, gB, wB, evB⟩ := fr_tab (I := (m+2)*k) 7 (Fin k × Fin s8 × Fin s8)
    (fr_edTerms hk m eN) gsA gA
    (fun p => fr_edTerms_lits hk m eN _ (Nat.le_add_right _ _) p)
    (fun p => fr_edTerms_cost hk m eN p)
  have hAB := extends_length_le eA
  have hBC := extends_length_le eB
  obtain ⟨gsC, coW, eC, lC, gC, wC, evC⟩ := fr_tab (I := (m+2)*k) 7
    (Fin k × Fin s8 × Fin s8 × Fin d × (Fin w ⊕ Unit ⊕ Fin w))
    (fr_coTerms hk m eN eI sw) gsB gB
    (fun p => fr_coTerms_lits hk m eN eI sw _ (Nat.le_add_right _ _)
      (fun j t => by have := hsw j t; omega) p)
    (fun p => fr_coTerms_cost hk m eN eI sw p)
  have hCD := extends_length_le eC
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at lA
  rw [fr_card2] at lB
  rw [fr_card3] at lC
  have hs : ∀ u ∈ fr_srcs k s8 d w stW edW coW, u < (m+2)*k + gsC.length :=
    fr_srcs_lt k s8 d w stW edW coW _ (fun i => by have := wA i; omega)
      (fun p => by have := wB p; omega) wC
  obtain ⟨gD, evD⟩ := copy_spec gsC gC (fr_srcs k s8 d w stW edW coW) hs
  refine ⟨gsC ++ copyGates (fr_srcs k s8 d w stW edW coW),
    extends_trans eA (extends_trans eB (extends_trans eC ⟨_, rfl⟩)), gD, ?_, ?_⟩
  · rw [List.length_append]
    unfold copyGates
    rw [List.length_map, fr_srcs_len]
    have e1 : k*s8*s8*(1+d*(2*w+1)) = k*s8*s8 + k*s8*s8*(d*(2*w+1)) := by ring
    omega
  · intro Q marked M hM
    obtain ⟨hx, hmr, hmc⟩ := fr_input
      (List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten (m*k)
      (fr_qlen m k (fun i c => decide (Q i c ≠ 0))) k (marked false) (marked true) false
    have hI : (m+2)*k = m*k + k + k := by ring
    rw [← hI] at hx
    generalize ((List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten ++
      List.ofFn (marked false) ++ List.ofFn (marked true)) = x at hM hx hmr hmc ⊢
    refine ⟨evalWires gsC x, ?_⟩
    rw [evD x hx]
    congr 1
    have e13 : Extends gs1 gsC := extends_trans eA (extends_trans eB eC)
    have ha : ∀ t : Fin k, wireAt gsC x (fr_mrW hk m t) = marked false (ix hk (t.val+2*k-2)) :=
      fun t => by
        rw [wireAt_input _ _ (by rw [hx]; exact fr_mrW_lt hk m t)]
        exact hmr _
    have hb : ∀ t : Fin k, wireAt gsC x (fr_mcW hk m t) = marked true (ix hk (t.val+k-1)) :=
      fun t => by
        rw [wireAt_input _ _ (by rw [hx]; exact fr_mcW_lt hk m t)]
        exact hmc _
    have hsv : ∀ (t : Fin k) (a : Fin r), wireAt gsC x (sw a t) = decide (M a t ≠ 0) :=
      fun t a => by
        rw [wireAt_extends e13 _ (by rw [hx]; exact hsw a t)]
        exact hM a t
    refine fr_srcs_map k s8 d w stW edW coW _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · intro i
      rw [evA gsC (extends_trans eB eC) _ hx i]
      exact fr_stTerms_val eN _ i
    · intro t i j
      rw [evB gsC eC _ hx (t, i, j)]
      exact fr_edTerms_val hk m eN marked _ t i j (ha t) (hb t)
    · intro t i j e l
      rw [evC gsC (extends_refl _) _ hx (t, i, j, e, Sum.inl l)]
      exact (fr_coTerms_val hk m eN eI sw marked M _ t i j e (ha t) (hb t) (hsv t)).1 l
    · intro t i j e
      rw [evC gsC (extends_refl _) _ hx (t, i, j, e, Sum.inr (Sum.inl ()))]
      exact (fr_coTerms_val hk m eN eI sw marked M _ t i j e (ha t) (hb t) (hsv t)).2.1
    · intro t i j e l
      rw [evC gsC (extends_refl _) _ hx (t, i, j, e, Sum.inr (Sum.inr l))]
      exact (fr_coTerms_val hk m eN eI sw marked M _ t i j e (ha t) (hb t) (hsv t)).2.2 l

end Front


section F2Post

open PEqualNP.CircuitLowerBounds

-- term tables of the three DNF stages

def po_okt (k : ℕ) (lastW : Fin k → ℕ) (_ : Unit) : List (List (ℕ × Bool)) :=
  [(List.finRange k).map (fun t => (lastW t, false))]

def po_outt (k : ℕ) (okW : ℕ) (tapW : Fin k → Fin k → ℕ) (p : Fin k × Fin k) :
    List (List (ℕ × Bool)) :=
  [[(okW, true), (tapW p.1 p.2, true)]]

def po_nzt (k : ℕ) (outT : Fin k × Fin k → ℕ) (i : Fin k) : List (List (ℕ × Bool)) :=
  (List.finRange k).map (fun j => [(outT (i, j), true)])

lemma po_okt_val (k : ℕ) (V : ℕ → Bool) (lastW : Fin k → ℕ) (u : Unit) :
    dnfVal V (po_okt k lastW u) = decide (∀ t, V (lastW t) = false) := by
  rw [Bool.eq_iff_iff]
  simp [dnfVal, po_okt, litVal]

lemma po_outt_val (k : ℕ) (V : ℕ → Bool) (okW : ℕ) (tapW : Fin k → Fin k → ℕ)
    (p : Fin k × Fin k) :
    dnfVal V (po_outt k okW tapW p) = (V okW && V (tapW p.1 p.2)) := by
  simp [dnfVal, po_outt, litVal]

lemma po_nzt_val (k : ℕ) (V : ℕ → Bool) (outT : Fin k × Fin k → ℕ) (i : Fin k) :
    dnfVal V (po_nzt k outT i) = true ↔ ∃ j, V (outT (i, j)) = true := by
  simp [dnfVal, po_nzt, litVal]

lemma po_okt_cost (k : ℕ) (lastW : Fin k → ℕ) (u : Unit) :
    dnfCost (po_okt k lastW u) ≤ 2 * k + 3 := by
  simp only [po_okt, dnfCost, List.length_map, List.length_finRange]
  omega

lemma po_outt_cost (k : ℕ) (okW : ℕ) (tapW : Fin k → Fin k → ℕ) (p : Fin k × Fin k) :
    dnfCost (po_outt k okW tapW p) ≤ 7 := by
  simp [po_outt, dnfCost]

lemma po_nzt_cost (k : ℕ) (outT : Fin k × Fin k → ℕ) (i : Fin k) :
    dnfCost (po_nzt k outT i) ≤ 1 + k * 4 := by
  have h := dnfCost_le 1 (po_nzt k outT i) (by
    intro t ht
    simp only [po_nzt, List.mem_map] at ht
    rcases ht with ⟨a, _, rfl⟩
    simp)
  simpa [po_nzt] using h

lemma po_arith (k : ℕ) :
    (2 * k + 3) + k * k * 7 + k * (1 + k * 4) + 40 * (k+2)^3 ≤ 60 * (k+2)^3 := by
  have h2 : (k+2)^3 = k * k * k + 6 * (k * k) + 12 * k + 8 := by ring
  have h3 : k * (1 + k * 4) = k + 4 * (k * k) := by ring
  have h5 : 0 ≤ k * k * k := Nat.zero_le _
  rw [h2, h3]
  omega

theorem post_circuit {I : ℕ} (k : ℕ) (gs4 : List Gate) (hG : Good I gs4)
    (lastW : Fin k → ℕ) (hl : ∀ t, lastW t < I + gs4.length)
    (tapW : Fin k → Fin k → ℕ) (ht : ∀ i j, tapW i j < I + gs4.length) :
    ∃ (gs5 : List Gate) (okW : ℕ) (outW : Fin k → Fin k → ℕ) (dW : Fin (Nat.log2 k + 1) → ℕ),
      Extends gs4 gs5 ∧ gs5.length ≤ gs4.length + 60 * (k+2)^3 ∧ Good I gs5 ∧
      okW < I + gs5.length ∧ (∀ i j, outW i j < I + gs5.length) ∧
      (∀ j, dW j < I + gs5.length) ∧
      ∀ x : List Bool, x.length = I →
        (wireAt gs5 x okW = decide (∀ t, wireAt gs4 x (lastW t) = false)) ∧
        (∀ i j, wireAt gs5 x (outW i j) = (wireAt gs5 x okW && wireAt gs4 x (tapW i j))) ∧
        (∀ j, wireAt gs5 x (dW j) =
          ((Finset.univ.filter (fun i : Fin k => ∃ j, wireAt gs5 x (outW i j) = true)).card).testBit j.val) := by
  -- stage 1: ok wire
  have s1 := mkDnfTab_spec (I := I) (2 * k + 3) Unit (po_okt k lastW) gs4 hG
    (by
      intro u t' ht' l' hl'
      simp only [po_okt, List.mem_singleton] at ht'
      subst ht'
      simp only [List.mem_map] at hl'
      rcases hl' with ⟨a, _, rfl⟩
      exact hl a)
    (fun u => po_okt_cost k lastW u)
  rcases h1 : mkDnfTab I Unit (po_okt k lastW) gs4 with ⟨gsa, okT⟩
  simp only [h1] at s1
  rcases s1 with ⟨e1, l1, g1, w1, ev1⟩
  have hl1 := extends_length_le e1
  have hcu : Nat.card Unit = 1 := by simp
  rw [hcu, one_mul] at l1
  -- stage 2: out table
  have s2 := mkDnfTab_spec (I := I) 7 (Fin k × Fin k) (po_outt k (okT ()) tapW) gsa g1
    (by
      intro p t' ht' l' hl'
      simp only [po_outt, List.mem_singleton] at ht'
      subst ht'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
      rcases hl' with rfl | rfl
      · exact w1 ()
      · have h := ht p.1 p.2
        show tapW p.1 p.2 < I + gsa.length
        omega)
    (fun p => po_outt_cost k _ tapW p)
  rcases h2 : mkDnfTab I (Fin k × Fin k) (po_outt k (okT ()) tapW) gsa with ⟨gsb, outT⟩
  simp only [h2] at s2
  rcases s2 with ⟨e2, l2, g2, w2, ev2⟩
  have hl2 := extends_length_le e2
  have hc2 : Nat.card (Fin k × Fin k) = k * k := by simp [Nat.card_eq_fintype_card]
  rw [hc2] at l2
  -- stage 3: nonzero-row table
  have s3 := mkDnfTab_spec (I := I) (1 + k * 4) (Fin k) (po_nzt k outT) gsb g2
    (by
      intro i t' ht' l' hl'
      simp only [po_nzt, List.mem_map] at ht'
      rcases ht' with ⟨j, _, rfl⟩
      simp only [List.mem_singleton] at hl'
      subst hl'
      exact w2 (i, j))
    (fun i => po_nzt_cost k outT i)
  rcases h3 : mkDnfTab I (Fin k) (po_nzt k outT) gsb with ⟨gsc, nzT⟩
  simp only [h3] at s3
  rcases s3 with ⟨e3, l3, g3, w3, ev3⟩
  have hl3 := extends_length_le e3
  rw [Nat.card_fin] at l3
  -- stage 4: counter
  obtain ⟨gs5, dW, e4, l4, g4, w4, ev4⟩ := count_circuit k gsc g3 nzT w3
  have hl4 := extends_length_le e4
  have e34 := extends_trans e3 e4
  have e24 := extends_trans e2 e34
  have e14 := extends_trans e1 e24
  refine ⟨gs5, okT (), fun i j => outT (i, j), dW, e14, ?_, g4, ?_, ?_, w4, ?_⟩
  · have ha := po_arith k
    omega
  · have h := w1 ()
    omega
  · intro i j
    have h := w2 (i, j)
    show outT (i, j) < I + gs5.length
    omega
  · intro x hx
    have hok : wireAt gs5 x (okT ()) = decide (∀ t, wireAt gs4 x (lastW t) = false) := by
      rw [ev1 gs5 e24 x hx (), po_okt_val]
      exact decide_eq_decide.mpr
        (forall_congr' (fun t => by rw [wire_ext e14 x hx (hl t)]))
    have hout : ∀ i j, wireAt gs5 x (outT (i, j)) =
        (wireAt gs5 x (okT ()) && wireAt gs4 x (tapW i j)) := by
      intro i j
      rw [ev2 gs5 e34 x hx (i, j), po_outt_val]
      show (wireAt gs5 x (okT ()) && wireAt gs5 x (tapW i j)) = _
      rw [wire_ext e14 x hx (ht i j)]
    refine ⟨hok, hout, fun j => ?_⟩
    rw [ev4 gs5 (extends_refl gs5) x hx j]
    have hf : (Finset.univ.filter (fun i : Fin k => wireAt gs5 x (nzT i) = true)) =
        (Finset.univ.filter (fun i : Fin k => ∃ j, wireAt gs5 x (outT (i, j)) = true)) := by
      apply Finset.filter_congr
      intro i _
      rw [ev3 gs5 e4 x hx i]
      exact po_nzt_val k _ outT i
    rw [hf]

end F2Post


-- ---------------------------------------------------------------------------
-- small helpers
-- ---------------------------------------------------------------------------

theorem zs_lt_two_pow (n : ℕ) : n < 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem zs_mono {N X a a' b b' : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) (ha : a ≤ a') (hb : b ≤ b') :
    N^a * X^b ≤ N^a' * X^b' :=
  Nat.mul_le_mul (Nat.pow_le_pow_right hN ha) (Nat.pow_le_pow_right hX hb)

theorem zs_four (A : ℕ) (hA : 1 ≤ A) :
    ((A+1)*(A+1)) * ((A+1)*(A+1)) ≤ 16 * A^4 := by
  have h : A + 1 ≤ 2*A := by omega
  calc ((A+1)*(A+1)) * ((A+1)*(A+1)) ≤ ((2*A)*(2*A)) * ((2*A)*(2*A)) := by gcongr
    _ = 16 * A^4 := by ring

-- ---------------------------------------------------------------------------
-- TARGET 1
-- ---------------------------------------------------------------------------

theorem card_Idx (r s : ℕ) : Nat.card (Idx r s) = r + s + 10 := by
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

-- ---------------------------------------------------------------------------
-- TARGET 2
-- ---------------------------------------------------------------------------

theorem zs_card_LNode_eq (H s : ℕ) :
    Fintype.card (LNode H s) =
      ((2^s)^s)^H * (((2^s+1)*(2^s+1)) * ((2^s+1)*(2^s+1))) := by
  simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

theorem card_LNode (H : ℕ) : 0 < Nat.card (LNode H (2*H)) ∧ Nat.card (LNode H (2*H)) ≤ 2^(4*H^3 + 8*H + 4) := by
  rw [Nat.card_eq_fintype_card, zs_card_LNode_eq]
  constructor
  · positivity
  · have hA : 1 ≤ 2^(2*H) := Nat.one_le_two_pow
    calc ((2^(2*H))^(2*H))^H * (((2^(2*H)+1)*(2^(2*H)+1)) * ((2^(2*H)+1)*(2^(2*H)+1)))
        ≤ ((2^(2*H))^(2*H))^H * (16 * (2^(2*H))^4) := Nat.mul_le_mul_left _ (zs_four _ hA)
      _ = 2^(4*H^3 + 8*H + 4) := by
        have e16 : (16:ℕ) = 2^4 := by norm_num
        rw [← pow_mul, ← pow_mul, ← pow_mul, e16, ← pow_add, ← pow_add]
        congr 1
        ring

-- ---------------------------------------------------------------------------
-- TARGET 3
-- ---------------------------------------------------------------------------

theorem zs_core (X N k m B s8 d w E P Q A8 L1 L3 L5 : ℕ)
    (hX : 60 ≤ X) (hk : k ≤ N) (hm1 : m + 1 ≤ N) (hk1 : k + 1 ≤ N) (hk2 : k + 2 ≤ N)
    (hs : s8 ≤ X^4) (hE : E ≤ X^3) (hdw : d + w + 6 ≤ X) (hQ : Q ≤ X)
    (hB2 : B + 2 ≤ X) (hP : P ≤ X)
    (h1 : L1 ≤ 40 * (m+1) * (k+1) * (B+2) * P)
    (h3 : L3 ≤ L1 + 8 * (2*s8 + k*s8*s8*Q))
    (hA : A8 ≤ E*(k+s8+d+w+6)^12)
    (h5 : L5 ≤ L3 + A8 + 60 * (k+2)^3) :
    L5 ≤ N^16 * X^64 := by
  have hN1 : 1 ≤ N := by omega
  have hX1 : 1 ≤ X := by omega
  have h40 : 40 ≤ X := by omega
  have b1 : L1 ≤ N^16 * X^63 := by
    calc L1 ≤ 40 * (m+1) * (k+1) * (B+2) * P := h1
      _ ≤ X * N * N * X * X := by gcongr
      _ = N^2 * X^3 := by ring
      _ ≤ N^16 * X^63 := zs_mono hN1 hX1 (by norm_num) (by norm_num)
  have b2 : 8 * (2*s8 + k*s8*s8*Q) ≤ N^16 * X^63 := by
    have c1 : 2 * s8 ≤ N^1 * X^9 := by
      calc 2 * s8 ≤ X * X^4 := Nat.mul_le_mul (by omega) hs
        _ = 1 * X^5 := by ring
        _ ≤ N^1 * X^9 :=
          Nat.mul_le_mul (le_of_le_of_eq hN1 (pow_one N).symm)
            (Nat.pow_le_pow_right hX1 (by norm_num))
    have c2 : k*s8*s8*Q ≤ N^1 * X^9 := by
      calc k*s8*s8*Q ≤ N * X^4 * X^4 * X := by gcongr
        _ = N^1 * X^9 := by ring
    calc 8 * (2*s8 + k*s8*s8*Q) ≤ 8 * (N^1 * X^9 + N^1 * X^9) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add c1 c2)
      _ = 16 * (N^1 * X^9) := by ring
      _ ≤ X * (N^1 * X^9) := Nat.mul_le_mul_right _ (by omega)
      _ = N^1 * X^10 := by ring
      _ ≤ N^16 * X^63 := zs_mono hN1 hX1 (by norm_num) (by norm_num)
  have b3 : A8 ≤ N^16 * X^63 := by
    have c1 : k + s8 + d + w + 6 ≤ N * X^5 := by
      have e1 : k ≤ N * X^4 := by
        calc k ≤ N * 1 := by omega
          _ ≤ N * X^4 := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hX1)
      have e2 : s8 ≤ N * X^4 := by
        calc s8 ≤ 1 * X^4 := by omega
          _ ≤ N * X^4 := Nat.mul_le_mul_right _ hN1
      have e3 : d + w + 6 ≤ N * X^4 := by
        calc d + w + 6 ≤ X := hdw
          _ = 1 * X^1 := by ring
          _ ≤ N * X^4 := Nat.mul_le_mul hN1 (Nat.pow_le_pow_right hX1 (by norm_num))
      calc k + s8 + d + w + 6 ≤ 3 * (N * X^4) := by omega
        _ ≤ X * (N * X^4) := Nat.mul_le_mul_right _ (by omega)
        _ = N * X^5 := by ring
    calc A8 ≤ E*(k+s8+d+w+6)^12 := hA
      _ ≤ X^3 * (N * X^5)^12 := Nat.mul_le_mul hE (Nat.pow_le_pow_left c1 12)
      _ = N^12 * X^63 := by ring
      _ ≤ N^16 * X^63 := zs_mono hN1 hX1 (by norm_num) (by norm_num)
  have b4 : 60 * (k+2)^3 ≤ N^16 * X^63 := by
    calc 60 * (k+2)^3 ≤ X * N^3 := Nat.mul_le_mul hX (Nat.pow_le_pow_left hk2 3)
      _ = N^3 * X^1 := by ring
      _ ≤ N^16 * X^63 := zs_mono hN1 hX1 (by norm_num) (by norm_num)
  calc L5 ≤ L3 + A8 + 60 * (k+2)^3 := h5
    _ ≤ (L1 + 8 * (2*s8 + k*s8*s8*Q)) + A8 + 60 * (k+2)^3 :=
        Nat.add_le_add_right (Nat.add_le_add_right h3 _) _
    _ ≤ N^16 * X^63 + N^16 * X^63 + N^16 * X^63 + N^16 * X^63 :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add b1 b2) b3) b4
    _ = 4 * (N^16 * X^63) := by ring
    _ ≤ X * (N^16 * X^63) := Nat.mul_le_mul_right _ (by omega)
    _ = N^16 * X^64 := by ring

theorem size_arith (k m B H s8 w d A8 L1 L3 L5 : ℕ) (hk : 0 < k)
    (hs8 : s8 ≤ 2^(4*H^3 + 8*H + 4)) (hw : w = B + 2*H + 11) (hd : d = 3*B + 2*H + 27)
    (h1 : L1 ≤ 40 * (m+1) * (k+1) * (B+2) * 2^(B+1))
    (h3 : L3 ≤ L1 + 8 * (2*s8 + k*s8*s8*(1+d*(2*w+1))))
    (hA : A8 ≤ 2^(12*(w+2)^2)*(k+s8+d+w+6)^12)
    (h5 : L5 ≤ L3 + A8 + 60 * (k+2)^3) :
    L5 ≤ 2^(128*(B+H+20)^3)*(k+m+5)^16 := by
  obtain ⟨T, hT⟩ : ∃ T, T = B + H + 20 := ⟨_, rfl⟩
  rw [← hT]
  have hT20 : 20 ≤ T := by omega
  have t1 : 400 * T ≤ T^3 := by
    calc 400 * T = 20 * 20 * T := by ring
      _ ≤ T * T * T := by gcongr
      _ = T^3 := by ring
  have t2 : 20 * (T * T) ≤ T^3 := by
    calc 20 * (T * T) ≤ T * (T * T) := Nat.mul_le_mul_right _ hT20
      _ = T^3 := by ring
  have t3 : 8000 ≤ T^3 := by
    calc 8000 = 20^3 := by norm_num
      _ ≤ T^3 := Nat.pow_le_pow_left hT20 3
  have t4 : (H+20)^3 ≤ T^3 := Nat.pow_le_pow_left (by omega) 3
  obtain ⟨Y, hY⟩ : ∃ Y, Y = T^3 := ⟨_, rfl⟩
  rw [← hY] at t1 t2 t3 t4 ⊢
  have hYX : Y < 2^Y := zs_lt_two_pow Y
  obtain ⟨X, hXd⟩ : ∃ X, X = 2^Y := ⟨_, rfl⟩
  rw [← hXd] at hYX
  have hX60 : 60 ≤ X := by omega
  have hs : s8 ≤ X^4 := by
    rw [hXd, ← pow_mul]
    refine le_trans hs8 (Nat.pow_le_pow_right (by norm_num) ?_)
    have e : (H+20)^3 = H^3 + 60*H^2 + 1200*H + 8000 := by ring
    rw [e] at t4
    omega
  have hE : 2^(12*(w+2)^2) ≤ X^3 := by
    rw [hXd, ← pow_mul]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have w2 : w + 2 ≤ 2*T := by omega
    have e2 : (w+2)^2 ≤ (2*T)^2 := Nat.pow_le_pow_left w2 2
    have e3 : (2*T)^2 = 4*(T*T) := by ring
    rw [e3] at e2
    omega
  have hdw : d + w + 6 ≤ X := by omega
  have hQ : 1 + d*(2*w+1) ≤ X := by
    have d3 : d ≤ 3*T := by omega
    have w4 : 2*w+1 ≤ 4*T := by omega
    have e2 : d*(2*w+1) ≤ (3*T)*(4*T) := Nat.mul_le_mul d3 w4
    have e3 : (3*T)*(4*T) = 12*(T*T) := by ring
    rw [e3] at e2
    omega
  have hB2 : B + 2 ≤ X := by omega
  have hP : 2^(B+1) ≤ X := by
    rw [hXd]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have core := zs_core X (k+m+5) k m B s8 d w (2^(12*(w+2)^2)) (2^(B+1)) (1+d*(2*w+1))
    A8 L1 L3 L5 hX60 (by omega) (by omega) (by omega) (by omega) hs hE hdw hQ hB2 hP
    h1 h3 hA h5
  calc L5 ≤ (k+m+5)^16 * X^64 := core
    _ ≤ (k+m+5)^16 * X^128 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))
    _ = 2^(128*Y) * (k+m+5)^16 := by
        rw [hXd, ← pow_mul, Nat.mul_comm Y 128, Nat.mul_comm]


section Final

open PEqualNP.CircuitLowerBounds

def out8 {n : ℕ} (A : Circuit) (bits : List Bool) (bw : Fin n → Fin n → ℕ) :
    Fin n → Fin n → ZMod 2 :=
  fun i j => if (A.wires bits).getD (bw i j) false = true then 1 else 0

theorem lib807' (n s d w : ℕ) (hn : 0 < n) (hs : 0 < s) :
    ∃ (A : Circuit) (bw : Fin n → Fin n → ℕ),
      PEqualNP.MetaComplexity.FanInTwo A ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*s + n*s*s*(1+d*(2*w+1))) A ∧
      (∀ i j, bw i j < 2*s + n*s*s*(1+d*(2*w+1)) + A.size) ∧
      A.size ≤ 2^(12*(w+2)^2)*(n+s+d+w+6)^12 ∧
      ∀ (start stop : Fin s → Bool) (edge : Fin n → Fin s → Fin s → Bool)
        (equation : Fin n → Fin s → Fin s → Fin d →
          (Fin w → ZMod 2) × ZMod 2 × (Fin w → ZMod 2)),
        (∃ p, Legal807 start stop edge p) →
        ∃ p, Legal807 start stop edge p ∧
          (∀ x : Fin n → ZMod 2,
            x ∈ Submodule.span (ZMod 2)
              (Set.range (out8 A (b_bits n s d w start stop edge equation) bw)) ↔
            Poss807 equation p x) ∧
          LinearIndependent (ZMod 2)
            (fun i : ↥((Finset.univ : Finset (Fin n)).filter
              (fun i => out8 A (b_bits n s d w start stop edge equation) bw i ≠ 0)) =>
              out8 A (b_bits n s d w start stop edge equation) bw i.val) ∧
          (∀ q, Legal807 start stop edge q →
            Nat.card {x : Fin n → ZMod 2 // Poss807 equation q x} ≤
              2^(Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
                (Set.range (out8 A (b_bits n s d w start stop edge equation) bw))))) := by
  obtain ⟨A, ok, walk, bw, h1, h2, h3, h4, h5⟩ := lib807 n s d w hn hs
  refine ⟨A, fun i j => (bw i j).val, h1, h2, fun i j => (bw i j).isLt, h4, ?_⟩
  intro start stop edge equation hex
  obtain ⟨ha, hb, hc⟩ := h5 start stop edge equation
  obtain ⟨p, hp, _, hK, hLI, hmax⟩ := hb (ha.mpr hex)
  exact ⟨p, hp, hK, hLI, hmax⟩

theorem finrank_span_nz {k n : ℕ} (out : Fin n → Fin k → ZMod 2)
    (hli : LinearIndependent (ZMod 2)
      (fun i : ↥((Finset.univ : Finset (Fin n)).filter (fun i => out i ≠ 0)) => out i.val)) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range out)) =
      ((Finset.univ : Finset (Fin n)).filter (fun i => out i ≠ 0)).card := by
  have hspan : Submodule.span (ZMod 2) (Set.range out) =
      Submodule.span (ZMod 2) (Set.range
        (fun i : ↥((Finset.univ : Finset (Fin n)).filter (fun i => out i ≠ 0)) => out i.val)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases hi : out i = 0
      · rw [hi]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨i, by simp [hi]⟩, rfl⟩
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i.val, rfl⟩
  rw [hspan, finrank_span_eq_card hli, Fintype.card_coe]

def xb {k m : ℕ} (Q : Fin m → Fin k → ZMod 2) (marked : Bool → Fin k → Bool) : List Bool :=
  (List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten ++
    List.ofFn (marked false) ++ List.ofFn (marked true)

def outF {k : ℕ} (gs : List Gate) (x : List Bool) (outW : Fin k → Fin k → ℕ) :
    Fin k → Fin k → ZMod 2 :=
  fun i j => if wireAt gs x (outW i j) = true then 1 else 0

theorem xb_length {k m : ℕ} (Q : Fin m → Fin k → ZMod 2) (marked : Bool → Fin k → Bool) :
    (xb Q marked).length = (m+2)*k := by
  have h : ((List.ofFn (fun i => List.ofFn (fun c : Fin k => decide (Q i c ≠ 0)))).flatten).length
      = m*k := by
    rw [List.ofFn_eq_map, ← List.flatMap_def]
    exact b_flat_len m k _ (fun i => by simp)
  unfold xb
  rw [List.length_append, List.length_append, h, List.length_ofFn, List.length_ofFn]
  ring

theorem outF_ne_zero_iff {k : ℕ} (gs : List Gate) (x : List Bool) (outW : Fin k → Fin k → ℕ)
    (i : Fin k) : outF gs x outW i ≠ 0 ↔ ∃ j, wireAt gs x (outW i j) = true := by
  constructor
  · intro hne
    by_contra hcon
    apply hne
    funext j
    have : ¬ wireAt gs x (outW i j) = true := fun hj => hcon ⟨j, hj⟩
    simp [outF, this]
  · rintro ⟨j, hj⟩ h0
    have := congrFun h0 j
    simp [outF, hj] at this

theorem core (k m b h : ℕ) (hk : 0 < k) :
    ∃ (gs : List Gate) (okW : ℕ) (outW : Fin k → Fin k → ℕ) (dW : Fin (Nat.log2 k + 1) → ℕ),
      Good ((m+2)*k) gs ∧ okW < (m+2)*k + gs.length ∧
      (∀ i j, outW i j < (m+2)*k + gs.length) ∧ (∀ j, dW j < (m+2)*k + gs.length) ∧
      gs.length ≤ 2^(128*(min b k + min h (2*k) + 20)^3)*(k+m+5)^16 ∧
      ∀ (Q : Fin m → Fin k → ZMod 2) (marked : Bool → Fin k → Bool),
        (wireAt gs (xb Q marked) okW = true ↔
          Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Q)) ≤ b) ∧
        (wireAt gs (xb Q marked) okW = true →
          Adm hk m h Q marked
            (Submodule.span (ZMod 2) (Set.range (outF gs (xb Q marked) outW))) ∧
          (∀ U : Submodule (ZMod 2) (Fin k → ZMod 2), Adm hk m h Q marked U →
            Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2)
              (Submodule.span (ZMod 2) (Set.range (outF gs (xb Q marked) outW)))) ∧
          LinearIndependent (ZMod 2)
            (fun i : ↥((Finset.univ : Finset (Fin k)).filter
              (fun i => outF gs (xb Q marked) outW i ≠ 0)) =>
              outF gs (xb Q marked) outW i.val)) ∧
        (wireAt gs (xb Q marked) okW = false → ∀ i, outF gs (xb Q marked) outW i = 0) ∧
        (∀ j : Fin (Nat.log2 k + 1), wireAt gs (xb Q marked) (dW j) =
          (Module.finrank (ZMod 2)
            (Submodule.span (ZMod 2) (Set.range (outF gs (xb Q marked) outW)))).testBit j.val) := by
  obtain ⟨gs1, sw, hG1, hL1, hsw, hsem1⟩ := elim_circuit k m (min b k)
  obtain ⟨hs8pos, hs8le⟩ := card_LNode (min h (2*k))
  obtain ⟨s8, hs8⟩ : ∃ s8 : ℕ, Nat.card (LNode (min h (2*k)) (2 * min h (2*k))) = s8 := ⟨_, rfl⟩
  obtain ⟨eN⟩ : Nonempty (LNode (min h (2*k)) (2 * min h (2*k)) ≃ Fin s8) :=
    ⟨hs8 ▸ Finite.equivFin _⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ, Nat.card (Idx (min b k + 1) (2 * min h (2*k))) = w := ⟨_, rfl⟩
  obtain ⟨eI⟩ : Nonempty (Idx (min b k + 1) (2 * min h (2*k)) ≃ Fin w) :=
    ⟨hw ▸ Finite.equivFin _⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = 3*(min b k + 1) + 2 * min h (2*k) + 24 := ⟨_, rfl⟩
  rw [hs8] at hs8pos hs8le
  rw [card_Idx] at hw
  obtain ⟨gs3, hE13, hG3, hL3, hsem3⟩ := front_circuit hk m (min b k + 1) (min h (2*k))
    (2 * min h (2*k)) s8 d w eN eI gs1 hG1 sw hsw
  obtain ⟨A8, bw8, hF8, hR8, hbw8, hsz8, hspec8⟩ := lib807' k s8 d w hk hs8pos
  have hsw1 : ∀ (Q : Fin m → Fin k → ZMod 2) (marked : Bool → Fin k → Bool) j t,
      wireAt gs1 (xb Q marked) (sw j t) =
        decide ((elim Q : Fin (min b k + 1) → Fin k → ZMod 2) j t ≠ 0) := by
    intro Q marked j t
    have := hsem1 gs1 (extends_refl _) Q (List.ofFn (marked false) ++ List.ofFn (marked true))
      (by simp; ring) j t
    rw [← List.append_assoc] at this
    exact this
  have hpreAll : ∀ (Q : Fin m → Fin k → ZMod 2) (marked : Bool → Fin k → Bool),
      ∃ pre : List Bool, evalWires gs3 (xb Q marked) =
        pre ++ b_bits k s8 d w (stS eN) (stS eN) (edS hk eN marked)
          (eqS hk eN eI marked (elim Q)) ∧
        pre.length + (2*s8 + k*s8*s8*(1+d*(2*w+1))) = (m+2)*k + gs3.length := by
    intro Q marked
    obtain ⟨pre, hpre⟩ := hsem3 Q marked (elim Q) (hsw1 Q marked)
    refine ⟨pre, hpre, ?_⟩
    have h2 : (evalWires gs3 (xb Q marked)).length = _ := congrArg List.length hpre
    rw [List.length_append, b_length, evalWires_length, xb_length] at h2
    omega
  have hN8 : 2*s8 + k*s8*s8*(1+d*(2*w+1)) ≤ (m+2)*k + gs3.length := by
    obtain ⟨pre, -, hlen⟩ := hpreAll (fun _ _ => 0) (fun _ _ => false)
    omega
  obtain ⟨hG4, hev4⟩ := shift_spec gs3 hG3 A8 hF8 hR8 hN8
  have hlen4 : (gs3 ++ shiftGates ((m+2)*k + gs3.length - (2*s8 + k*s8*s8*(1+d*(2*w+1))))
      A8.gates).length = gs3.length + A8.size := by
    simp [shiftGates, Circuit.size]
  have hlen13 := extends_length_le hE13
  obtain ⟨gs5, okW, outW, dW, hE45, hL5, hG5, hok, hout, hdw, hsem5⟩ :=
    post_circuit k _ hG4 (fun t => sw (Fin.last (min b k)) t)
      (fun t => by have := hsw (Fin.last (min b k)) t; rw [hlen4]; omega)
      (fun i j => (m+2)*k + gs3.length - (2*s8 + k*s8*s8*(1+d*(2*w+1))) + bw8 i j)
      (fun i j => by have := hbw8 i j; rw [hlen4]; omega)
  refine ⟨gs5, okW, outW, dW, hG5, hok, hout, hdw, ?_, ?_⟩
  · refine size_arith k m (min b k) (min h (2*k)) s8 w d A8.size gs1.length gs3.length gs5.length
      hk hs8le (by omega) (by omega) hL1 hL3 hsz8 ?_
    rw [hlen4] at hL5
    omega
  · intro Q marked
    have hx : (xb Q marked).length = (m+2)*k := xb_length Q marked
    obtain ⟨pre, hpre, hprelen⟩ := hpreAll Q marked
    have hb8 := b_length k s8 d w (stS eN) (stS eN) (edS hk eN marked)
      (eqS hk eN eI marked (elim Q) (d := d))
    have hev := hev4 (xb Q marked) hx pre _ hpre hb8
    obtain ⟨hokv, houtv, hdv⟩ := hsem5 (xb Q marked) hx
    have htap : ∀ i j, wireAt (gs3 ++ shiftGates ((m+2)*k + gs3.length -
          (2*s8 + k*s8*s8*(1+d*(2*w+1)))) A8.gates) (xb Q marked)
          ((m+2)*k + gs3.length - (2*s8 + k*s8*s8*(1+d*(2*w+1))) + bw8 i j) =
        (A8.wires (b_bits k s8 d w (stS eN) (stS eN) (edS hk eN marked)
          (eqS hk eN eI marked (elim Q)))).getD (bw8 i j) false :=
      fun i j => shift_wire gs3 A8 (xb Q marked) pre _ hev (by omega) (bw8 i j)
    have hlast : ∀ t, wireAt (gs3 ++ shiftGates ((m+2)*k + gs3.length -
          (2*s8 + k*s8*s8*(1+d*(2*w+1)))) A8.gates) (xb Q marked)
          (sw (Fin.last (min b k)) t) =
        decide ((elim Q : Fin (min b k + 1) → Fin k → ZMod 2) (Fin.last (min b k)) t ≠ 0) := by
      intro t
      rw [wire_ext (extends_trans hE13 ⟨_, rfl⟩) (xb Q marked) hx (hsw _ t)]
      exact hsw1 Q marked _ t
    have hokiff : wireAt gs5 (xb Q marked) okW = true ↔
        (elim Q : Fin (min b k + 1) → Fin k → ZMod 2) (Fin.last (min b k)) = 0 := by
      rw [hokv, decide_eq_true_iff]
      constructor
      · intro hall
        funext t
        have := hall t
        rw [hlast t] at this
        simpa using this
      · intro h0 t
        rw [hlast t, h0]
        simp
    obtain ⟨hE1, hE2⟩ := elim_spec (r := min b k) Q
    have hrank : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Q)) ≤ min b k ↔
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Q)) ≤ b := by
      have hle : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Q)) ≤ k := by
        have := Submodule.finrank_le (Submodule.span (ZMod 2) (Set.range Q))
        simpa using this
      omega
    have hout_ok : wireAt gs5 (xb Q marked) okW = true →
        outF gs5 (xb Q marked) outW = out8 A8 (b_bits k s8 d w (stS eN) (stS eN)
          (edS hk eN marked) (eqS hk eN eI marked (elim Q))) bw8 := by
      intro hokt
      funext i j
      unfold outF out8
      rw [houtv i j, hokt, htap i j]
      simp
    have hout_no : wireAt gs5 (xb Q marked) okW = false →
        ∀ i, outF gs5 (xb Q marked) outW i = 0 := by
      intro hokf i
      funext j
      unfold outF
      rw [houtv i j, hokf]
      simp
    have hmain : wireAt gs5 (xb Q marked) okW = true →
        Adm hk m h Q marked
          (Submodule.span (ZMod 2) (Set.range (outF gs5 (xb Q marked) outW))) ∧
        (∀ U : Submodule (ZMod 2) (Fin k → ZMod 2), Adm hk m h Q marked U →
          Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2)
            (Submodule.span (ZMod 2) (Set.range (outF gs5 (xb Q marked) outW)))) ∧
        LinearIndependent (ZMod 2)
          (fun i : ↥((Finset.univ : Finset (Fin k)).filter
            (fun i => outF gs5 (xb Q marked) outW i ≠ 0)) =>
            outF gs5 (xb Q marked) outW i.val) := by
      intro hokt
      have h0 := hokiff.mp hokt
      obtain ⟨hex, hall⟩ := sem_core hk m h (min b k + 1) s8 d w Q marked (elim Q) (hE2 h0)
        eN eI (by omega)
      obtain ⟨p, hp, hK8, hLI8, hmax8⟩ := hspec8 (stS eN) (stS eN) (edS hk eN marked)
        (eqS hk eN eI marked (elim Q)) hex
      obtain ⟨hadm, hmaxU⟩ := hall p hp _ hK8 hmax8
      rw [hout_ok hokt]
      exact ⟨hadm, hmaxU, hLI8⟩
    have hLI : LinearIndependent (ZMod 2)
        (fun i : ↥((Finset.univ : Finset (Fin k)).filter
          (fun i => outF gs5 (xb Q marked) outW i ≠ 0)) =>
          outF gs5 (xb Q marked) outW i.val) := by
      cases hc : wireAt gs5 (xb Q marked) okW with
      | true => exact (hmain hc).2.2
      | false =>
        have hz := hout_no hc
        have hemp : IsEmpty ↥((Finset.univ : Finset (Fin k)).filter
            (fun i => outF gs5 (xb Q marked) outW i ≠ 0)) :=
          ⟨fun i => (Finset.mem_filter.mp i.property).2 (hz i.val)⟩
        exact linearIndependent_empty_type
    refine ⟨hokiff.trans (hE1.trans hrank), hmain, hout_no, ?_⟩
    intro j
    rw [hdv j, finrank_span_nz _ hLI]
    congr 2
    apply Finset.filter_congr
    intro i _
    exact (outF_ne_zero_iff gs5 (xb Q marked) outW i).symm

end Final


end PEqualNP.Outside.L_meta_29723

theorem PEqualNP.Outside.L_meta_29723 : ∀ (k m b h : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun s : Nat => (⟨s % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (w : W) (j : Fin k) => w (ix (j.val+k-s % k))
  let run := fun (col : Bool) (name c key : W) (j : Fin k) =>
    let d := if col then 2 else 1
    let z := rot (if col then 3 else 1) key + name
    let y := fun i : Fin k => z i + z (ix (i.val+d)) + z (ix (i.val+k-d % k))
    y j + (1+y (ix (j.val+1)))*y (ix (j.val+2)) +
      rot (if col then 4 else 0) key j + c j
  let inputs := (m+2)*k
  let bitsN := Nat.log2 k + 1
  let H := min h (2*k)
  let B := min b k
  ∃ (A : PEqualNP.CircuitLowerBounds.Circuit) (ok : Fin (inputs+A.size))
    (rowWire : Fin k → Fin k → Fin (inputs+A.size))
    (dimWire : Fin bitsN → Fin (inputs+A.size)),
    PEqualNP.MetaComplexity.FanInTwo A ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs A ∧
    A.output = ok.val ∧
    A.size ≤ 2^(128*(B+H+20)^3)*(k+m+5)^16 ∧
    ∀ (Q : Fin m → W) (marked : Bool → Fin k → Bool),
      let pack := fun w : W => List.ofFn (fun j : Fin k => decide (w j ≠ 0))
      let bits := (List.ofFn (fun i => pack (Q i))).flatten ++
        List.ofFn (marked false) ++ List.ofFn (marked true)
      let wire := fun i : Fin (inputs+A.size) => (A.wires bits).getD i.val false
      let out := fun i j => (if wire (rowWire i j) then 1 else 0 : F)
      let K := Submodule.span F (Set.range out)
      let nz := (Finset.univ : Finset (Fin k)).filter (fun i => out i ≠ 0)
      let dim := Module.finrank F K
      let obs := {u : Bool × Fin k // marked u.1 u.2 = true}
      let admissible := fun (U : Submodule F W) =>
        (∀ x ∈ U, ∀ i : Fin m, dotProduct (Q i) x = 0) ∧
        (∀ (name c : Bool → W) (a : W),
          let polar := fun (u : obs) (xy : U × U) =>
            let probe := run u.val.1 (name u.val.1) (c u.val.1)
            probe a u.val.2 + probe (a+xy.1.val) u.val.2 +
              probe (a+xy.2.val) u.val.2 + probe (a+xy.1.val+xy.2.val) u.val.2
          Module.finrank F (Submodule.span F (Set.range polar)) ≤ h)
      (wire ok = true ↔ Module.finrank F (Submodule.span F (Set.range Q)) ≤ b) ∧
      (wire ok = true →
        admissible K ∧ (∀ U : Submodule F W, admissible U → Module.finrank F U ≤ dim) ∧
        LinearIndependent F (fun i : ↥nz => out i.val)) ∧
      (wire ok = false → ∀ i, out i = 0) ∧
      (∀ j : Fin bitsN, wire (dimWire j) = dim.testBit j.val) := by
  intro k m b h hk F W ix0 rot0 run0 inputs bitsN H B
  obtain ⟨gs, okW, outW, dW, hG, hok, hout, hdw, hsize, hspec⟩ :=
    PEqualNP.Outside.L_meta_29723.core k m b h hk
  refine ⟨⟨gs, okW⟩, ⟨okW, hok⟩, fun i j => ⟨outW i j, hout i j⟩, fun j => ⟨dW j, hdw j⟩,
    hG.1, hG.2, rfl, hsize, ?_⟩
  intro Q marked pack bits wire out K nz dim obs admissible
  obtain ⟨h1, h2, h3, h4⟩ := hspec Q marked
  exact ⟨h1, h2, h3, h4⟩
