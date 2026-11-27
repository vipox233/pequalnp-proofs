import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_807

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

end PEqualNP.Outside.L_lib_807

theorem PEqualNP.Outside.L_lib_807 : (∀ (n s d w : Nat) (hn : 0 < n) (hs : 0 < s),
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
    PEqualNP.Outside.L_lib_807.build_spec n s d w hn hs
  refine ⟨⟨(PEqualNP.Outside.L_lib_807.r15 n s d w).1,
      (PEqualNP.Outside.L_lib_807.r10 n s d w).2.1⟩,
    ⟨(PEqualNP.Outside.L_lib_807.r10 n s d w).2.1, hok⟩,
    fun t j => ⟨(PEqualNP.Outside.L_lib_807.r11 n s d w).2 (t, j), hwalk _⟩,
    fun i j => ⟨(PEqualNP.Outside.L_lib_807.r15 n s d w).2 (i, j), hout _⟩,
    hGood.1, hGood.2, rfl,
    le_trans hlen (PEqualNP.Outside.L_lib_807.size_le n s d w hn hs), ?_⟩
  intro start stop edge equation pack bits wire out K nz legal possible
  obtain ⟨hF, hin⟩ :=
    PEqualNP.Outside.L_lib_807.final_core n s d w hn hs start stop edge equation
  obtain ⟨h1, h2, h3⟩ :=
    PEqualNP.Outside.L_lib_807.sem_D1 n s d w start stop edge equation _ hin hF
  obtain ⟨h4, h5⟩ :=
    PEqualNP.Outside.L_lib_807.sem_D2 n s d w hn start stop edge equation _ hin hF
  refine ⟨h1, ?_, ?_⟩
  · intro hokv
    obtain ⟨p, hp, hw, hopt⟩ := h2 hokv
    obtain ⟨hb1, hb0⟩ := h4 p hw
    have hK : K = PEqualNP.Outside.L_lib_807.m1_poss
        (PEqualNP.Outside.L_lib_807.pathLam equation p) :=
      (PEqualNP.Outside.L_lib_807.m2_basis _ _ hb1 hb0).1
    refine ⟨p, hp, hw, ?_, ?_, ?_⟩
    · intro x
      rw [hK]
      exact (PEqualNP.Outside.L_lib_807.poss_iff equation p x).symm
    · exact (PEqualNP.Outside.L_lib_807.m2_basis _ _ hb1 hb0).2
    · intro q hq
      have hc : Nat.card {x : W // possible q x} =
          Nat.card {x : Fin n → ZMod 2 // x ∈ PEqualNP.Outside.L_lib_807.m1_poss
            (PEqualNP.Outside.L_lib_807.pathLam equation q)} :=
        Nat.card_congr (Equiv.subtypeEquivRight
          (fun x => PEqualNP.Outside.L_lib_807.poss_iff equation q x))
      rw [hc, PEqualNP.Outside.L_lib_807.m2_card_sub, hK]
      exact Nat.pow_le_pow_right (by norm_num) (hopt q hq)
  · intro hokv
    have hwf := h3 hokv
    refine ⟨fun i => ?_, hwf⟩
    funext j
    have := h5 hwf i j
    change (if PEqualNP.Outside.L_lib_807.wireAt (PEqualNP.Outside.L_lib_807.r15 n s d w).1
      (PEqualNP.Outside.L_lib_807.b_bits n s d w start stop edge equation)
      ((PEqualNP.Outside.L_lib_807.r15 n s d w).2 (i, j)) = true then (1 : ZMod 2) else 0) = 0
    rw [this]
    rfl
