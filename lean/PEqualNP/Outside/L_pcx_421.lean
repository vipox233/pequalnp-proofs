import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_421_aux

abbrev F := ZMod 2

def fv (r : ℕ) (x : Fin r → Fin 3 → F) : Fin r → F := fun i => x i 2 + x i 0 * x i 1

def Works (r d e : ℕ) : Prop :=
  ∃ (first : (Fin r → Fin 3 → F) →ₗ[F] (Fin d → F))
     (second : (Fin d → F) → (Fin r → Fin 3 → F) →ₗ[F] (Fin e → F))
     (out : (Fin d → F) → (Fin e → F) → (Fin r → F)),
     ∀ x, out (first x) (second (first x) x) = fv r x

def One (a b : ℕ) : Prop :=
  ∃ (g1 : (Fin 3 → F) →ₗ[F] (Fin a → F))
    (g2 : (Fin a → F) → (Fin 3 → F) →ₗ[F] (Fin b → F))
    (o : (Fin a → F) → (Fin b → F) → F),
    ∀ v, o (g1 v) (g2 (g1 v) v) = v 2 + v 0 * v 1

theorem works_zero (d e : ℕ) : Works 0 d e :=
  ⟨0, fun _ => 0, fun _ _ => fun i => Fin.elim0 i, fun _ => funext fun i => Fin.elim0 i⟩

theorem append_add {n m : ℕ} (u u' : Fin n → F) (v v' : Fin m → F) :
    Fin.append (u + u') (v + v') = Fin.append u v + Fin.append u' v' := by
  funext j
  refine Fin.addCases ?_ ?_ j <;> intro j <;> simp

theorem append_smul {n m : ℕ} (c : F) (u : Fin n → F) (v : Fin m → F) :
    Fin.append (c • u) (c • v) = c • Fin.append u v := by
  funext j
  refine Fin.addCases ?_ ?_ j <;> intro j <;> simp

def lft {n m : ℕ} (z : Fin (n+m) → F) : Fin n → F := fun j => z (Fin.castAdd m j)

def rgt {n m : ℕ} (z : Fin (n+m) → F) : Fin m → F := fun j => z (Fin.natAdd n j)

theorem lft_append {n m : ℕ} (u : Fin n → F) (v : Fin m → F) : lft (Fin.append u v) = u := by
  funext j; simp [lft]

theorem rgt_append {n m : ℕ} (u : Fin n → F) (v : Fin m → F) : rgt (Fin.append u v) = v := by
  funext j; simp [rgt]

theorem step {r d e a b : ℕ} (h : Works r d e) (h1 : One a b) : Works (r+1) (d+a) (e+b) := by
  obtain ⟨first, second, out, hw⟩ := h
  obtain ⟨g1, g2, o, ho⟩ := h1
  have tadd : ∀ x y : Fin (r+1) → Fin 3 → F, Fin.tail (x + y) = Fin.tail x + Fin.tail y :=
    fun _ _ => rfl
  have tsmul : ∀ (c : F) (x : Fin (r+1) → Fin 3 → F), Fin.tail (c • x) = c • Fin.tail x :=
    fun _ _ => rfl
  refine ⟨{ toFun := fun x => Fin.append (first (Fin.tail x)) (g1 (x 0)),
            map_add' := ?_, map_smul' := ?_ },
          fun z => { toFun := fun x => Fin.append (second (lft z) (Fin.tail x)) (g2 (rgt z) (x 0)),
                     map_add' := ?_, map_smul' := ?_ },
          fun z t => Fin.cons (o (rgt z) (rgt t)) (out (lft z) (lft t)), ?_⟩
  · intro x y
    simp only [tadd, map_add, Pi.add_apply]
    exact append_add _ _ _ _
  · intro c x
    simp only [tsmul, map_smul, Pi.smul_apply, RingHom.id_apply]
    exact append_smul _ _ _
  · intro x y
    simp only [tadd, map_add, Pi.add_apply]
    exact append_add _ _ _ _
  · intro c x
    simp only [tsmul, map_smul, Pi.smul_apply, RingHom.id_apply]
    exact append_smul _ _ _
  · intro x
    funext i
    refine Fin.cases ?_ ?_ i
    · simp only [LinearMap.coe_mk, AddHom.coe_mk, lft_append, rgt_append, Fin.cons_zero, ho]
      rfl
    · intro i
      simp only [LinearMap.coe_mk, AddHom.coe_mk, lft_append, rgt_append, Fin.cons_succ, hw]
      rfl

theorem one11 : One 1 1 :=
  ⟨{ toFun := fun v _ => v 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
   fun z => { toFun := fun v _ => v 2 + z 0 * v 1,
              map_add' := fun v w => by funext j; simp; ring,
              map_smul' := fun c v => by funext j; simp; ring },
   fun _ t => t 0, fun _ => rfl⟩

theorem one30 : One 3 0 :=
  ⟨LinearMap.id, fun _ => 0, fun z _ => z 2 + z 0 * z 1, fun _ => rfl⟩

theorem one03 : One 0 3 :=
  ⟨0, fun _ => LinearMap.id, fun _ t => t 2 + t 0 * t 1, fun _ => rfl⟩

theorem upper : ∀ r d e : ℕ, 3*r ≤ 2*d+e → 3*r ≤ d+2*e → Works r d e := by
  intro r
  induction r with
  | zero => intro d e _ _; exact works_zero d e
  | succ r ih =>
    intro d e h1 h2
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 3 := ⟨e - 3, by omega⟩
      have := step (ih 0 e' (by omega) (by omega)) one03
      simpa using this
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 3 := ⟨d - 3, by omega⟩
      have := step (ih d' 0 (by omega) (by omega)) one30
      simpa using this
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    exact step (ih d' e' (by omega) (by omega)) one11


theorem finrank_X (r : ℕ) : Module.finrank F (Fin r → Fin 3 → F) = 3 * r := by
  rw [Module.finrank_pi_fintype]
  simp
  ring

theorem ker_bound {r n : ℕ} (L : (Fin r → Fin 3 → F) →ₗ[F] (Fin n → F)) :
    3 * r ≤ Module.finrank F (LinearMap.ker L) + n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 : Module.finrank F (LinearMap.range L) ≤ n := by
    have := Submodule.finrank_le (LinearMap.range L)
    simpa using this
  rw [finrank_X] at h1
  omega

theorem inf_bound {r n : ℕ} (K : Submodule F (Fin r → Fin 3 → F))
    (L : (Fin r → Fin 3 → F) →ₗ[F] (Fin n → F)) :
    Module.finrank F K ≤ Module.finrank F (K ⊓ LinearMap.ker L : Submodule F _) + n := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq K (LinearMap.ker L)
  have h2 := ker_bound L
  have h3 : Module.finrank F (K ⊔ LinearMap.ker L : Submodule F _) ≤ 3 * r := by
    have := Submodule.finrank_le (K ⊔ LinearMap.ker L)
    rwa [finrank_X] at this
  omega

theorem fin_lemma : ∀ v0 v1 u0 u1 u2 t : ZMod 2, (v0 ≠ 0 ∨ v1 ≠ 0) → u2 + u0 * u1 = 0 →
    v0 * u1 + v1 * u0 = 0 →
    t + v1 * (1 + v1) = (t + u2) + (v1 + u0) * ((1 + v1) + u1) →
    u0 = 0 ∧ u1 = 0 ∧ u2 = 0 := by
  decide

theorem lower {r d e : ℕ} (h : Works r d e) : 3*r ≤ 2*d+e ∧ 3*r ≤ d+2*e := by
  classical
  obtain ⟨first, second, out, hw⟩ := h
  set K := LinearMap.ker first with hKdef
  have hfib : ∀ y z, first y = first z → second (first y) y = second (first y) z →
      fv r y = fv r z := by
    intro y z h1 h2
    rw [← hw y, ← hw z, ← h1, h2]
  have hK := ker_bound first
  set W0 := K ⊓ LinearMap.ker (second 0) with hW0
  have hW0b := inf_bound K (second 0)
  have keyw : ∀ w ∈ W0, ∀ k ∈ K, ∀ i : Fin r,
      k i 0 * w i 1 + k i 1 * w i 0 = 0 ∧ w i 2 + w i 0 * w i 1 = 0 := by
    intro w hw k hk i
    have hwK : first w = 0 := (Submodule.mem_inf.1 hw).1
    have hw2 : second 0 w = 0 := (Submodule.mem_inf.1 hw).2
    have hk' : first k = 0 := hk
    have e1 : fv r k = fv r (k + w) :=
      hfib k (k + w) (by rw [map_add, hwK, add_zero]) (by rw [hk', map_add, hw2, add_zero])
    have e2 : fv r 0 = fv r w :=
      hfib 0 w (by rw [hwK, map_zero]) (by rw [map_zero, map_zero, hw2])
    have a1 : k i 2 + k i 0 * k i 1 =
        (k i 2 + w i 2) + (k i 0 + w i 0) * (k i 1 + w i 1) := congrFun e1 i
    have a2 : (0 : F) + 0 * 0 = w i 2 + w i 0 * w i 1 := congrFun e2 i
    constructor
    · linear_combination a2 - a1
    · linear_combination -a2
  let Ψ : (Fin r → Fin 3 → F) →ₗ[F] Module.Dual F (Fin r → Fin 3 → F) :=
    LinearMap.mk₂ F (fun w y => ∑ i, (y i 0 * w i 1 + y i 1 * w i 0))
      (by
        intro a b c
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by ring))
      (by
        intro a b c
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring))
      (by
        intro a b c
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by ring))
      (by
        intro a b c
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring))
  have hmap : LinearMap.range (Ψ.domRestrict W0) ≤ K.dualAnnihilator := by
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro k hk
    show ∑ i, (k i 0 * w i 1 + k i 1 * w i 0) = 0
    exact Finset.sum_eq_zero (fun i _ => (keyw w hw k hk i).1)
  have hinj : Function.Injective (Ψ.domRestrict W0) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w, hw⟩ h0
    have hv : ∀ i, w i 0 = 0 ∧ w i 1 = 0 := by
      intro i
      have c0 := LinearMap.congr_fun h0
        (fun j (c : Fin 3) => if j = i then (if c = 0 then (1:F) else 0) else 0)
      have c1 := LinearMap.congr_fun h0
        (fun j (c : Fin 3) => if j = i then (if c = 1 then (1:F) else 0) else 0)
      change ∑ x : Fin r, ((fun j (c : Fin 3) => if j = i then (if c = 0 then (1:F) else 0) else 0) x 0 * w x 1 +
        (fun j (c : Fin 3) => if j = i then (if c = 0 then (1:F) else 0) else 0) x 1 * w x 0) = 0 at c0
      change ∑ x : Fin r, ((fun j (c : Fin 3) => if j = i then (if c = 1 then (1:F) else 0) else 0) x 0 * w x 1 +
        (fun j (c : Fin 3) => if j = i then (if c = 1 then (1:F) else 0) else 0) x 1 * w x 0) = 0 at c1
      simp at c0 c1
      exact ⟨c1, c0⟩
    apply Subtype.ext
    funext i c
    have h2 := (keyw w hw 0 K.zero_mem i).2
    rw [(hv i).1, (hv i).2] at h2
    have h2' : w i 2 = 0 := by simpa using h2
    fin_cases c
    · exact (hv i).1
    · exact (hv i).2
    · exact h2'
  have hr1 := LinearMap.finrank_range_of_inj hinj
  have hr2 := Submodule.finrank_mono hmap
  have hr3 := Subspace.finrank_add_finrank_dualAnnihilator_eq K
  rw [finrank_X] at hr3
  have P : ∀ i : Fin r, ∃ kk : Fin r → Fin 3 → F, kk ∈ K ∧
      ((∃ k ∈ K, k i 0 ≠ 0 ∨ k i 1 ≠ 0) → (kk i 0 ≠ 0 ∨ kk i 1 ≠ 0)) := by
    intro i
    by_cases hP : ∃ k ∈ K, k i 0 ≠ 0 ∨ k i 1 ≠ 0
    · obtain ⟨k, hk, h⟩ := hP
      exact ⟨k, hk, fun _ => h⟩
    · exact ⟨0, K.zero_mem, fun h => absurd h hP⟩
  choose kk hkK hkP using P
  let δ : Fin r → Fin 3 → F := fun i => ![kk i i 1, 1 + kk i i 1, 0]
  set W1 := K ⊓ LinearMap.ker (second (first δ)) with hW1
  have hW1b := inf_bound K (second (first δ))
  have hdis : W0 ⊓ W1 = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw0, hw1⟩ := Submodule.mem_inf.1 hw
    have hwK : w ∈ K := (Submodule.mem_inf.1 hw0).1
    have hw2 : second (first δ) w = 0 := (Submodule.mem_inf.1 hw1).2
    have hwK' : first w = 0 := hwK
    have e3 : fv r δ = fv r (δ + w) :=
      hfib δ (δ + w) (by rw [map_add, hwK', add_zero]) (by rw [map_add, hw2, add_zero])
    rw [Submodule.mem_bot]
    funext i c
    have a3 : δ i 2 + kk i i 1 * (1 + kk i i 1) =
        (δ i 2 + w i 2) + (kk i i 1 + w i 0) * ((1 + kk i i 1) + w i 1) := congrFun e3 i
    obtain ⟨b1, b2⟩ := keyw w hw0 (kk i) (hkK i) i
    have hzero : w i 0 = 0 ∧ w i 1 = 0 ∧ w i 2 = 0 := by
      by_cases hP : ∃ k ∈ K, k i 0 ≠ 0 ∨ k i 1 ≠ 0
      · exact fin_lemma (kk i i 0) (kk i i 1) (w i 0) (w i 1) (w i 2) (δ i 2) (hkP i hP) b2 b1 a3
      · push Not at hP
        obtain ⟨h0, h1⟩ := hP w hwK
        refine ⟨h0, h1, ?_⟩
        rw [h0, h1] at b2
        simpa using b2
    fin_cases c
    · exact hzero.1
    · exact hzero.2.1
    · exact hzero.2.2
  have hs := Submodule.finrank_sup_add_finrank_inf_eq W0 W1
  rw [hdis, finrank_bot] at hs
  have hs2 : Module.finrank F (W0 ⊔ W1 : Submodule F _) ≤ Module.finrank F K :=
    Submodule.finrank_mono (sup_le inf_le_left inf_le_left)
  have A1 : 3 * r ≤ Module.finrank F K + d := hK
  have A2 : Module.finrank F K ≤ Module.finrank F W0 + e := hW0b
  have A3 : Module.finrank F K ≤ Module.finrank F W1 + e := hW1b
  have A4 : Module.finrank F W0 + Module.finrank F K ≤ 3 * r := by
    have : Module.finrank F W0 ≤ Module.finrank F K.dualAnnihilator := by
      rw [← hr1]
      exact hr2
    omega
  have A5 : Module.finrank F W0 + Module.finrank F W1 ≤ Module.finrank F K := by omega
  constructor <;> omega

end PEqualNP.Outside.L_pcx_421_aux

theorem PEqualNP.Outside.L_pcx_421 : (∀ (r d e : ℕ),
  let F := ZMod 2
  let X := Fin r → Fin 3 → F
  let Y := Fin r → F
  let f := fun (x : X) (i : Fin r) => x i 2 + x i 0 * x i 1
  (∃ (first : X →ₗ[F] (Fin d → F))
     (second : (Fin d → F) → X →ₗ[F] (Fin e → F))
     (out : (Fin d → F) → (Fin e → F) → Y),
     ∀ x : X, out (first x) (second (first x) x) = f x) ↔
    3*r ≤ 2*d+e ∧ 3*r ≤ d+2*e) := by
  intro r d e
  exact Iff.intro (fun h => PEqualNP.Outside.L_pcx_421_aux.lower h)
    (fun h => PEqualNP.Outside.L_pcx_421_aux.upper r d e h.1 h.2)
