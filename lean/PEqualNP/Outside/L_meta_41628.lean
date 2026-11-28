import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41628

theorem lemA {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (k r : ℕ) (hk : 0 < k)
    (g : V →ₗ[ZMod 2] (Fin k → ZMod 2)) (hr : Module.finrank (ZMod 2) (LinearMap.range g) ≤ r) :
    ∃ c : Fin r → Fin k, ∀ x, (∀ j, g x (c j) = 0) → g x = 0 := by
  classical
  let φ : Fin k → Module.Dual (ZMod 2) V := fun i => (LinearMap.proj i).comp g
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent (ZMod 2) (Set.range φ)
  have hfin : b.Finite := (Set.finite_range φ).subset hbs
  haveI : Fintype b := hfin.fintype
  have hcard : Fintype.card b ≤ r := by
    have h1 := finrank_span_set_eq_card (R := ZMod 2) (s := b) hli
    have h2 : Submodule.span (ZMod 2) b ≤ LinearMap.range g.dualMap := by
      rw [hspan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨LinearMap.proj i, rfl⟩
    have h3 := Submodule.finrank_mono h2
    rw [LinearMap.finrank_range_dualMap_eq_finrank_range] at h3
    rw [← Set.toFinset_card]; omega
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le (α := b) (β := Fin r) (by simpa using hcard)
  have hidx : ∀ ψ : b, ∃ i, φ i = ψ.1 := fun ψ => hbs ψ.2
  refine ⟨fun j => if h : ∃ ψ : b, emb ψ = j then Classical.choose (hidx (Classical.choose h))
    else ⟨0, hk⟩, ?_⟩
  intro x hx
  have hb : ∀ ψ ∈ b, ψ x = 0 := by
    intro ψ hψ
    have h : ∃ ψ' : b, emb ψ' = emb ⟨ψ, hψ⟩ := ⟨_, rfl⟩
    have h1 := hx (emb ⟨ψ, hψ⟩)
    simp only [dif_pos h] at h1
    have h2 : Classical.choose h = ⟨ψ, hψ⟩ := emb.injective (Classical.choose_spec h)
    have key : ∀ ψ' : b, ψ' = ⟨ψ, hψ⟩ → g x (Classical.choose (hidx ψ')) = 0 → ψ x = 0 := by
      intro ψ' he h
      subst he
      have h3 := Classical.choose_spec (hidx ⟨ψ, hψ⟩)
      exact (LinearMap.congr_fun h3 x).symm.trans h
    exact key _ h2 h1
  funext i
  have hi : φ i ∈ Submodule.span (ZMod 2) b := by
    rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩
  have hle : Submodule.span (ZMod 2) b ≤ LinearMap.ker (Module.Dual.eval (ZMod 2) V x) := by
    rw [Submodule.span_le]
    intro ψ hψ
    exact LinearMap.mem_ker.2 (hb ψ hψ)
  exact LinearMap.mem_ker.1 (hle hi)

theorem lemB {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V] (s : ℕ)
    (N K' : Submodule (ZMod 2) V) (p : V) (hp : p ∉ N)
    (hr : Module.finrank (ZMod 2) K' + 1 ≤ s) :
    ∃ f : V →ₗ[ZMod 2] (Fin s → ZMod 2), (∀ y ∈ K', f y = 0 → y = 0) ∧
      (∀ y ∈ N, f (p + y) ≠ 0) := by
  obtain ⟨f0, hf0, hN⟩ := Submodule.exists_le_ker_of_notMem hp
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective K'.subtype (Submodule.ker_subtype K')
  let b := Module.finBasis (ZMod 2) K'
  refine ⟨LinearMap.pi (fun j : Fin s => if h : j.val < Module.finrank (ZMod 2) K' then
    (b.coord ⟨j.val, h⟩).comp π else f0), ?_, ?_⟩
  · intro y hy h
    have hπy : π y = ⟨y, hy⟩ := LinearMap.congr_fun hπ ⟨y, hy⟩
    have h0 : (⟨y, hy⟩ : K') = 0 := by
      apply b.ext_elem
      intro i
      have hi := congrFun h ⟨i.val, by omega⟩
      simp only [LinearMap.pi_apply, dif_pos i.2, LinearMap.comp_apply, hπy] at hi
      simpa using hi
    exact congrArg Subtype.val h0
  · intro y hy h
    have hj := congrFun h ⟨Module.finrank (ZMod 2) K', by omega⟩
    simp only [LinearMap.pi_apply, lt_irrefl, dif_neg, not_false_iff, map_add, Pi.zero_apply] at hj
    have hy0 : f0 y = 0 := LinearMap.mem_ker.1 (hN hy)
    rw [hy0, add_zero] at hj
    exact hf0 hj

variable {k : ℕ}

def xr (x y : Fin k → Bool) : Fin k → Bool := fun i => xor (x i) (y i)
def zz : Fin k → Bool := fun _ => false

theorem xr_self (x : Fin k → Bool) : xr x x = zz := by funext i; simp [xr, zz]
theorem xr_zz (x : Fin k → Bool) : xr x zz = x := by funext i; simp [xr, zz]
theorem xr_cancel (x y : Fin k → Bool) : xr x (xr x y) = y := by funext i; simp [xr]
theorem xr_eq_zz (x y : Fin k → Bool) (h : xr x y = zz) : x = y := by
  funext i
  have := congrFun h i
  simpa [xr, zz] using this
theorem xr_left (x t : Fin k → Bool) (h : xr x t = x) : t = zz := by
  funext i
  have := congrFun h i
  revert this
  simp only [xr, zz]
  cases x i <;> cases t i <;> simp

def E : (Fin k → Bool) ≃ (Fin k → ZMod 2) where
  toFun x i := if x i then 1 else 0
  invFun v i := decide (v i = 1)
  left_inv x := by funext i; cases h : x i <;> simp [h]
  right_inv v := by
    funext i
    have h : ∀ c : ZMod 2, (if decide (c = 1) then (1 : ZMod 2) else 0) = c := by decide
    exact h (v i)

theorem E_xr (x y : Fin k → Bool) : E (xr x y) = E x + E y := by
  funext i
  show (if xor (x i) (y i) then (1 : ZMod 2) else 0) = (if x i then 1 else 0) + (if y i then 1 else 0)
  cases x i <;> cases y i <;> decide

theorem E_zz : E (zz : Fin k → Bool) = 0 := by funext i; rfl

theorem E_eq_zero (x : Fin k → Bool) : E x = 0 ↔ x = zz := by
  rw [← E_zz]; exact E.apply_eq_iff_eq

theorem Esymm_add (v w : Fin k → ZMod 2) : E.symm (v + w) = xr (E.symm v) (E.symm w) := by
  apply E.injective; rw [E_xr]; simp

def lin (h : (Fin k → Bool) → (Fin k → Bool)) (hadd : ∀ x y, h (xr x y) = xr (h x) (h y)) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' (fun v => E (h (E.symm v)))
    (by intro v w; rw [Esymm_add, hadd, E_xr]))

theorem lin_E (h : (Fin k → Bool) → (Fin k → Bool)) (hadd : ∀ x y, h (xr x y) = xr (h x) (h y))
    (x : Fin k → Bool) : lin h hadd (E x) = E (h x) := by
  show E (h (E.symm (E x))) = E (h x)
  rw [Equiv.symm_apply_apply]

theorem add0 (h : (Fin k → Bool) → (Fin k → Bool)) (hadd : ∀ x y, h (xr x y) = xr (h x) (h y)) :
    h zz = zz := by
  have := hadd zz zz
  rw [xr_self, xr_self] at this
  exact this

def par (J : Finset (Fin k)) (w : Fin k → Bool) : Bool :=
  decide ((J.filter (fun i => w i)).card % 2 = 1)

theorem bridge {s : ℕ} (f : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin s → ZMod 2)) (j : Fin s)
    (w : Fin k → Bool) :
    (f (E w) j = 1) ↔ ((Finset.univ.filter (fun i : Fin k =>
      f (fun j' => if i = j' then 1 else 0) j = 1)).filter (fun i => w i)).card % 2 = 1 := by
  rw [LinearMap.pi_apply_eq_sum_univ f (E w), Finset.sum_apply]
  have h : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      (E w i • f (fun j' => if i = j' then (1 : ZMod 2) else 0)) j =
      if (f (fun j' => if i = j' then (1 : ZMod 2) else 0) j = 1 ∧ w i = true) then 1 else 0 := by
    intro i _
    show (if w i then (1 : ZMod 2) else 0) * f _ j = _
    generalize f (fun j' => if i = j' then (1 : ZMod 2) else 0) j = c
    cases w i <;> revert c <;> decide
  rw [Finset.sum_congr rfl h, Finset.sum_boole, Finset.filter_filter,
    ← Nat.cast_one (R := ZMod 2), ZMod.natCast_eq_natCast_iff']

theorem ker_fin (M : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (P : (Fin k → Bool) → Prop)
    [DecidablePred P] (h : ∀ x, P x ↔ M (E x) = 0) :
    (Finset.univ.filter P).card = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker M) := by
  classical
  have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker M)
  rw [ZMod.card] at h1
  rw [← h1, ← Fintype.card_subtype]
  exact Fintype.card_congr (E.subtypeEquiv (fun x => (h x).trans LinearMap.mem_ker.symm))

theorem coreC (k s : ℕ) (hk : 0 < k)
    (L R G q0 : (Fin k → Bool) → (Fin k → Bool)) (Bl : (Fin k → Bool) → (Fin k → Bool) → (Fin k → Bool))
    (e0 : Fin k → Bool) (base diff : (Fin k → Bool) → (Fin k → Bool))
    (hL : ∀ x y, L (xr x y) = xr (L x) (L y)) (hR : ∀ x y, R (xr x y) = xr (R x) (R y))
    (hG : ∀ x y, G (xr x y) = xr (G x) (G y))
    (hB : ∀ w x y, Bl w (xr x y) = xr (Bl w x) (Bl w y))
    (hq0 : q0 zz = zz) (hBz : ∀ y, Bl zz y = zz)
    (hdiff : ∀ x, diff x = xr e0 (G (L x)))
    (hbase : ∀ x t, base (xr x t) = xr (base x) (xr (q0 (L t)) (xr (Bl (L t) (L x)) (R t))))
    (hT : (Finset.univ.filter (fun x => G (L x) = zz)).card = 2 ^ s)
    (hK : 2 * (Finset.univ.filter (fun x => L x = zz)).card = 2 ^ s)
    (hinj : ∀ x t, G (L t) = zz → base (xr x t) = base x → t = zz) :
    ∃ (c : Fin (k - s) → Fin k) (J : Fin s → Finset (Fin k)), ∀ x y,
      (∀ j, diff x (c j) = diff y (c j)) → (∀ j, par (J j) (base x) = par (J j) (base y)) →
      x = y := by
  classical
  have L0 : L zz = zz := add0 L hL
  have G0 : G zz = zz := add0 G hG
  have R0 : R zz = zz := add0 R hR
  have cK := ker_fin (lin L hL) (fun x => L x = zz) (fun x => by rw [lin_E, E_eq_zero])
  have cT := ker_fin ((lin G hG).comp (lin L hL)) (fun x => G (L x) = zz)
    (fun x => by rw [LinearMap.comp_apply, lin_E, lin_E, E_eq_zero])
  have fK : Module.finrank (ZMod 2) (LinearMap.ker (lin L hL)) + 1 = s := by
    rw [cK] at hK
    rw [← pow_succ'] at hK
    exact Nat.pow_right_injective (le_refl 2) hK
  have fT : Module.finrank (ZMod 2) (LinearMap.ker ((lin G hG).comp (lin L hL))) = s := by
    rw [cT] at hT
    exact Nat.pow_right_injective (le_refl 2) hT
  have fR : Module.finrank (ZMod 2) (LinearMap.range ((lin G hG).comp (lin L hL))) ≤ k - s := by
    have h := LinearMap.finrank_range_add_finrank_ker ((lin G hG).comp (lin L hL))
    rw [fT, Module.finrank_fin_fun] at h
    omega
  obtain ⟨c, hc⟩ := lemA k (k - s) hk ((lin G hG).comp (lin L hL)) fR
  have ht0 : ∃ t0, G (L t0) = zz ∧ L t0 ≠ zz := by
    by_contra hcon
    have hsub : Finset.univ.filter (fun x => G (L x) = zz) ⊆ Finset.univ.filter (fun x => L x = zz) := by
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      refine ⟨ht.1, ?_⟩
      by_contra h
      exact hcon ⟨t, ht.2, h⟩
    have h1 := Finset.card_le_card hsub
    have h2 : 0 < 2 ^ s := Nat.pow_pos (by norm_num)
    omega
  obtain ⟨t0, ht0T, ht0K⟩ := ht0
  have coset : ∀ t, G (L t) = zz → L t ≠ zz → ∃ κ, L κ = zz ∧ t = xr t0 κ := by
    have hsub : Finset.univ.filter (fun x => L x = zz) ∪
        (Finset.univ.filter (fun x => L x = zz)).image (xr t0) ⊆
        Finset.univ.filter (fun x => G (L x) = zz) := by
      intro t ht
      rw [Finset.mem_union, Finset.mem_image] at ht
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases ht with ht | ⟨κ, hκ, rfl⟩
      · rw [(Finset.mem_filter.1 ht).2, G0]
      · rw [hL, (Finset.mem_filter.1 hκ).2, xr_zz, ht0T]
    have hdisj : Disjoint (Finset.univ.filter (fun x => L x = zz))
        ((Finset.univ.filter (fun x => L x = zz)).image (xr t0)) := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.1 ht'
      have h1 := (Finset.mem_filter.1 ht).2
      rw [hL, (Finset.mem_filter.1 hκ).2, xr_zz] at h1
      exact ht0K h1
    have hinjx : Function.Injective (xr t0) := by
      intro a b hab
      have := congrArg (xr t0) hab
      rwa [xr_cancel, xr_cancel] at this
    have hcard : (Finset.univ.filter (fun x => L x = zz) ∪
        (Finset.univ.filter (fun x => L x = zz)).image (xr t0)).card =
        2 * (Finset.univ.filter (fun x => L x = zz)).card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinjx]
      ring
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hK, hT])
    intro t htT htK
    have ht : t ∈ Finset.univ.filter (fun x => G (L x) = zz) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, htT⟩
    rw [← heq, Finset.mem_union, Finset.mem_image] at ht
    rcases ht with ht | ⟨κ, hκ, rfl⟩
    · exact absurd (Finset.mem_filter.1 ht).2 htK
    · exact ⟨κ, (Finset.mem_filter.1 hκ).2, rfl⟩
  have hp : E (xr (q0 (L t0)) (R t0)) ∉
      LinearMap.range ((lin (Bl (L t0)) (hB (L t0))).comp (lin L hL)) ⊔
        (LinearMap.ker (lin L hL)).map (lin R hR) := by
    intro hpN
    obtain ⟨y1, hy1, y2, hy2, hsum⟩ := Submodule.mem_sup.1 hpN
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hy1
    obtain ⟨κ', hκ', rfl⟩ := Submodule.mem_map.1 hy2
    obtain ⟨x, rfl⟩ := E.surjective v
    obtain ⟨κ, rfl⟩ := E.surjective κ'
    have hκ : L κ = zz := by
      have := LinearMap.mem_ker.1 hκ'
      rwa [lin_E, E_eq_zero] at this
    rw [LinearMap.comp_apply, lin_E, lin_E, lin_E] at hsum
    have hLt : L (xr t0 κ) = L t0 := by rw [hL, hκ, xr_zz]
    have hΔ : xr (q0 (L t0)) (xr (Bl (L t0) (L x)) (R (xr t0 κ))) = zz := by
      apply E.injective
      rw [E_zz, hR, E_xr, E_xr, E_xr]
      rw [E_xr] at hsum
      have h2 : ∀ a b : Fin k → ZMod 2, a + a = 0 := by
        intro a _; funext i; show a i + a i = 0; generalize a i = c; revert c; decide
      have h5 : ∀ a b c d : Fin k → ZMod 2, b + d = a + c → a + (b + (c + d)) = 0 := by
        intro a b c d h
        rw [show a + (b + (c + d)) = (a + c) + (b + d) by abel, h]
        exact h2 _ 0
      exact h5 _ _ _ _ hsum
    have hb := hbase x (xr t0 κ)
    rw [hLt, hΔ, xr_zz] at hb
    have h4 := hinj x (xr t0 κ) (by rw [hLt, ht0T]) hb
    rw [h4, L0] at hLt
    exact ht0K hLt.symm
  have fK' : Module.finrank (ZMod 2) ((LinearMap.ker (lin L hL)).map (lin R hR)) + 1 ≤ s := by
    have := Submodule.finrank_map_le (lin R hR) (LinearMap.ker (lin L hL))
    omega
  obtain ⟨f, hf1, hf2⟩ := lemB s _ ((LinearMap.ker (lin L hL)).map (lin R hR)) _ hp fK'
  refine ⟨c, fun j => Finset.univ.filter (fun i : Fin k =>
    f (fun j' => if i = j' then 1 else 0) j = 1), ?_⟩
  intro x y hd hpar
  have hy : y = xr x (xr x y) := (xr_cancel x y).symm
  have hT' : G (L (xr x y)) = zz := by
    rw [← E_eq_zero]
    have h1 := hc (E (xr x y)) (fun j => by
      rw [LinearMap.comp_apply, lin_E, lin_E, hL, hG]
      have hj := hd j
      rw [hdiff, hdiff] at hj
      show (if xor (G (L x) (c j)) (G (L y) (c j)) then (1 : ZMod 2) else 0) = 0
      have hj' : xor (e0 (c j)) (G (L x) (c j)) = xor (e0 (c j)) (G (L y) (c j)) := hj
      revert hj'
      cases e0 (c j) <;> cases G (L x) (c j) <;> cases G (L y) (c j) <;> simp)
    rwa [LinearMap.comp_apply, lin_E, lin_E] at h1
  have hfΔ : f (E (xr (q0 (L (xr x y))) (xr (Bl (L (xr x y)) (L x)) (R (xr x y))))) = 0 := by
    funext j
    have hj := hpar j
    rw [hy, hbase] at hj
    have hj2 := decide_eq_decide.1 hj
    rw [← bridge f j, ← bridge f j, E_xr, map_add] at hj2
    have h2 : ∀ a b : ZMod 2, (a = 1 ↔ a + b = 1) → b = 0 := by decide
    exact h2 _ _ hj2
  have ht : xr x y = zz := by
    by_cases hLt : L (xr x y) = zz
    · rw [hLt, hq0, hBz] at hfΔ
      have hΔ : xr (zz : Fin k → Bool) (xr zz (R (xr x y))) = R (xr x y) := by
        funext i; simp [xr, zz]
      rw [hΔ, ← lin_E R hR] at hfΔ
      have h1 := hf1 _ (Submodule.mem_map.2 ⟨E (xr x y),
        LinearMap.mem_ker.2 (by rw [lin_E, hLt, E_zz]), rfl⟩) hfΔ
      rw [lin_E, E_eq_zero] at h1
      have hb := hbase x (xr x y)
      rw [hLt, hq0, hBz, hΔ, h1, xr_zz] at hb
      exact hinj x (xr x y) hT' hb
    · exfalso
      obtain ⟨κ, hκ, hκe⟩ := coset _ hT' hLt
      have hLt0 : L (xr x y) = L t0 := by rw [hκe, hL, hκ, xr_zz]
      rw [hLt0, hκe, hR, E_xr, E_xr, E_xr] at hfΔ
      refine hf2 (E (Bl (L t0) (L x)) + E (R κ)) (Submodule.mem_sup.2
        ⟨_, LinearMap.mem_range.2 ⟨E x, by rw [LinearMap.comp_apply, lin_E, lin_E]⟩, _,
          Submodule.mem_map.2 ⟨E κ, LinearMap.mem_ker.2 (by rw [lin_E, hκ, E_zz]), lin_E R hR κ⟩,
          rfl⟩) ?_
      rw [← hfΔ, E_xr]
      congr 1
      abel
  exact xr_eq_zz x y ht

theorem asm (k s n q : ℕ) (base diff : (Fin k → Bool) → (Fin k → Bool))
    (c : Fin (k - s) → Fin k) (J : Fin s → Finset (Fin k))
    (hCJ : ∀ x y, (∀ j, diff x (c j) = diff y (c j)) →
      (∀ j, par (J j) (base x) = par (J j) (base y)) → x = y) (hq : n * s ≤ q) :
    ∃ (site : Fin (n * (k - s)) → Fin n × Fin k) (mask : Fin q → Finset (Fin n × Fin k)),
      Function.Injective (fun x : Fin n → (Fin k → Bool) =>
        ((fun i : Fin (n * (k - s)) => diff (x (site i).1) (site i).2),
         (fun j : Fin q => decide (((mask j).filter (fun a => base (x a.1) a.2)).card % 2 = 1)))) := by
  classical
  refine ⟨fun i => ((finProdFinEquiv.symm i).1, c (finProdFinEquiv.symm i).2),
    fun j => if h : j.val < n * s then
      (J (finProdFinEquiv.symm ⟨j.val, h⟩).2).map
        ⟨fun i => ((finProdFinEquiv.symm ⟨j.val, h⟩).1, i), fun i i' hii => (Prod.mk.inj hii).2⟩
      else ∅, ?_⟩
  intro x y h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  funext a
  apply hCJ
  · intro j
    have := congrFun h1 (finProdFinEquiv (a, j))
    simpa using this
  · intro j
    have hlt : (finProdFinEquiv (a, j)).val < n * s := (finProdFinEquiv (a, j)).2
    have := congrFun h2 ⟨(finProdFinEquiv (a, j)).val, lt_of_lt_of_le hlt hq⟩
    simp only [dif_pos hlt, Fin.eta, Equiv.symm_apply_apply, Finset.filter_map,
      Finset.card_map] at this
    exact this

def chiG (σ1 σ2 : Fin k → Fin k) (r : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (r i) (!(r (σ1 i)) && r (σ2 i))
def BlG (σ1 σ2 : Fin k → Fin k) (w y : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (y (σ1 i) && w (σ2 i)) (w (σ1 i) && y (σ2 i))
def bs (σ1 σ2 : Fin k → Fin k) (L R : (Fin k → Bool) → (Fin k → Bool)) (a x : Fin k → Bool) :
    Fin k → Bool := xr (chiG σ1 σ2 (xr a (L x))) (R x)

theorem bG : ∀ w1 w2 v1 v2 a1 a2 b1 b2 : Bool,
    xor (xor (a1 && xor w2 v2) (xor w1 v1 && a2)) (xor (b1 && xor w2 v2) (xor w1 v1 && b2)) =
    xor (xor (xor (a1 && w2) (w1 && a2)) (xor (b1 && w2) (w1 && b2)))
      (xor (xor (a1 && v2) (v1 && a2)) (xor (b1 && v2) (v1 && b2))) := by decide

theorem bB : ∀ w1 w2 x1 x2 y1 y2 : Bool, xor (xor x1 y1 && w2) (w1 && xor x2 y2) =
    xor (xor (x1 && w2) (w1 && x2)) (xor (y1 && w2) (w1 && y2)) := by decide

theorem bdiff : ∀ a0 a1 a2 b0 b1 b2 l0 l1 l2 r : Bool,
    xor (xor (xor (xor a0 l0) (!(xor a1 l1) && xor a2 l2)) r)
      (xor (xor (xor b0 l0) (!(xor b1 l1) && xor b2 l2)) r) =
    xor (xor (xor a0 (!a1 && a2)) (xor b0 (!b1 && b2)))
      (xor (xor (a1 && l2) (l1 && a2)) (xor (b1 && l2) (l1 && b2))) := by decide

theorem bbase : ∀ a0 a1 a2 x0 x1 x2 t0 t1 t2 rx rt : Bool,
    xor (xor (xor a0 (xor x0 t0)) (!(xor a1 (xor x1 t1)) && xor a2 (xor x2 t2))) (xor rx rt) =
    xor (xor (xor (xor a0 x0) (!(xor a1 x1) && xor a2 x2)) rx)
      (xor (xor (xor t0 (!t1 && t2)) (xor (a1 && t2) (t1 && a2)))
        (xor (xor (x1 && t2) (t1 && x2)) rt)) := by decide

theorem bL : ∀ a b c d e f : Bool, xor (xor a b) (xor (xor c d) (xor e f)) =
    xor (xor a (xor c e)) (xor b (xor d f)) := by decide

theorem mid (k s : ℕ) (hk : 0 < k) (σ1 σ2 : Fin k → Fin k)
    (L R : (Fin k → Bool) → (Fin k → Bool))
    (hL : ∀ x y, L (xr x y) = xr (L x) (L y)) (hR : ∀ x y, R (xr x y) = xr (R x) (R y))
    (a b : Fin k → Bool)
    (hT : (Finset.univ.filter (fun x => xr (bs σ1 σ2 L R a x) (bs σ1 σ2 L R b x) =
      xr (bs σ1 σ2 L R a zz) (bs σ1 σ2 L R b zz))).card = 2 ^ s)
    (hK : 2 * (Finset.univ.filter (fun x => L x = zz)).card = 2 ^ s)
    (hinj : Function.Injective (fun x => (bs σ1 σ2 L R a x, bs σ1 σ2 L R b x))) :
    ∃ (c : Fin (k - s) → Fin k) (J : Fin s → Finset (Fin k)), ∀ x y,
      (∀ j, xr (bs σ1 σ2 L R a x) (bs σ1 σ2 L R b x) (c j) =
        xr (bs σ1 σ2 L R a y) (bs σ1 σ2 L R b y) (c j)) →
      (∀ j, par (J j) (bs σ1 σ2 L R a x) = par (J j) (bs σ1 σ2 L R a y)) → x = y := by
  have hdiff : ∀ x, xr (bs σ1 σ2 L R a x) (bs σ1 σ2 L R b x) =
      xr (xr (chiG σ1 σ2 a) (chiG σ1 σ2 b)) (xr (BlG σ1 σ2 (L x) a) (BlG σ1 σ2 (L x) b)) := by
    intro x; funext i; exact bdiff _ _ _ _ _ _ _ _ _ _
  have L0 := add0 L hL
  have hG : ∀ w w', (fun w => xr (BlG σ1 σ2 w a) (BlG σ1 σ2 w b)) (xr w w') =
      xr ((fun w => xr (BlG σ1 σ2 w a) (BlG σ1 σ2 w b)) w)
        ((fun w => xr (BlG σ1 σ2 w a) (BlG σ1 σ2 w b)) w') := by
    intro w w'; funext i; exact bG _ _ _ _ _ _ _ _
  have G0 : xr (BlG σ1 σ2 zz a) (BlG σ1 σ2 zz b) = zz :=
    add0 (fun w => xr (BlG σ1 σ2 w a) (BlG σ1 σ2 w b)) hG
  have hG' : ∀ w w', xr (BlG σ1 σ2 (xr w w') a) (BlG σ1 σ2 (xr w w') b) =
      xr (xr (BlG σ1 σ2 w a) (BlG σ1 σ2 w b)) (xr (BlG σ1 σ2 w' a) (BlG σ1 σ2 w' b)) := hG
  have hTiff : ∀ x, (xr (bs σ1 σ2 L R a x) (bs σ1 σ2 L R b x) =
      xr (bs σ1 σ2 L R a zz) (bs σ1 σ2 L R b zz)) ↔
      xr (BlG σ1 σ2 (L x) a) (BlG σ1 σ2 (L x) b) = zz := by
    intro x
    rw [hdiff, hdiff zz, L0, G0, xr_zz]
    constructor
    · intro h; exact xr_left _ _ h
    · intro h; rw [h, xr_zz]
  have hT' : (Finset.univ.filter (fun x =>
      (fun w => xr (BlG σ1 σ2 w a) (BlG σ1 σ2 w b)) (L x) = zz)).card = 2 ^ s := by
    rw [← hT]
    exact congrArg Finset.card (Finset.filter_congr (fun x _ => (hTiff x).symm))
  refine coreC k s hk L R (fun w => xr (BlG σ1 σ2 w a) (BlG σ1 σ2 w b))
    (fun w => xr (chiG σ1 σ2 w) (BlG σ1 σ2 w a)) (BlG σ1 σ2) (xr (chiG σ1 σ2 a) (chiG σ1 σ2 b))
    (bs σ1 σ2 L R a) (fun x => xr (bs σ1 σ2 L R a x) (bs σ1 σ2 L R b x)) hL hR hG ?_ ?_ ?_ hdiff
    ?_ hT' hK ?_
  · intro w x y; funext i; exact bB _ _ _ _ _ _
  · funext i; simp [xr, chiG, BlG, zz]
  · intro y; funext i; simp [BlG, zz]
  · intro x t
    show xr (chiG σ1 σ2 (xr a (L (xr x t)))) (R (xr x t)) = _
    rw [hL, hR]
    funext i
    exact bbase _ _ _ _ _ _ _ _ _ _ _
  · intro x t hGt hb
    have hd : xr (bs σ1 σ2 L R a (xr x t)) (bs σ1 σ2 L R b (xr x t)) =
        xr (bs σ1 σ2 L R a x) (bs σ1 σ2 L R b x) := by
      rw [hdiff, hdiff x, hL, hG', hGt, xr_zz]
    have h2 : bs σ1 σ2 L R b (xr x t) = bs σ1 σ2 L R b x := by
      rw [← xr_cancel (bs σ1 σ2 L R a (xr x t)) (bs σ1 σ2 L R b (xr x t)), hd, hb, xr_cancel]
    have h3 : xr x t = x := hinj (Prod.ext hb h2)
    exact xr_left x t h3

end PEqualNP.Outside.L_meta_41628

theorem PEqualNP.Outside.L_meta_41628 : ∀ (k : Nat) (hk : 0 < k),
  let W := Fin k → Bool
  let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (u v : W) (i : Fin k) => xor (u i) (v i)
  let mix := fun (d : Nat) (x : W) (i : Fin k) =>
    xor (x (ix (i.val+k-d % k))) (xor (x i) (x (ix (i.val+d))))
  let rot := fun (a : Nat) (x : W) (i : Fin k) => x (ix (i.val+k-a % k))
  let chi := fun (r : W) (i : Fin k) => xor (r i) (!(r (ix (i.val+1))) && r (ix (i.val+2)))
  ∀ (d ini fin : Nat) (u v : W),
    let L := fun x : W => mix d (rot ini x)
    let base := fun x : W => add (chi (add (mix d u) (L x))) (rot fin x)
    let other := fun x : W => add (chi (add (mix d v) (L x))) (rot fin x)
    let diff := fun x : W => add (base x) (other x)
    let z : W := fun _ => false
    let keys : Finset W := Finset.univ
    ∀ s : Nat, 0 < s → s ≤ k →
      (keys.filter (fun x => diff x = diff z)).card = 2^s →
      2*(keys.filter (fun x => L x = z)).card = 2^s →
      Function.Injective (fun x : W => (base x, other x)) →
      ∀ n q : Nat,
        let m := n*(k-s)
        (∃ (site : Fin m → Fin n × Fin k) (mask : Fin q → Finset (Fin n × Fin k)),
          Function.Injective (fun x : Fin n → W =>
            ((fun i : Fin m => diff (x (site i).1) (site i).2),
             (fun j : Fin q => decide (((mask j).filter (fun a => base (x a.1) a.2)).card % 2 = 1))))) ↔
        n*s ≤ q := by
  intro k hk W ix add mix rot chi d ini fin u v L base other diff z keys s hs hsk hT hK hinj n q m
  constructor
  · rintro ⟨site, mask, hI⟩
    have hcT : Fintype.card {x : W // diff x = diff z} = 2 ^ s := by
      rw [Fintype.card_subtype]; exact hT
    have gi : Function.Injective (fun (t : Fin n → {x : W // diff x = diff z}) (j : Fin q) =>
        decide (((mask j).filter (fun a => base ((t a.1).1) a.2)).card % 2 = 1)) := by
      intro t t' h
      have h2 := @hI (fun a => (t a).1) (fun a => (t' a).1) (by
        simp only [Prod.mk.injEq]
        refine ⟨?_, h⟩
        funext i
        rw [(t _).2, (t' _).2])
      funext a
      exact Subtype.ext (congrFun h2 a)
    have h3 := Fintype.card_le_of_injective _ gi
    rw [Fintype.card_fun, Fintype.card_fun, hcT, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_bool, ← pow_mul] at h3
    have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
    rw [mul_comm]
    exact h4
  · intro hq
    obtain ⟨c, J, hCJ⟩ := PEqualNP.Outside.L_meta_41628.mid k s hk (fun i => ix (i.val+1))
      (fun i => ix (i.val+2)) L (rot fin)
      (fun x y => funext (fun i => PEqualNP.Outside.L_meta_41628.bL _ _ _ _ _ _))
      (fun _ _ => rfl) (mix d u) (mix d v) hT hK hinj
    exact PEqualNP.Outside.L_meta_41628.asm k s n q base diff c J hCJ hq
