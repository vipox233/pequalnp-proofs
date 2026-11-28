import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Choose

namespace PEqualNP.Outside.L_lib_748_aux

-- Lower bound (restrict to the all-zero transcript and count sites).

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  obtain ⟨v, hv⟩ := a
  rcases v with _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    have hv' : v + 2 < 2 := hv
    omega

theorem zmod2_polar (a1 b1 a2 b2 a3 b3 : ZMod 2) (h1 : a1 ≠ 0) (h2 : b2 ≠ 0) (h3 : a3 ≠ b3)
    (e1 : a1 * b2 + a2 * b1 = 0) (e2 : a1 * b3 + a3 * b1 = 0) : False := by
  rcases zmod2_cases a1 with rfl | rfl
  · exact h1 rfl
  rcases zmod2_cases b2 with rfl | rfl
  · exact h2 rfl
  rcases zmod2_cases a2 with rfl | rfl <;> rcases zmod2_cases b1 with rfl | rfl <;>
    rcases zmod2_cases a3 with rfl | rfl <;> rcases zmod2_cases b3 with rfl | rfl <;>
    first
    | exact h3 rfl
    | exact absurd e1 (by decide)
    | exact absurd e2 (by decide)

theorem dep_of_polar {V : Type} (K : V → Prop) (α β : V → ZMod 2)
    (hB : ∀ u, K u → ∀ v, K v → α u * β v + α v * β u = 0) :
    (∀ x, K x → α x = 0) ∨ (∀ x, K x → β x = 0) ∨ (∀ x, K x → α x = β x) := by
  by_contra hne
  push_neg at hne
  obtain ⟨⟨x1, hx1, h1⟩, ⟨x2, hx2, h2⟩, ⟨x3, hx3, h3⟩⟩ := hne
  exact zmod2_polar (α x1) (β x1) (α x2) (β x2) (α x3) (β x3) h1 h2 h3
    (hB x1 hx1 x2 hx2) (hB x1 hx1 x3 hx3)

theorem polar_of_affine {n : ℕ} (K : (Fin n → ZMod 2) → Prop)
    (hadd : ∀ u v, K u → K v → K (u + v)) (h0 : K 0) (α β : (Fin n → ZMod 2) → ZMod 2)
    (hα : ∀ u v, α (u + v) = α u + α v) (hβ : ∀ u v, β (u + v) = β u + β v) (hα0 : α 0 = 0)
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (c : ZMod 2)
    (hf : ∀ x, K x → α x * β x = L x + c) :
    ∀ u, K u → ∀ v, K v → α u * β v + α v * β u = 0 := by
  intro u hu v hv
  have h1 := hf (u + v) (hadd u v hu hv)
  have h2 := hf u hu
  have h3 := hf v hv
  have h4 := hf 0 h0
  rw [hα, hβ, map_add] at h1
  rw [hα0, map_zero] at h4
  linear_combination h1 - h2 - h3 + h4

def yv (h : ℕ) (x : Fin (h+4) → ZMod 2) (k : ℕ) : ZMod 2 := x (Fin.ofNat (h+4) k)

theorem yv_add (h : ℕ) (u v : Fin (h+4) → ZMod 2) (k : ℕ) :
    yv h (u + v) k = yv h u k + yv h v k := rfl

theorem yv_zero (h : ℕ) (k : ℕ) : yv h 0 k = 0 := rfl

theorem foldl_zero {d : ℕ} (g : Fin d → ℕ → ZMod 2) (hg : ∀ j, g j 0 = 0) (l : List (Fin d)) :
    l.foldl (fun t j => 2 * t + (if g j t = 0 then 0 else 1)) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have e : 2 * 0 + (if g j 0 = 0 then 0 else 1) = (0 : ℕ) := by rw [hg j, if_pos rfl]
    calc List.foldl (fun t j => 2 * t + (if g j t = 0 then 0 else 1)) 0 (j :: l)
        = List.foldl (fun t j => 2 * t + (if g j t = 0 then 0 else 1))
            (2 * 0 + (if g j 0 = 0 then 0 else 1)) l := rfl
      _ = List.foldl (fun t j => 2 * t + (if g j t = 0 then 0 else 1)) 0 l := by rw [e]
      _ = 0 := ih

theorem fo_unique (h : ℕ) (Kp : (Fin (h+4) → ZMod 2) → Prop)
    (hF2 : ∀ k, 3 ≤ k → k ≤ h + 2 →
      (∀ x, Kp x → yv h x k = 0) ∨ (∀ x, Kp x → yv h x (k+1) = 0) ∨
      (∀ x, Kp x → yv h x k = yv h x (k+1)))
    (hT2 : ∀ p, 4 ≤ p → p ≤ h → (∀ x, Kp x → yv h x (p-1) = 0) →
      (∀ x, Kp x → yv h x (p+1) = 0) →
      (∀ x, Kp x → yv h x p = 0) ∨ (∀ x, Kp x → yv h x (p+2) = 0) ∨
      (∀ x, Kp x → yv h x p = yv h x (p+2)))
    (p p' : ℕ) (hp1 : 3 ≤ p) (hp2 : p ≤ h + 1) (hpZ : ¬ ∀ x, Kp x → yv h x p = 0)
    (hpE : ∀ k, 3 ≤ k → k < p → ¬ ∀ x, Kp x → yv h x k = yv h x p)
    (hq1 : 3 ≤ p') (hq2 : p' ≤ h + 1) (hqZ : ¬ ∀ x, Kp x → yv h x p' = 0)
    (hqE : ∀ k, 3 ≤ k → k < p' → ¬ ∀ x, Kp x → yv h x k = yv h x p')
    (hlt : p < p') (hblk : (p - 2) / 3 = (p' - 2) / 3) : False := by
  have hcase : p' = p + 1 ∨ (p' = p + 2 ∧ 4 ≤ p) := by omega
  rcases hcase with rfl | ⟨rfl, hp4⟩
  · rcases hF2 p hp1 (by omega) with hz | hz | he
    · exact hpZ hz
    · exact hqZ hz
    · exact hqE p hp1 (by omega) he
  · have hz1 : ∀ x, Kp x → yv h x (p+1) = 0 := by
      rcases hF2 p hp1 (by omega) with hz | hz | he
      · exact (hpZ hz).elim
      · exact hz
      · have hF' := hF2 (p+1) (by omega) (by omega)
        rw [show p + 1 + 1 = p + 2 by omega] at hF'
        rcases hF' with hz' | hz' | he'
        · exact hz'
        · exact (hqZ hz').elim
        · exact (hqE p hp1 (by omega) (fun x hx => (he x hx).trans (he' x hx))).elim
    have hz0 : ∀ x, Kp x → yv h x (p-1) = 0 := by
      have hF := hF2 (p-1) (by omega) (by omega)
      rw [show p - 1 + 1 = p by omega] at hF
      rcases hF with hz | hz | he
      · exact hz
      · exact (hpZ hz).elim
      · exact (hpE (p-1) (by omega) (by omega) he).elim
    rcases hT2 p hp4 (by omega) hz0 hz1 with hz | hz | he
    · exact hpZ hz
    · exact hqZ hz
    · exact hqE p hp1 (by omega) he

theorem site_exists (h : ℕ) (Kp : (Fin (h+4) → ZMod 2) → Prop)
    (hF2 : ∀ k, 3 ≤ k → k ≤ h + 2 →
      (∀ x, Kp x → yv h x k = 0) ∨ (∀ x, Kp x → yv h x (k+1) = 0) ∨
      (∀ x, Kp x → yv h x k = yv h x (k+1)))
    (hT2 : ∀ p, 4 ≤ p → p ≤ h → (∀ x, Kp x → yv h x (p-1) = 0) →
      (∀ x, Kp x → yv h x (p+1) = 0) →
      (∀ x, Kp x → yv h x p = 0) ∨ (∀ x, Kp x → yv h x (p+2) = 0) ∨
      (∀ x, Kp x → yv h x p = yv h x (p+2))) :
    ∃ site : Fin (6 + (h-1)/3) → Fin (h+4), ∀ x, Kp x → (∀ c, x (site c) = 0) → x = 0 := by
  have hsite : ∀ c : Fin (6 + (h-1)/3), ∃ s : Fin (h+4),
      (c.val < 3 → s.val = c.val) ∧ (c.val = 3 → s.val = h + 2) ∧ (c.val = 4 → s.val = h + 3) ∧
      (5 ≤ c.val → ∀ p, 3 ≤ p → p ≤ h + 1 → (¬ ∀ x, Kp x → yv h x p = 0) →
        (∀ k, 3 ≤ k → k < p → ¬ ∀ x, Kp x → yv h x k = yv h x p) →
        (p - 2) / 3 = c.val - 5 → s.val = p) := by
    intro c
    rcases (by omega : c.val < 3 ∨ c.val = 3 ∨ c.val = 4 ∨ 5 ≤ c.val) with h3 | h3 | h3 | h5
    · exact ⟨⟨c.val, by omega⟩, fun _ => rfl, fun h' => absurd h' (by omega),
        fun h' => absurd h' (by omega), fun h' => absurd h' (by omega)⟩
    · exact ⟨⟨h + 2, by omega⟩, fun h' => absurd h' (by omega), fun _ => rfl,
        fun h' => absurd h' (by omega), fun h' => absurd h' (by omega)⟩
    · exact ⟨⟨h + 3, by omega⟩, fun h' => absurd h' (by omega), fun h' => absurd h' (by omega),
        fun _ => rfl, fun h' => absurd h' (by omega)⟩
    · by_cases hex : ∃ p, 3 ≤ p ∧ p ≤ h + 1 ∧ (¬ ∀ x, Kp x → yv h x p = 0) ∧
          (∀ k, 3 ≤ k → k < p → ¬ ∀ x, Kp x → yv h x k = yv h x p) ∧ (p - 2) / 3 = c.val - 5
      · obtain ⟨p, hp1, hp2, hpZ, hpE, hpb⟩ := hex
        refine ⟨⟨p, by omega⟩, fun h' => absurd h' (by omega), fun h' => absurd h' (by omega),
          fun h' => absurd h' (by omega), fun _ p' hq1 hq2 hqZ hqE hqb => ?_⟩
        show p = p'
        rcases lt_trichotomy p p' with hlt | heq | hgt
        · exact (fo_unique h Kp hF2 hT2 p p' hp1 hp2 hpZ hpE hq1 hq2 hqZ hqE hlt
            (by omega)).elim
        · exact heq
        · exact (fo_unique h Kp hF2 hT2 p' p hq1 hq2 hqZ hqE hp1 hp2 hpZ hpE hgt
            (by omega)).elim
      · exact ⟨⟨0, by omega⟩, fun h' => absurd h' (by omega), fun h' => absurd h' (by omega),
          fun h' => absurd h' (by omega),
          fun _ p' hq1 hq2 hqZ hqE hqb => (hex ⟨p', hq1, hq2, hqZ, hqE, hqb⟩).elim⟩
  choose site hs using hsite
  refine ⟨site, fun x hx hz => ?_⟩
  have hval : ∀ k, k < h + 4 → ∀ c, (site c).val = k → yv h x k = 0 := by
    intro k hk c hc
    have e : site c = Fin.ofNat (h+4) k := by
      apply Fin.ext
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt hk, hc]
    show x (Fin.ofNat (h+4) k) = 0
    rw [← e]
    exact hz c
  have hwin : ∀ k, 3 ≤ k → k ≤ h + 1 → yv h x k = 0 := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih hk1 hk2
    by_cases hZ : ∀ y, Kp y → yv h y k = 0
    · exact hZ x hx
    · by_cases hfirst : ∀ k', 3 ≤ k' → k' < k → ¬ ∀ y, Kp y → yv h y k' = yv h y k
      · have hcb : 5 + (k - 2) / 3 < 6 + (h - 1) / 3 := by omega
        exact hval k (by omega) ⟨5 + (k - 2) / 3, hcb⟩
          ((hs ⟨5 + (k - 2) / 3, hcb⟩).2.2.2 (by show 5 ≤ 5 + (k - 2) / 3; omega) k hk1 hk2 hZ
            hfirst (by show (k - 2) / 3 = 5 + (k - 2) / 3 - 5; omega))
      · push_neg at hfirst
        obtain ⟨k', hk'1, hk'2, hE⟩ := hfirst
        rw [← hE x hx]
        exact ih k' hk'2 hk'1 (by omega)
  funext s
  have hsl := s.isLt
  have hs' : yv h x s.val = 0 := by
    rcases (by omega : s.val < 3 ∨ (3 ≤ s.val ∧ s.val ≤ h + 1) ∨ s.val = h + 2 ∨
        s.val = h + 3) with h1 | ⟨h1, h2⟩ | h1 | h1
    · exact hval s.val hsl ⟨s.val, by omega⟩ ((hs ⟨s.val, by omega⟩).1 h1)
    · exact hwin s.val h1 h2
    · exact hval s.val hsl ⟨3, by omega⟩ (((hs ⟨3, by omega⟩).2.1 rfl).trans h1.symm)
    · exact hval s.val hsl ⟨4, by omega⟩ (((hs ⟨4, by omega⟩).2.2.1 rfl).trans h1.symm)
  have e2 : yv h x s.val = x s := by
    show x (Fin.ofNat (h+4) s.val) = x s
    rw [Fin.ofNat_val_eq_self]
  exact e2.symm.trans hs'

theorem dim_bound (n d m : ℕ) (q : Fin d → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (site : Fin m → Fin n)
    (hdet : ∀ x : Fin n → ZMod 2, (∀ j, q j x = 0) → (∀ c, x (site c) = 0) → x = 0) :
    n ≤ d + m := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi q)
  have hr := Submodule.finrank_le (LinearMap.range (LinearMap.pi q))
  rw [Module.finrank_fin_fun] at hrn
  rw [Module.finrank_fin_fun] at hr
  have hinj : Function.Injective
      ((LinearMap.funLeft (ZMod 2) (ZMod 2) site).comp
        (LinearMap.ker (LinearMap.pi q)).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hyK : ∀ j, q j (y : Fin n → ZMod 2) = 0 := by
      intro j
      have h1 := y.2
      rw [LinearMap.mem_ker] at h1
      have h2 := congrFun h1 j
      rw [LinearMap.pi_apply] at h2
      exact h2
    have hyz : (y : Fin n → ZMod 2) = 0 := by
      apply hdet _ hyK
      intro c
      have h3 := congrFun hy c
      rw [LinearMap.comp_apply, LinearMap.funLeft_apply] at h3
      exact h3
    exact (Submodule.coe_eq_zero).mp hyz
  have hk := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun] at hk
  omega

theorem core (h : ℕ) (hh : 3 ≤ h) (d : ℕ)
    (q : Fin d → ((Fin (h+4) → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (line' : (Fin (h+4) → ZMod 2) → Bool → Fin h → ZMod 2)
    (run : (Fin (h+4) → ZMod 2) → ℕ)
    (readout : ℕ → Bool → Fin h → ((Fin (h+4) → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (bias : ℕ → Bool → Fin h → ZMod 2)
    (hrun : ∀ x, (∀ j, q j x = 0) → run x = 0)
    (hlineT : ∀ x i, line' x true i = (yv h x i.val + yv h x (i.val+1) + yv h x (i.val+2)) *
        (yv h x (i.val+1) + yv h x (i.val+2) + yv h x (i.val+3)))
    (hlineF : ∀ x i, line' x false i = yv h x (i.val+3) * yv h x (i.val+4))
    (hyp : ∀ x b i, line' x b i = readout (run x) b i x + bias (run x) b i) :
    h - 2 - (h-1)/3 ≤ d := by
  have hadd : ∀ u v : Fin (h+4) → ZMod 2, (∀ j, q j u = 0) → (∀ j, q j v = 0) →
      ∀ j, q j (u + v) = 0 := by
    intro u v hu hv j
    rw [map_add, hu j, hv j, add_zero]
  have h0 : ∀ j, q j (0 : Fin (h+4) → ZMod 2) = 0 := fun j => map_zero (q j)
  have haff : ∀ x, (∀ j, q j x = 0) → ∀ b i, line' x b i = readout 0 b i x + bias 0 b i := by
    intro x hx b i
    rw [hyp x b i, hrun x hx]
  have hF2 : ∀ k, 3 ≤ k → k ≤ h + 2 →
      (∀ x, (∀ j, q j x = 0) → yv h x k = 0) ∨ (∀ x, (∀ j, q j x = 0) → yv h x (k+1) = 0) ∨
      (∀ x, (∀ j, q j x = 0) → yv h x k = yv h x (k+1)) := by
    intro k hk1 hk2
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 3 := ⟨k - 3, by omega⟩
    have hi : i < h := by omega
    exact dep_of_polar (fun x => ∀ j, q j x = 0) (fun x => yv h x (i+3)) (fun x => yv h x (i+3+1))
      (polar_of_affine (fun x => ∀ j, q j x = 0) hadd h0 (fun x => yv h x (i+3))
        (fun x => yv h x (i+3+1)) (fun u v => rfl) (fun u v => rfl) rfl
        (readout 0 false ⟨i, hi⟩) (bias 0 false ⟨i, hi⟩)
        (fun x hx => (hlineF x ⟨i, hi⟩).symm.trans (haff x hx false ⟨i, hi⟩)))
  have hTpolar : ∀ i, i < h → ∀ u, (∀ j, q j u = 0) → ∀ v, (∀ j, q j v = 0) →
      (yv h u i + yv h u (i+1) + yv h u (i+2)) * (yv h v (i+1) + yv h v (i+2) + yv h v (i+3)) +
      (yv h v i + yv h v (i+1) + yv h v (i+2)) * (yv h u (i+1) + yv h u (i+2) + yv h u (i+3))
        = 0 := by
    intro i hi
    exact polar_of_affine (fun x => ∀ j, q j x = 0) hadd h0
      (fun x => yv h x i + yv h x (i+1) + yv h x (i+2))
      (fun x => yv h x (i+1) + yv h x (i+2) + yv h x (i+3))
      (fun u v => by simp only [yv_add]; ring)
      (fun u v => by simp only [yv_add]; ring)
      (by simp only [yv_zero, add_zero])
      (readout 0 true ⟨i, hi⟩) (bias 0 true ⟨i, hi⟩)
      (fun x hx => (hlineT x ⟨i, hi⟩).symm.trans (haff x hx true ⟨i, hi⟩))
  have hT2 : ∀ p, 4 ≤ p → p ≤ h →
      (∀ x, (∀ j, q j x = 0) → yv h x (p-1) = 0) → (∀ x, (∀ j, q j x = 0) → yv h x (p+1) = 0) →
      (∀ x, (∀ j, q j x = 0) → yv h x p = 0) ∨ (∀ x, (∀ j, q j x = 0) → yv h x (p+2) = 0) ∨
      (∀ x, (∀ j, q j x = 0) → yv h x p = yv h x (p+2)) := by
    intro p hp4 hph hz0 hz1
    obtain ⟨i, rfl⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
    rw [show i + 1 - 1 = i by omega] at hz0
    rw [show i + 1 + 1 = i + 2 by omega] at hz1
    rw [show i + 1 + 2 = i + 3 by omega]
    refine dep_of_polar (fun x => ∀ j, q j x = 0) (fun x => yv h x (i+1)) (fun x => yv h x (i+3)) ?_
    intro u hu v hv
    have key := hTpolar i (by omega) u hu v hv
    rw [hz0 u hu, hz0 v hv, hz1 u hu, hz1 v hv] at key
    have two : (2 : ZMod 2) = 0 := by decide
    show yv h u (i+1) * yv h v (i+3) + yv h v (i+1) * yv h u (i+3) = 0
    linear_combination key - (yv h u (i+1) * yv h v (i+1)) * two
  obtain ⟨site, hdet⟩ := site_exists h (fun x => ∀ j, q j x = 0) hF2 hT2
  have hb := dim_bound (h+4) d (6 + (h-1)/3) q site hdet
  omega

theorem lower_main : ∀ h : ℕ, 3 ≤ h →
  let F := ZMod 2
  let admits := fun (n : ℕ) (target : (Fin n → F) → Bool → Fin h → F) (d : ℕ) =>
    let W := Fin n → F
    let D := W →ₗ[F] F
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun t j => 2*t + (if ask j t x = 0 then 0 else 1)) (0 : ℕ)
    ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin h → D)
      (bias : ℕ → Bool → Fin h → F),
      ∀ x b i, target x b i = readout (run ask x) b i x + bias (run ask x) b i
  let line := fun (y : Fin (h+4) → F) (b : Bool) (i : Fin h) =>
    let a := fun j : ℕ => y (Fin.ofNat (h+4) (i.val+j))
    if b then (a 0 + a 1 + a 2) * (a 1 + a 2 + a 3) else a 3 * a 4
  ∀ d : ℕ, admits (h+4) line d → h-2-(h-1)/3 ≤ d := by
  intro h hh
  dsimp only
  intro d hadm
  obtain ⟨ask, readout, bias, hyp⟩ := hadm
  refine core h hh d (fun j => ask j 0) _ _ readout bias ?_ ?_ ?_ hyp
  · intro x hx
    exact foldl_zero (fun j t => ask j t x) hx (List.finRange d)
  · intro x i
    rfl
  · intro x i
    rfl


-- Upper bound (a nonadaptive scheme of h+4-(h+4)/3 questions) and the glue iff_of_lower.

noncomputable def pr (h k : ℕ) : (Fin (h+4) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj (Fin.ofNat (h+4) k)

theorem pr_apply (h k : ℕ) (y : Fin (h+4) → ZMod 2) : pr h k y = y (Fin.ofNat (h+4) k) := by
  unfold pr
  exact LinearMap.proj_apply _ _

noncomputable def qn (h j : ℕ) : (Fin (h+4) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  if j % 2 = 0 then pr h (3 * (j / 2)) else pr h (3 * (j / 2) + 1) + pr h (3 * (j / 2) + 2)

theorem qn_even (h q : ℕ) (hq : q % 3 = 0) : qn h (2 * (q / 3)) = pr h q := by
  have e1 : 2 * (q / 3) % 2 = 0 := by omega
  have e2 : 2 * (q / 3) / 2 = q / 3 := by omega
  have e3 : 3 * (q / 3) = q := by omega
  rw [qn, ite_eq_left e1, e2, e3]

theorem qn_odd (h q : ℕ) (hq : q % 3 = 1) :
    qn h (2 * (q / 3) + 1) = pr h q + pr h (q + 1) := by
  have e1 : ¬ ((2 * (q / 3) + 1) % 2 = 0) := by omega
  have e2 : (2 * (q / 3) + 1) / 2 = q / 3 := by omega
  have e3 : 3 * (q / 3) + 1 = q := by omega
  have e4 : 3 * (q / 3) + 2 = q + 1 := by omega
  rw [qn, ite_eq_right e1, e2, e3, e4]

noncomputable def runq (h d : ℕ) (x : Fin (h+4) → ZMod 2) : ℕ :=
  (List.finRange d).foldl (fun t j => 2*t + (if qn h j.val x = 0 then 0 else 1)) 0

noncomputable def ro (h : ℕ) (x0 : Fin (h+4) → ZMod 2) (b : Bool) (i : Fin h) :
    (Fin (h+4) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  if b then
    (if i.val % 3 = 2 then
      (pr h (i.val+1) x0 + pr h (i.val+2) x0 + pr h (i.val+3) x0) •
        (pr h i.val + pr h (i.val+1) + pr h (i.val+2))
    else
      (pr h i.val x0 + pr h (i.val+1) x0 + pr h (i.val+2) x0) •
        (pr h (i.val+1) + pr h (i.val+2) + pr h (i.val+3)))
  else
    (if i.val % 3 = 0 then pr h (i.val+3) x0 • pr h (i.val+4)
    else if i.val % 3 = 1 then (1 + (pr h (i.val+3) x0 + pr h (i.val+4) x0)) • pr h (i.val+3)
    else pr h (i.val+4) x0 • pr h (i.val+3))

theorem fold_inj {α : Type} (l : List α) (f g : α → ℕ) (hf : ∀ a, f a < 2) (hg : ∀ a, g a < 2) :
    ∀ s t : ℕ, l.foldl (fun t j => 2 * t + f j) s = l.foldl (fun t j => 2 * t + g j) t →
      s = t ∧ ∀ a ∈ l, f a = g a := by
  induction l with
  | nil =>
    intro s t hst
    exact ⟨hst, fun a ha => by simp at ha⟩
  | cons a l ih =>
    intro s t hst
    simp only [List.foldl_cons] at hst
    obtain ⟨h1, h2⟩ := ih _ _ hst
    have h1' : 2 * s + f a = 2 * t + g a := h1
    have ha := hf a
    have hb := hg a
    refine ⟨by omega, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with hc | hc
    · subst hc
      omega
    · exact h2 c hc

theorem ite_lt2 (P : Prop) [Decidable P] : (if P then 0 else 1 : ℕ) < 2 := by
  split <;> omega

theorem bit_inj : ∀ u v : ZMod 2, (if u = 0 then 0 else 1 : ℕ) = (if v = 0 then 0 else 1) → u = v := by
  decide

theorem lemF0 : ∀ u v u0 : ZMod 2, u0 = u → u * v = u0 * v := by
  decide

theorem lemF1 : ∀ u v u0 v0 : ZMod 2, u0 + v0 = u + v → u * v = (1 + (u0 + v0)) * u := by
  decide

theorem lemF2 : ∀ u v v0 : ZMod 2, v0 = v → u * v = v0 * u := by
  decide

theorem lemT0 : ∀ a b c d a0 b0 c0 : ZMod 2, a0 = a → b0 + c0 = b + c →
    (a + b + c) * (b + c + d) = (a0 + b0 + c0) * (b + c + d) := by
  decide

theorem lemT1 : ∀ a b c d a0 b0 c0 : ZMod 2, a0 + b0 = a + b → c0 = c →
    (a + b + c) * (b + c + d) = (a0 + b0 + c0) * (b + c + d) := by
  decide

theorem lemT2 : ∀ a b c d b0 c0 d0 : ZMod 2, b0 = b → c0 + d0 = c + d →
    (a + b + c) * (b + c + d) = (b0 + c0 + d0) * (a + b + c) := by
  decide

theorem agree (h d : ℕ) (x x0 : Fin (h+4) → ZMod 2) (hx0 : runq h d x0 = runq h d x) :
    ∀ j, j < d → qn h j x0 = qn h j x := by
  intro j hj
  have key := (fold_inj (List.finRange d) (fun j : Fin d => if qn h j.val x0 = 0 then 0 else 1)
    (fun j : Fin d => if qn h j.val x = 0 then 0 else 1) (fun _ => ite_lt2 _) (fun _ => ite_lt2 _)
    0 0 hx0).2 ⟨j, hj⟩ (List.mem_finRange _)
  exact bit_inj _ _ key

theorem rep_spec (h d : ℕ) (x : Fin (h+4) → ZMod 2) :
    runq h d (Function.invFun (runq h d) (runq h d x)) = runq h d x :=
  Function.invFun_eq ⟨x, rfl⟩

theorem key0 (h : ℕ) (hh : 3 ≤ h) (x x0 : Fin (h+4) → ZMod 2)
    (hx0 : runq h (h+4-(h+4)/3) x0 = runq h (h+4-(h+4)/3) x) (b : Bool) (i : Fin h) :
    (if b then (x (Fin.ofNat (h+4) i.val) + x (Fin.ofNat (h+4) (i.val+1)) +
        x (Fin.ofNat (h+4) (i.val+2))) * (x (Fin.ofNat (h+4) (i.val+1)) +
        x (Fin.ofNat (h+4) (i.val+2)) + x (Fin.ofNat (h+4) (i.val+3)))
      else x (Fin.ofNat (h+4) (i.val+3)) * x (Fin.ofNat (h+4) (i.val+4))) =
      ro h x0 b i x + 0 := by
  have hqn := agree h (h+4-(h+4)/3) x x0 hx0
  have hE : ∀ q, q % 3 = 0 → 2 * (q / 3) < h+4-(h+4)/3 →
      x0 (Fin.ofNat (h+4) q) = x (Fin.ofNat (h+4) q) := by
    intro q h0 hb
    have e := hqn _ hb
    rw [qn_even h q h0, pr_apply, pr_apply] at e
    exact e
  have hO : ∀ q q', q % 3 = 1 → q' = q + 1 → 2 * (q / 3) + 1 < h+4-(h+4)/3 →
      x0 (Fin.ofNat (h+4) q) + x0 (Fin.ofNat (h+4) q') =
        x (Fin.ofNat (h+4) q) + x (Fin.ofNat (h+4) q') := by
    intro q q' h1 h2 hb
    subst h2
    have e := hqn _ hb
    simp only [qn_odd h q h1, LinearMap.add_apply, pr_apply] at e
    exact e
  have hi := i.isLt
  cases b with
  | false =>
    show x (Fin.ofNat (h+4) (i.val+3)) * x (Fin.ofNat (h+4) (i.val+4)) = ro h x0 false i x + 0
    rw [ro, ite_eq_right (show ¬ (false = true) by decide)]
    rcases (show i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 by omega) with hm | hm | hm
    · rw [ite_eq_left hm]
      simp only [LinearMap.smul_apply, smul_eq_mul, pr_apply, add_zero]
      exact lemF0 _ _ _ (hE (i.val+3) (by omega) (by omega))
    · rw [ite_eq_right (show ¬ (i.val % 3 = 0) by omega), ite_eq_left hm]
      simp only [LinearMap.smul_apply, smul_eq_mul, pr_apply, add_zero]
      exact lemF1 _ _ _ _ (hO (i.val+3) (i.val+4) (by omega) (by omega) (by omega))
    · rw [ite_eq_right (show ¬ (i.val % 3 = 0) by omega), ite_eq_right (show ¬ (i.val % 3 = 1) by omega)]
      simp only [LinearMap.smul_apply, smul_eq_mul, pr_apply, add_zero]
      exact lemF2 _ _ _ (hE (i.val+4) (by omega) (by omega))
  | true =>
    show (x (Fin.ofNat (h+4) i.val) + x (Fin.ofNat (h+4) (i.val+1)) +
        x (Fin.ofNat (h+4) (i.val+2))) * (x (Fin.ofNat (h+4) (i.val+1)) +
        x (Fin.ofNat (h+4) (i.val+2)) + x (Fin.ofNat (h+4) (i.val+3))) = ro h x0 true i x + 0
    rw [ro, ite_eq_left (rfl : true = true)]
    rcases (show i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 by omega) with hm | hm | hm
    · rw [ite_eq_right (show ¬ (i.val % 3 = 2) by omega)]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, pr_apply, add_zero]
      exact lemT0 _ _ _ _ _ _ _ (hE i.val hm (by omega))
        (hO (i.val+1) (i.val+2) (by omega) (by omega) (by omega))
    · rw [ite_eq_right (show ¬ (i.val % 3 = 2) by omega)]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, pr_apply, add_zero]
      exact lemT1 _ _ _ _ _ _ _ (hO i.val (i.val+1) hm (by omega) (by omega))
        (hE (i.val+2) (by omega) (by omega))
    · rw [ite_eq_left hm]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, pr_apply, add_zero]
      exact lemT2 _ _ _ _ _ _ _ (hE (i.val+1) (by omega) (by omega))
        (hO (i.val+2) (i.val+3) (by omega) (by omega) (by omega))

theorem upper : ∀ h : ℕ, 3 ≤ h →
  let F := ZMod 2
  let admits := fun (n : ℕ) (target : (Fin n → F) → Bool → Fin h → F) (d : ℕ) =>
    let W := Fin n → F
    let D := W →ₗ[F] F
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun t j => 2*t + (if ask j t x = 0 then 0 else 1)) (0 : ℕ)
    ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin h → D)
      (bias : ℕ → Bool → Fin h → F),
      ∀ x b i, target x b i = readout (run ask x) b i x + bias (run ask x) b i
  let line := fun (y : Fin (h+4) → F) (b : Bool) (i : Fin h) =>
    let a := fun j : ℕ => y (Fin.ofNat (h+4) (i.val+j))
    if b then (a 0 + a 1 + a 2) * (a 1 + a 2 + a 3) else a 3 * a 4
  admits (h+4) line (h+4-(h+4)/3) := by
  intro h hh
  dsimp only
  exact ⟨fun j _ => qn h j.val,
    fun t b i => ro h (Function.invFun (runq h (h+4-(h+4)/3)) t) b i,
    fun _ _ _ => 0,
    fun x b i => key0 h hh x (Function.invFun (runq h (h+4-(h+4)/3)) (runq h (h+4-(h+4)/3) x))
      (rep_spec h (h+4-(h+4)/3) x) b i⟩

theorem iff_of_lower (lower : ∀ h : ℕ, 3 ≤ h →
  let F := ZMod 2
  let admits := fun (n : ℕ) (target : (Fin n → F) → Bool → Fin h → F) (d : ℕ) =>
    let W := Fin n → F
    let D := W →ₗ[F] F
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun t j => 2*t + (if ask j t x = 0 then 0 else 1)) (0 : ℕ)
    ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin h → D)
      (bias : ℕ → Bool → Fin h → F),
      ∀ x b i, target x b i = readout (run ask x) b i x + bias (run ask x) b i
  let line := fun (y : Fin (h+4) → F) (b : Bool) (i : Fin h) =>
    let a := fun j : ℕ => y (Fin.ofNat (h+4) (i.val+j))
    if b then (a 0 + a 1 + a 2) * (a 1 + a 2 + a 3) else a 3 * a 4
  ∀ d : ℕ, admits (h+4) line d → h-2-(h-1)/3 ≤ d) :
  ∀ h : ℕ, 3 ≤ h →
  let F := ZMod 2
  let admits := fun (n : ℕ) (target : (Fin n → F) → Bool → Fin h → F) (d : ℕ) =>
    let W := Fin n → F
    let D := W →ₗ[F] F
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun t j => 2*t + (if ask j t x = 0 then 0 else 1)) (0 : ℕ)
    ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin h → D)
      (bias : ℕ → Bool → Fin h → F),
      ∀ x b i, target x b i = readout (run ask x) b i x + bias (run ask x) b i
  let line := fun (y : Fin (h+4) → F) (b : Bool) (i : Fin h) =>
    let a := fun j : ℕ => y (Fin.ofNat (h+4) (i.val+j))
    if b then (a 0 + a 1 + a 2) * (a 1 + a 2 + a 3) else a 3 * a 4
  (∀ d : ℕ, admits (h+4) line d → h-2-(h-1)/3 ≤ d) ∧
    admits (h+4) line (h+4-(h+4)/3) := by
  intro h hh
  exact ⟨lower h hh, upper h hh⟩


end PEqualNP.Outside.L_lib_748_aux

theorem PEqualNP.Outside.L_lib_748 : ∀ h : ℕ, 3 ≤ h →
  let F := ZMod 2
  let admits := fun (n : ℕ) (target : (Fin n → F) → Bool → Fin h → F) (d : ℕ) =>
    let W := Fin n → F
    let D := W →ₗ[F] F
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun t j => 2*t + (if ask j t x = 0 then 0 else 1)) (0 : ℕ)
    ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin h → D)
      (bias : ℕ → Bool → Fin h → F),
      ∀ x b i, target x b i = readout (run ask x) b i x + bias (run ask x) b i
  let line := fun (y : Fin (h+4) → F) (b : Bool) (i : Fin h) =>
    let a := fun j : ℕ => y (Fin.ofNat (h+4) (i.val+j))
    if b then (a 0 + a 1 + a 2) * (a 1 + a 2 + a 3) else a 3 * a 4
  (∀ d : ℕ, admits (h+4) line d → h-2-(h-1)/3 ≤ d) ∧
    admits (h+4) line (h+4-(h+4)/3) :=
  PEqualNP.Outside.L_lib_748_aux.iff_of_lower PEqualNP.Outside.L_lib_748_aux.lower_main
