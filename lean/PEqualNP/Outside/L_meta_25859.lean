import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25859_aux

private lemma rot_inv_idx {k : ℕ} (hk : 0 < k) (m : ℕ) (i : Fin k) :
    ((i.val + k - (k - m % k) % k) % k + k - m % k) % k = i.val := by
  have hr : m % k < k := Nat.mod_lt m hk
  by_cases hm : m % k = 0
  · simp only [hm, Nat.sub_zero, Nat.mod_self, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i.isLt]
  · have hmod1 : (k - m % k) % k = k - m % k := Nat.mod_eq_of_lt (by omega)
    rw [hmod1]
    have h1 : i.val + k - (k - m % k) = i.val + m % k := by omega
    rw [h1]
    by_cases hlt : i.val + m % k < k
    · rw [Nat.mod_eq_of_lt hlt]
      have h2 : i.val + m % k + k - m % k = i.val + k := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    · have hmod2 : (i.val + m % k) % k = i.val + m % k - k := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hmod2]
      have h2 : i.val + m % k - k + k - m % k = i.val := by omega
      rw [h2, Nat.mod_eq_of_lt i.isLt]

end PEqualNP.Outside.L_meta_25859_aux

theorem PEqualNP.Outside.L_meta_25859 :
    ∀ (k d s : ℕ) (hk : 0 < k),
      let F := ZMod 2
      let W := Fin k → F
      let ix := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
      let rot := fun (n : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - n % k))
      let mix := fun (x : W) (i : Fin k) =>
        x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))
      let layer := fun (x : W) (i : Fin k) =>
        mix x i + (1 + mix x (ix (i.val + 1))) * mix x (ix (i.val + 2))
      let polar := fun (x y : W) (i : Fin k) =>
        mix x (ix (i.val + 1)) * mix y (ix (i.val + 2)) + mix x (ix (i.val + 2)) * mix y (ix (i.val + 1))
      ∀ (start : ℕ) (feed : ℕ → ℕ) (c : ℕ → W) (shift : Fin s → W),
        let state := fun (sched : ℕ → W) (name key : W) (t : ℕ) =>
          Nat.rec (motive := fun _ => W) (rot start key + name) (fun j x => layer x + rot (feed j) key + sched j) t
        ∀ (r t : ℕ), t + 2 ≤ r → ∀ (name : W) (path : ℕ → Fin s → W),
          let fits := fun (w : W) => ∀ j ≤ r, ∀ p,
            state c name (w + shift p) j - state c name w j = path j p
          let pool := fun (j : ℕ) => (Finset.univ : Finset W).filter (fun x =>
            ∀ p, layer (x + path j p) - layer x + rot (feed j) (shift p) = path (j + 1) p)
          let dimension := fun (j : ℕ) => Module.finrank F (Submodule.span F
            {x : W | ∀ p, polar x (path j p) = 0})
          let candidates := (pool t).biUnion (fun x => (pool (t + 1)).image (fun y =>
            rot (k - (feed t) % k) (y - layer x - c t)))
          (Finset.univ.filter fits = candidates.filter fits) ∧
            candidates.card ≤ 2 ^ (dimension t + dimension (t + 1)) := by
  intro k d s hk F W ix rot mix layer polar start feed c shift state r t htr name path
    fits pool dimension candidates
  have hrot_add : ∀ (n : ℕ) (a b : W), rot n (a + b) = rot n a + rot n b := fun n a b => by
    funext i; rfl
  have hrot_inv : ∀ (m : ℕ) (x : W), rot (k - m % k) (rot m x) = x := fun m x => by
    funext i
    show x (ix ((ix (i.val + k - (k - m % k) % k)).val + k - m % k)) = x i
    congr 1
    exact Fin.ext (PEqualNP.Outside.L_meta_25859_aux.rot_inv_idx hk m i)
  have hmix_zero : mix 0 = 0 := by
    funext i; show (0 : F) + 0 + 0 = 0; ring
  have hmix_add : ∀ a b : W, mix (a + b) = mix a + mix b := fun a b => by
    funext i
    show (a i + b i) + (a (ix (i.val + d)) + b (ix (i.val + d))) +
      (a (ix (i.val + k - d % k)) + b (ix (i.val + k - d % k))) =
      (a i + a (ix (i.val + d)) + a (ix (i.val + k - d % k))) +
      (b i + b (ix (i.val + d)) + b (ix (i.val + k - d % k)))
    ring
  have hmix_sub : ∀ a b : W, mix (a - b) = mix a - mix b := fun a b => by
    funext i
    show (a i - b i) + (a (ix (i.val + d)) - b (ix (i.val + d))) +
      (a (ix (i.val + k - d % k)) - b (ix (i.val + k - d % k))) =
      (a i + a (ix (i.val + d)) + a (ix (i.val + k - d % k))) -
      (b i + b (ix (i.val + d)) + b (ix (i.val + k - d % k)))
    ring
  have hmix_smul : ∀ (a : F) (x : W), mix (a • x) = a • mix x := fun a x => by
    funext i
    show (a * x i) + (a * x (ix (i.val + d))) + (a * x (ix (i.val + k - d % k))) =
      a * (x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k)))
    ring
  have hpolar_zero : ∀ y : W, polar 0 y = 0 := fun y => by
    funext i; simp [polar, hmix_zero]
  have hpolar_add : ∀ a b y : W, polar (a + b) y = polar a y + polar b y := fun a b y => by
    funext i; simp only [polar, hmix_add, Pi.add_apply]; ring
  have hpolar_smul : ∀ (a : F) (x y : W), polar (a • x) y = a • polar x y := fun a x y => by
    funext i; simp only [polar, hmix_smul, Pi.smul_apply, smul_eq_mul]; ring
  have hlayer_diff : ∀ u v : W, layer (u + v) - layer u = layer v + polar u v := fun u v => by
    funext i
    simp only [layer, polar, hmix_add, Pi.sub_apply, Pi.add_apply]
    ring
  have hpolar_diff : ∀ x x0 v : W,
      (layer (x + v) - layer x) - (layer (x0 + v) - layer x0) = polar (x - x0) v := fun x x0 v => by
    rw [hlayer_diff x v, hlayer_diff x0 v]
    funext i
    simp only [polar, hmix_sub, Pi.sub_apply, Pi.add_apply]
    ring
  have hstate_succ : ∀ (key : W) (j : ℕ),
      state c name key (j + 1) = layer (state c name key j) + rot (feed j) key + c j := fun _ _ => rfl
  have hconj1 : Finset.univ.filter fits = candidates.filter fits := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hw
      refine ⟨?_, hw⟩
      have hpool_mem : ∀ j, j + 1 ≤ r → state c name w j ∈ pool j := by
        intro j hjr
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p => ?_⟩
        have hj : state c name (w + shift p) j = state c name w j + path j p := by
          have := hw j (by omega) p
          exact eq_add_of_sub_eq' this
        have hj1 := hw (j + 1) hjr p
        rw [hstate_succ (w + shift p) j, hstate_succ w j, hj, hrot_add] at hj1
        calc layer (state c name w j + path j p) - layer (state c name w j) + rot (feed j) (shift p)
            = (layer (state c name w j + path j p) + (rot (feed j) w + rot (feed j) (shift p)) + c j) -
              (layer (state c name w j) + rot (feed j) w + c j) := by abel
          _ = path (j + 1) p := hj1
      have hxt : state c name w t ∈ pool t := hpool_mem t (by omega)
      have hyt : state c name w (t + 1) ∈ pool (t + 1) := hpool_mem (t + 1) htr
      refine Finset.mem_biUnion.mpr ⟨state c name w t, hxt, Finset.mem_image.mpr ⟨state c name w (t + 1), hyt, ?_⟩⟩
      have hsub : state c name w (t + 1) - layer (state c name w t) - c t = rot (feed t) w := by
        rw [hstate_succ w t]; abel
      rw [hsub]
      exact hrot_inv (feed t) w
    · exact fun h => h.2
  have hpool_card : ∀ j : ℕ, (pool j).card ≤ 2 ^ dimension j := by
    intro j
    by_cases hne : (pool j).Nonempty
    · obtain ⟨x0, hx0⟩ := hne
      have hx0' : ∀ p, layer (x0 + path j p) - layer x0 + rot (feed j) (shift p) = path (j + 1) p :=
        (Finset.mem_filter.mp hx0).2
      let K : Submodule F W :=
        { carrier := {x : W | ∀ p, polar x (path j p) = 0}
          zero_mem' := fun p => hpolar_zero (path j p), add_mem' := fun ha hb p => by rw [hpolar_add, ha p, hb p, add_zero]
          smul_mem' := fun a _ hx p => by rw [hpolar_smul, hx p, smul_zero] }
      have hdim : dimension j = Module.finrank F K := by
        change Module.finrank F (Submodule.span F (K : Set W)) = Module.finrank F K
        rw [Submodule.span_eq K]
      have hmemK : ∀ x ∈ pool j, x - x0 ∈ K := by
        intro x hx p
        have hx' := (Finset.mem_filter.mp hx).2 p
        have h0 := hx0' p
        rw [← hpolar_diff x x0 (path j p)]
        calc (layer (x + path j p) - layer x) - (layer (x0 + path j p) - layer x0)
            = (layer (x + path j p) - layer x + rot (feed j) (shift p)) -
              (layer (x0 + path j p) - layer x0 + rot (feed j) (shift p)) := by abel
          _ = path (j + 1) p - path (j + 1) p := by rw [hx', h0]
          _ = 0 := sub_self _
      classical
      have hcard_le : (pool j).card ≤ Fintype.card K := by
        have hle := Finset.card_le_card_of_injOn (fun x => x - x0)
          (fun x hx => by
            show x - x0 ∈ (Finset.univ : Finset K).image Subtype.val
            exact Finset.mem_image.mpr ⟨⟨x - x0, hmemK x hx⟩, Finset.mem_univ _, rfl⟩)
          (fun x1 _ x2 _ heq => sub_left_injective heq)
        exact le_trans hle (le_trans Finset.card_image_le (by simp))
      have hcardK : Fintype.card K = 2 ^ dimension j := by
        rw [hdim, Module.card_eq_pow_finrank (K := F) (V := K)]
        simp [F]
      rw [← hcardK]
      exact hcard_le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  have hconj2 : candidates.card ≤ 2 ^ (dimension t + dimension (t + 1)) := by
    have h1 : candidates.card ≤ (pool t).card * (pool (t + 1)).card := by
      calc candidates.card
          ≤ ∑ x ∈ pool t, ((pool (t + 1)).image (fun y => rot (k - (feed t) % k) (y - layer x - c t))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ pool t, (pool (t + 1)).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ = (pool t).card * (pool (t + 1)).card := by simp
    calc candidates.card
        ≤ (pool t).card * (pool (t + 1)).card := h1
      _ ≤ 2 ^ dimension t * 2 ^ dimension (t + 1) := Nat.mul_le_mul (hpool_card t) (hpool_card (t + 1))
      _ = 2 ^ (dimension t + dimension (t + 1)) := (pow_add 2 (dimension t) (dimension (t + 1))).symm
  exact ⟨hconj1, hconj2⟩
