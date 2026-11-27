import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25861_aux

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma vec_add_self {k : ℕ} (x : Fin k → ZMod 2) : x + x = 0 :=
  funext fun i => zmod2_add_self (x i)

private lemma vec_sub_eq_add {k : ℕ} (x y : Fin k → ZMod 2) : x - y = x + y :=
  funext fun i => zmod2_sub_eq_add (x i) (y i)

private lemma vec_add_eq_zero_iff {k : ℕ} (x y : Fin k → ZMod 2) : x + y = 0 ↔ y = x := by
  constructor
  · intro h
    have h1 := congrArg (fun z => x + z) h
    rw [add_zero, ← add_assoc, vec_add_self, zero_add] at h1
    exact h1
  · rintro rfl
    exact vec_add_self y

private def signZ (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

private lemma signZ_zero : signZ 0 = 1 := rfl

private lemma signZ_add (a b : ZMod 2) : signZ (a + b) = signZ a * signZ b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma signZ_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ZMod 2) :
    signZ (∑ i ∈ s, f i) = ∏ i ∈ s, signZ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [signZ_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, signZ_add, ih]

private lemma sum_signZ_dot {k : ℕ} (v : Fin k → ZMod 2) :
    ∑ u : Fin k → ZMod 2, signZ (dotProduct u v) = if v = 0 then (2 : ℤ) ^ k else 0 := by
  have hprod : ∑ u : Fin k → ZMod 2, signZ (dotProduct u v) =
      ∏ i : Fin k, ∑ a : ZMod 2, signZ (a * v i) := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro u _
    unfold dotProduct
    exact signZ_sum Finset.univ (fun i => u i * v i)
  rw [hprod]
  by_cases hv : v = 0
  · subst hv
    simp only [↓reduceIte]
    have hterm : ∀ i : Fin k, ∑ a : ZMod 2, signZ (a * (0 : Fin k → ZMod 2) i) = 2 := by
      intro i
      simp only [Pi.zero_apply]
      decide
    simp only [hterm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · simp only [hv, ↓reduceIte]
    have hex : ∃ i : Fin k, v i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv (funext hall)
    rcases hex with ⟨i0, hi0⟩
    apply Finset.prod_eq_zero (Finset.mem_univ i0)
    have hv1 : v i0 = 1 := by
      generalize v i0 = z at hi0 ⊢
      fin_cases z
      · exact absurd rfl hi0
      · rfl
    rw [hv1]
    decide

private lemma sum_signZ_tuple {k s : ℕ} (v : Fin s → Fin k → ZMod 2) :
    ∑ m : Fin s → Fin k → ZMod 2, signZ (∑ p : Fin s, dotProduct (m p) (v p)) =
      if (∀ p, v p = 0) then ((2 : ℤ) ^ k) ^ s else 0 := by
  have hprod : ∑ m : Fin s → Fin k → ZMod 2, signZ (∑ p : Fin s, dotProduct (m p) (v p)) =
      ∏ p : Fin s, ∑ u : Fin k → ZMod 2, signZ (dotProduct u (v p)) := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro m _
    exact signZ_sum Finset.univ (fun p => dotProduct (m p) (v p))
  rw [hprod]
  split_ifs with hv
  · have hterm : ∀ p : Fin s, ∑ u : Fin k → ZMod 2, signZ (dotProduct u (v p)) = (2 : ℤ) ^ k := by
      intro p
      rw [sum_signZ_dot, hv p]
      simp
    simp only [hterm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · push Not at hv
    rcases hv with ⟨p0, hp0⟩
    apply Finset.prod_eq_zero (Finset.mem_univ p0)
    rw [sum_signZ_dot]
    simp only [hp0, ↓reduceIte]

private lemma rot_inv_idx {k : ℕ} (hk : 0 < k) (m i : ℕ) (hi : i < k) :
    ((i + k - (k - m % k) % k) % k + k - m % k) % k = i := by
  set r := m % k
  have hr : r < k := Nat.mod_lt m hk
  by_cases hr0 : r = 0
  · rw [hr0]
    simp only [Nat.sub_zero, Nat.mod_self, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have hkr : k - r < k := by omega
    rw [Nat.mod_eq_of_lt hkr]
    have h1 : i + k - (k - r) = i + r := by omega
    rw [h1]
    have h2 : ((i + r) % k + k - r) % k = ((i + r) % k + (k - r)) % k := by
      congr 1; omega
    rw [h2, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h3 : i + r + (k - r) = i + k := by omega
    rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

private lemma rot_inv_idx' {k : ℕ} (hk : 0 < k) (m i : ℕ) (hi : i < k) :
    ((i + k - m % k) % k + k - (k - m % k) % k) % k = i := by
  set r := m % k
  have hr : r < k := Nat.mod_lt m hk
  by_cases hr0 : r = 0
  · rw [hr0]
    simp only [Nat.sub_zero, Nat.mod_self, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have hkr : k - r < k := by omega
    rw [Nat.mod_eq_of_lt hkr]
    have h1 : ((i + k - r) % k + k - (k - r)) % k = ((i + k - r) % k + r) % k := by
      congr 1; omega
    rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h2 : i + k - r + r = i + k := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

end PEqualNP.Outside.L_meta_25861_aux

open PEqualNP.Outside.L_meta_25861_aux

theorem PEqualNP.Outside.L_meta_25861 :
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
        ∀ (next later : Fin s → W),
          let A := (Finset.univ : Finset W).filter (fun x => ∀ p,
            layer (x + rot start (shift p)) - layer x + rot (feed 0) (shift p) = next p)
          let B := (Finset.univ : Finset W).filter (fun y => ∀ p,
            layer (y + next p) - layer y + rot (feed 1) (shift p) = later p)
          let inv := rot (k - (feed 0) % k)
          let trans := fun z => rot (feed 1) (inv z)
          let sign := fun (b : F) => if b = 0 then (1 : ℤ) else -1
          let delta := fun (nm w : W) (j : ℕ) (p : Fin s) =>
            state c nm (w + shift p) j - state c nm w j
          let passes := fun nm w => ∀ p, delta nm w 1 p = next p ∧ delta nm w 2 p = later p
          let pairs := (Finset.univ : Finset (W × W)).filter (fun nw => passes nw.1 nw.2)
          let separated := fun (nm km : W) (m : Fin s → W) =>
            let price := fun z => dotProduct km (inv z) + dotProduct nm (rot start (inv z))
            let ell := fun z => ∑ p, dotProduct (m p) (polar z (later p))
            let offset := price (c 0) + ell (trans (c 0) + c 1) +
              ∑ p, dotProduct (m p) (layer (later p) + rot (feed 2) (shift p))
            sign offset *
              (∑ x ∈ A, sign (dotProduct nm x + price (layer x) + ell (trans (layer x)))) *
              (∑ y ∈ B, sign (price y + ell (layer y + trans y)))
          (∀ nm km m, (∑ nw ∈ pairs, sign (dotProduct nm nw.1 + dotProduct km nw.2 +
            ∑ p, dotProduct (m p) (delta nw.1 nw.2 3 p))) = separated nm km m) ∧
          (∀ (name : W) (want : Fin s → W),
            (2 : ℤ) ^ (k * (s + 1)) * ((Finset.univ.filter (fun w : W =>
              passes name w ∧ ∀ p, delta name w 3 p = want p)).card : ℤ) =
              ∑ nm : W, ∑ m : Fin s → W,
                sign (dotProduct nm name + ∑ p, dotProduct (m p) (want p)) * separated nm 0 m) := by
  intro k d s hk F W ix rot mix layer polar start feed c shift state
    next later A B inv trans sign delta passes pairs separated
  have hsign_eq : sign = signZ := rfl
  have hrot_add : ∀ (m : ℕ) (x y : W), rot m (x + y) = rot m x + rot m y := by
    intro m x y; funext i; rfl
  have hmix_add : ∀ (x y : W), mix (x + y) = mix x + mix y := by
    intro x y; funext i
    change (x i + y i) + (x (ix (i.val + d)) + y (ix (i.val + d))) +
        (x (ix (i.val + k - d % k)) + y (ix (i.val + k - d % k))) =
      (x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))) +
        (y i + y (ix (i.val + d)) + y (ix (i.val + k - d % k)))
    ring
  have hmix_add_at : ∀ (x y : W) (j : Fin k), mix (x + y) j = mix x j + mix y j :=
    fun x y j => congrFun (hmix_add x y) j
  have hpolar_add_left : ∀ (x y z : W), polar (x + y) z = polar x z + polar y z := by
    intro x y z; funext i
    change mix (x + y) (ix (i.val + 1)) * mix z (ix (i.val + 2)) +
        mix (x + y) (ix (i.val + 2)) * mix z (ix (i.val + 1)) =
      (mix x (ix (i.val + 1)) * mix z (ix (i.val + 2)) +
        mix x (ix (i.val + 2)) * mix z (ix (i.val + 1))) +
      (mix y (ix (i.val + 1)) * mix z (ix (i.val + 2)) +
        mix y (ix (i.val + 2)) * mix z (ix (i.val + 1)))
    simp only [hmix_add_at]
    ring
  have hlayer_diff : ∀ (z u : W), layer (z + u) - layer z = layer u + polar z u := by
    intro z u; funext i
    change (mix (z + u) i + (1 + mix (z + u) (ix (i.val + 1))) * mix (z + u) (ix (i.val + 2))) -
        (mix z i + (1 + mix z (ix (i.val + 1))) * mix z (ix (i.val + 2))) =
      (mix u i + (1 + mix u (ix (i.val + 1))) * mix u (ix (i.val + 2))) +
      (mix z (ix (i.val + 1)) * mix u (ix (i.val + 2)) +
        mix z (ix (i.val + 2)) * mix u (ix (i.val + 1)))
    simp only [hmix_add_at]
    ring
  have hrot_inv : ∀ (m : ℕ) (z : W), rot (k - m % k) (rot m z) = z := by
    intro m z; funext i
    change z ⟨((i.val + k - (k - m % k) % k) % k + k - m % k) % k, _⟩ = z i
    congr 1
    exact Fin.ext (rot_inv_idx hk m i.val i.isLt)
  have hrot_inv' : ∀ (m : ℕ) (z : W), rot m (rot (k - m % k) z) = z := by
    intro m z; funext i
    change z ⟨((i.val + k - m % k) % k + k - (k - m % k) % k) % k, _⟩ = z i
    congr 1
    exact Fin.ext (rot_inv_idx' hk m i.val i.isLt)
  have hinv_add : ∀ x y : W, inv (x + y) = inv x + inv y := fun x y => hrot_add _ x y
  have htrans_add : ∀ x y : W, trans (x + y) = trans x + trans y := fun x y => by
    change rot (feed 1) (inv (x + y)) = rot (feed 1) (inv x) + rot (feed 1) (inv y)
    rw [hinv_add, hrot_add]
  let coordEquiv : (W × W) ≃ (W × W) :=
    { toFun := fun nw =>
        let x := rot start nw.2 + nw.1
        (x, layer x + rot (feed 0) nw.2 + c 0)
      invFun := fun xy =>
        let w := inv (xy.2 + layer xy.1 + c 0)
        (xy.1 + rot start w, w)
      left_inv := by
        rintro ⟨nm, w⟩
        dsimp only
        have hsum : layer (rot start w + nm) + rot (feed 0) w + c 0 +
            layer (rot start w + nm) + c 0 = rot (feed 0) w := by
          calc
            layer (rot start w + nm) + rot (feed 0) w + c 0 + layer (rot start w + nm) + c 0
              = rot (feed 0) w + (layer (rot start w + nm) + layer (rot start w + nm)) +
                (c 0 + c 0) := by abel
            _ = rot (feed 0) w := by rw [vec_add_self, vec_add_self, add_zero, add_zero]
        have hw : inv (layer (rot start w + nm) + rot (feed 0) w + c 0 +
            layer (rot start w + nm) + c 0) = w := by
          rw [hsum]; exact hrot_inv (feed 0) w
        apply Prod.ext
        · rw [hw]
          calc
            rot start w + nm + rot start w = nm + (rot start w + rot start w) := by abel
            _ = nm := by rw [vec_add_self, add_zero]
        · exact hw
      right_inv := by
        rintro ⟨x, y⟩
        dsimp only
        set w := inv (y + layer x + c 0)
        have hx : rot start w + (x + rot start w) = x := by
          calc
            rot start w + (x + rot start w) = x + (rot start w + rot start w) := by abel
            _ = x := by rw [vec_add_self, add_zero]
        have hrot0 : rot (feed 0) w = y + layer x + c 0 := hrot_inv' (feed 0) (y + layer x + c 0)
        apply Prod.ext
        · exact hx
        · rw [hx, hrot0]
          calc
            layer x + (y + layer x + c 0) + c 0
              = y + (layer x + layer x) + (c 0 + c 0) := by abel
            _ = y := by rw [vec_add_self, vec_add_self, add_zero, add_zero] }
  have hdelta1 : ∀ (nm w : W) (p : Fin s),
      delta nm w 1 p =
        layer (state c nm w 0 + rot start (shift p)) - layer (state c nm w 0) +
          rot (feed 0) (shift p) := by
    intro nm w p
    change (layer (rot start (w + shift p) + nm) + rot (feed 0) (w + shift p) + c 0) -
        (layer (rot start w + nm) + rot (feed 0) w + c 0) =
      layer ((rot start w + nm) + rot start (shift p)) - layer (rot start w + nm) +
        rot (feed 0) (shift p)
    rw [hrot_add, hrot_add]
    have ha : rot start w + rot start (shift p) + nm = rot start w + nm + rot start (shift p) := by
      abel
    rw [ha, vec_sub_eq_add, vec_sub_eq_add]
    calc
      layer (rot start w + nm + rot start (shift p)) + (rot (feed 0) w + rot (feed 0) (shift p)) + c 0 +
          (layer (rot start w + nm) + rot (feed 0) w + c 0)
        = layer (rot start w + nm + rot start (shift p)) + layer (rot start w + nm) +
          rot (feed 0) (shift p) + (rot (feed 0) w + rot (feed 0) w) + (c 0 + c 0) := by abel
      _ = layer (rot start w + nm + rot start (shift p)) + layer (rot start w + nm) +
          rot (feed 0) (shift p) := by rw [vec_add_self, vec_add_self, add_zero, add_zero]
  have hdelta2 : ∀ (nm w : W) (p : Fin s),
      delta nm w 1 p = next p →
      delta nm w 2 p =
        layer (state c nm w 1 + next p) - layer (state c nm w 1) + rot (feed 1) (shift p) := by
    intro nm w p h1
    have hst1 : state c nm (w + shift p) 1 = state c nm w 1 + next p := by
      rw [← h1]
      change state c nm (w + shift p) 1 = state c nm w 1 + (state c nm (w + shift p) 1 - state c nm w 1)
      rw [vec_sub_eq_add]
      calc
        state c nm (w + shift p) 1 =
            state c nm (w + shift p) 1 + (state c nm w 1 + state c nm w 1) := by
          rw [vec_add_self, add_zero]
        _ = state c nm w 1 + (state c nm (w + shift p) 1 + state c nm w 1) := by abel
    change (layer (state c nm (w + shift p) 1) + rot (feed 1) (w + shift p) + c 1) -
        (layer (state c nm w 1) + rot (feed 1) w + c 1) =
      layer (state c nm w 1 + next p) - layer (state c nm w 1) + rot (feed 1) (shift p)
    rw [hst1, hrot_add, vec_sub_eq_add, vec_sub_eq_add]
    calc
      layer (state c nm w 1 + next p) + (rot (feed 1) w + rot (feed 1) (shift p)) + c 1 +
          (layer (state c nm w 1) + rot (feed 1) w + c 1)
        = layer (state c nm w 1 + next p) + layer (state c nm w 1) + rot (feed 1) (shift p) +
          (rot (feed 1) w + rot (feed 1) w) + (c 1 + c 1) := by abel
      _ = layer (state c nm w 1 + next p) + layer (state c nm w 1) + rot (feed 1) (shift p) := by
        rw [vec_add_self, vec_add_self, add_zero, add_zero]
  have hdelta3 : ∀ (nm w : W) (p : Fin s),
      delta nm w 2 p = later p →
      delta nm w 3 p =
        polar (state c nm w 2) (later p) + layer (later p) + rot (feed 2) (shift p) := by
    intro nm w p h2
    have hst2 : state c nm (w + shift p) 2 = state c nm w 2 + later p := by
      rw [← h2]
      change state c nm (w + shift p) 2 = state c nm w 2 + (state c nm (w + shift p) 2 - state c nm w 2)
      rw [vec_sub_eq_add]
      calc
        state c nm (w + shift p) 2 =
            state c nm (w + shift p) 2 + (state c nm w 2 + state c nm w 2) := by
          rw [vec_add_self, add_zero]
        _ = state c nm w 2 + (state c nm (w + shift p) 2 + state c nm w 2) := by abel
    change (layer (state c nm (w + shift p) 2) + rot (feed 2) (w + shift p) + c 2) -
        (layer (state c nm w 2) + rot (feed 2) w + c 2) =
      polar (state c nm w 2) (later p) + layer (later p) + rot (feed 2) (shift p)
    rw [hst2, hrot_add, vec_sub_eq_add]
    have hstep :
        layer (state c nm w 2 + later p) + (rot (feed 2) w + rot (feed 2) (shift p)) + c 2 +
            (layer (state c nm w 2) + rot (feed 2) w + c 2) =
          (layer (state c nm w 2 + later p) - layer (state c nm w 2)) + rot (feed 2) (shift p) := by
      rw [vec_sub_eq_add]
      calc
        layer (state c nm w 2 + later p) + (rot (feed 2) w + rot (feed 2) (shift p)) + c 2 +
            (layer (state c nm w 2) + rot (feed 2) w + c 2)
          = layer (state c nm w 2 + later p) + layer (state c nm w 2) + rot (feed 2) (shift p) +
            (rot (feed 2) w + rot (feed 2) w) + (c 2 + c 2) := by abel
        _ = layer (state c nm w 2 + later p) + layer (state c nm w 2) + rot (feed 2) (shift p) := by
          rw [vec_add_self, vec_add_self, add_zero, add_zero]
    rw [hstep, hlayer_diff]
    abel
  have hpasses_iff : ∀ nw : W × W, passes nw.1 nw.2 ↔ coordEquiv nw ∈ A ×ˢ B := by
    rintro ⟨nm, w⟩
    simp only [Finset.mem_product, A, B, Finset.mem_filter, Finset.mem_univ, true_and]
    change (∀ p, delta nm w 1 p = next p ∧ delta nm w 2 p = later p) ↔
      (∀ p, layer (state c nm w 0 + rot start (shift p)) - layer (state c nm w 0) +
        rot (feed 0) (shift p) = next p) ∧
      (∀ p, layer (state c nm w 1 + next p) - layer (state c nm w 1) +
        rot (feed 1) (shift p) = later p)
    constructor
    · intro h
      refine ⟨fun p => ?_, fun p => ?_⟩
      · rw [← hdelta1 nm w p]; exact (h p).1
      · rw [← hdelta2 nm w p (h p).1]; exact (h p).2
    · rintro ⟨hA, hB⟩ p
      have h1 : delta nm w 1 p = next p := by rw [hdelta1 nm w p]; exact hA p
      exact ⟨h1, by rw [hdelta2 nm w p h1]; exact hB p⟩
  have hfact : ∀ (nm km : W) (m : Fin s → W),
      (∑ nw ∈ pairs, sign (dotProduct nm nw.1 + dotProduct km nw.2 +
        ∑ p, dotProduct (m p) (delta nw.1 nw.2 3 p))) = separated nm km m := by
    intro nm km m
    let price : W → F := fun z => dotProduct km (inv z) + dotProduct nm (rot start (inv z))
    let ell : W → F := fun z => ∑ p, dotProduct (m p) (polar z (later p))
    let offset : F := price (c 0) + ell (trans (c 0) + c 1) +
      ∑ p, dotProduct (m p) (layer (later p) + rot (feed 2) (shift p))
    have hprice_add : ∀ x y : W, price (x + y) = price x + price y := by
      intro x y
      dsimp only [price]
      rw [hinv_add, hrot_add, dotProduct_add, dotProduct_add]
      ring
    have hell_add : ∀ x y : W, ell (x + y) = ell x + ell y := by
      intro x y
      dsimp only [ell]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rw [hpolar_add_left, dotProduct_add]
    have hsum_bij :
        ∑ nw ∈ pairs, signZ (dotProduct nm nw.1 + dotProduct km nw.2 +
          ∑ p, dotProduct (m p) (delta nw.1 nw.2 3 p)) =
        ∑ xy ∈ A ×ˢ B,
          signZ (offset + (dotProduct nm xy.1 + price (layer xy.1) + ell (trans (layer xy.1))) +
            (price xy.2 + ell (layer xy.2 + trans xy.2))) := by
      apply Finset.sum_bij (fun nw _ => coordEquiv nw)
      · intro nw hnw
        exact (hpasses_iff nw).mp (Finset.mem_filter.mp hnw).2
      · intro nw1 _ nw2 _ heq
        exact coordEquiv.injective heq
      · intro xy hxy
        refine ⟨coordEquiv.symm xy, ?_, coordEquiv.apply_symm_apply xy⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, (hpasses_iff _).mpr ?_⟩
        rw [coordEquiv.apply_symm_apply]
        exact hxy
      · intro nw hnw
        have hpass : passes nw.1 nw.2 := (Finset.mem_filter.mp hnw).2
        set x := (coordEquiv nw).1
        set y := (coordEquiv nw).2
        have hinv_xy : coordEquiv.symm (x, y) = nw := coordEquiv.left_inv nw
        have hw_eq : nw.2 = inv (y + layer x + c 0) :=
          (congrArg Prod.snd hinv_xy).symm
        have hnm_eq : nw.1 = x + rot start (inv (y + layer x + c 0)) :=
          (congrArg Prod.fst hinv_xy).symm
        have hst2_eq : state c nw.1 nw.2 2 =
            (layer y + trans y) + trans (layer x) + (trans (c 0) + c 1) := by
          change layer y + rot (feed 1) nw.2 + c 1 = _
          rw [hw_eq]
          change layer y + trans (y + layer x + c 0) + c 1 = _
          rw [htrans_add, htrans_add]
          abel
        have hsum_d3 :
            ∑ p, dotProduct (m p) (delta nw.1 nw.2 3 p) =
              ell (layer y + trans y) + ell (trans (layer x)) + ell (trans (c 0) + c 1) +
                ∑ p, dotProduct (m p) (layer (later p) + rot (feed 2) (shift p)) := by
          have hterm : ∀ p : Fin s,
              dotProduct (m p) (delta nw.1 nw.2 3 p) =
                dotProduct (m p) (polar (state c nw.1 nw.2 2) (later p)) +
                dotProduct (m p) (layer (later p) + rot (feed 2) (shift p)) := by
            intro p
            rw [hdelta3 nw.1 nw.2 p (hpass p).2, add_assoc, dotProduct_add]
          rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_add_distrib]
          change ell (state c nw.1 nw.2 2) + _ = _
          rw [hst2_eq, hell_add, hell_add]
        congr 1
        rw [hsum_d3, hnm_eq, hw_eq, dotProduct_add]
        have h1 : dotProduct nm (rot start (inv (y + layer x + c 0))) +
            dotProduct km (inv (y + layer x + c 0)) =
            price y + price (layer x) + price (c 0) := by
          rw [← hprice_add, ← hprice_add]
          dsimp only [price]
          ring
        dsimp only [offset]
        linear_combination h1
    change ∑ nw ∈ pairs, signZ (dotProduct nm nw.1 + dotProduct km nw.2 +
        ∑ p, dotProduct (m p) (delta nw.1 nw.2 3 p)) =
      signZ offset *
        (∑ x ∈ A, signZ (dotProduct nm x + price (layer x) + ell (trans (layer x)))) *
        (∑ y ∈ B, signZ (price y + ell (layer y + trans y)))
    rw [hsum_bij, Finset.sum_product]
    have hinner : ∀ x ∈ A,
        ∑ y ∈ B, signZ (offset + (dotProduct nm x + price (layer x) + ell (trans (layer x))) +
            (price y + ell (layer y + trans y))) =
          signZ offset * signZ (dotProduct nm x + price (layer x) + ell (trans (layer x))) *
            ∑ y ∈ B, signZ (price y + ell (layer y + trans y)) := by
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [signZ_add, signZ_add]
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ← Finset.mul_sum]
  refine ⟨hfact, ?_⟩
  intro name want
  have hRHS :
      ∑ nm : W, ∑ m : Fin s → W,
          sign (dotProduct nm name + ∑ p, dotProduct (m p) (want p)) * separated nm 0 m =
      ∑ nw ∈ pairs,
        (∑ nm : W, signZ (dotProduct nm (name + nw.1))) *
        (∑ m : Fin s → W, signZ (∑ p, dotProduct (m p) (want p + delta nw.1 nw.2 3 p))) := by
    have hstep1 :
        ∑ nm : W, ∑ m : Fin s → W,
            sign (dotProduct nm name + ∑ p, dotProduct (m p) (want p)) * separated nm 0 m =
        ∑ nm : W, ∑ m : Fin s → W, ∑ nw ∈ pairs,
          signZ (dotProduct nm (name + nw.1)) *
          signZ (∑ p, dotProduct (m p) (want p + delta nw.1 nw.2 3 p)) := by
      apply Finset.sum_congr rfl
      intro nm _
      apply Finset.sum_congr rfl
      intro m _
      rw [← hfact nm 0 m, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro nw _
      change signZ _ * signZ _ = _
      rw [← signZ_add, ← signZ_add]
      congr 1
      have h0 : dotProduct (0 : W) nw.2 = 0 := zero_dotProduct nw.2
      rw [h0, add_zero, dotProduct_add]
      have hsum_add :
          (∑ p, dotProduct (m p) (want p)) + (∑ p, dotProduct (m p) (delta nw.1 nw.2 3 p)) =
            ∑ p, dotProduct (m p) (want p + delta nw.1 nw.2 3 p) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun p _ => (dotProduct_add _ _ _).symm)
      linear_combination hsum_add
    rw [hstep1, Finset.sum_comm]
    have hswap :
        ∑ m : Fin s → W, ∑ nm : W, ∑ nw ∈ pairs,
          signZ (dotProduct nm (name + nw.1)) *
          signZ (∑ p, dotProduct (m p) (want p + delta nw.1 nw.2 3 p)) =
        ∑ m : Fin s → W, ∑ nw ∈ pairs, ∑ nm : W,
          signZ (dotProduct nm (name + nw.1)) *
          signZ (∑ p, dotProduct (m p) (want p + delta nw.1 nw.2 3 p)) :=
      Finset.sum_congr rfl (fun m _ => Finset.sum_comm)
    rw [hswap, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro nw _
    rw [Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro nm _
    rw [Finset.mul_sum]
  rw [hRHS]
  have hpow : (2 : ℤ) ^ k * ((2 : ℤ) ^ k) ^ s = (2 : ℤ) ^ (k * (s + 1)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hterm : ∀ nw ∈ pairs,
      (∑ nm : W, signZ (dotProduct nm (name + nw.1))) *
      (∑ m : Fin s → W, signZ (∑ p, dotProduct (m p) (want p + delta nw.1 nw.2 3 p))) =
      if (nw.1 = name ∧ ∀ p, delta nw.1 nw.2 3 p = want p) then (2 : ℤ) ^ (k * (s + 1)) else 0 := by
    intro nw _
    rw [sum_signZ_dot, sum_signZ_tuple]
    have h1eq : (name + nw.1 = 0) ↔ (nw.1 = name) := vec_add_eq_zero_iff name nw.1
    have h2eq : (∀ p, want p + delta nw.1 nw.2 3 p = 0) ↔ (∀ p, delta nw.1 nw.2 3 p = want p) :=
      forall_congr' (fun p => vec_add_eq_zero_iff (want p) _)
    simp only [h1eq, h2eq]
    by_cases h1 : nw.1 = name <;> by_cases h2 : ∀ p, delta nw.1 nw.2 3 p = want p <;>
      simp [h1, h2, hpow]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  norm_cast
  apply Finset.card_bij (fun w _ => (name, w))
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_filter, pairs, Finset.mem_univ, true_and]
    exact hw
  · intro w1 _ w2 _ heq
    exact congrArg Prod.snd heq
  · rintro ⟨nm, w⟩ hmem
    simp only [Finset.mem_filter, pairs, Finset.mem_univ, true_and] at hmem
    rcases hmem with ⟨hpass, rfl, hwant⟩
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hpass, hwant⟩, rfl⟩
