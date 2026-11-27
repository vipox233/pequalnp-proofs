import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_356_aux

abbrev Ed (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}
abbrev I (k : ℕ) := Ed k × (Bool × Fin 3 × Bool)
abbrev W (k : ℕ) := Fin k ⊕ (Ed k × Bool × Bool)

def lv (c : Bool × Fin 3 × Bool) : Bool ⊕ Bool × Bool :=
  if c.2.1 = 0 then (if c.2.2 then .inr (c.1, false) else .inl false)
  else if c.2.1 = 1 then .inr (c.1, c.2.2)
  else (if c.2.2 then .inl true else .inr (c.1, true))

def gl {k : ℕ} (e : Ed k) : Bool ⊕ Bool × Bool → W k :=
  Sum.elim (fun b => .inl (if b then e.1.2 else e.1.1)) (fun w => .inr (e, w))

def vtx {k : ℕ} (c : I k) : W k := gl c.1 (lv c.2)

def fl (k : ℕ) : Equiv.Perm (I k) :=
  Function.Involutive.toPerm (fun c => (c.1, c.2.1, c.2.2.1, !c.2.2.2))
    (fun c => by simp)

def val (u v : Bool) (h : Bool → Bool → Bool) : Bool ⊕ Bool × Bool → Bool :=
  Sum.elim (fun b => if b then v else u) (fun w => h w.1 w.2)

def cst (u v : Bool) (h : Bool → Bool → Bool) : ℕ :=
  (Finset.univ.filter (fun c : Bool × Fin 3 × Bool =>
    val u v h (lv c) ≠ val u v h (lv (c.1, c.2.1, !c.2.2)))).card

def A (g : Bool) : Finset (Bool → Bool → Bool) :=
  if g = true then Finset.univ else {fun p t => p != t}

def T (g u v : Bool) : ℕ := if g = true ∧ u ≠ v then 12 else 8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem loc : ∀ g u v : Bool, (∀ h ∈ A g, cst u v h ≤ T g u v) ∧
    ((A g).filter (fun h => cst u v h = T g u v)).card = if g = true ∧ u = v then 9 else 1 := by
  decide

theorem cyc (m : ℕ) (g : Fin m → Bool) (h : ∀ i, g (finRotate m i) = g i) (i j : Fin m) :
    g i = g j := by
  cases m with
  | zero => exact i.elim0
  | succ m =>
    have : ∀ i : Fin (m+1), g i = g 0 := fun i => by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => rw [← ih, ← h i.castSucc, finRotate_apply, Fin.coeSucc_eq_succ]
    rw [this i, this j]

theorem rot {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) :
    ∃ σ : Equiv.Perm α, (∀ a, f (σ a) = f a) ∧
      ∀ g : α → Bool, (∀ a, g (σ a) = g a) → ∀ a b, f a = f b → g a = g b := by
  classical
  let F := Equiv.sigmaFiberEquiv f
  let φ : ∀ b, {a // f a = b} ≃ Fin (Fintype.card {a // f a = b}) := fun b => Fintype.equivFin _
  let τ : ∀ b, Equiv.Perm {a // f a = b} := fun b => (φ b).trans ((finRotate _).trans (φ b).symm)
  let σ : Equiv.Perm α := F.symm.trans ((Equiv.sigmaCongrRight τ).trans F)
  have hσ : ∀ b (a : {a // f a = b}), σ a.1 = (τ b a).1 := by
    rintro b ⟨a, rfl⟩
    rfl
  refine ⟨σ, fun a => ?_, fun g hg a b hab => ?_⟩
  · rw [hσ (f a) ⟨a, rfl⟩]
    exact (τ (f a) ⟨a, rfl⟩).2
  · have := cyc _ (fun i => g ((φ (f b)).symm i).1) (fun i => by
      have := hg ((φ (f b)).symm i).1
      rw [hσ (f b)] at this
      simpa [τ] using this) (φ (f b) ⟨a, hab⟩) (φ (f b) ⟨b, rfl⟩)
    simpa using this

theorem cardE (k : ℕ) : Fintype.card (Ed k) = k.choose 2 := by
  let e : Ed k ≃ Σ j : Fin k, Fin j.val :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
      invFun := fun s => ⟨(⟨s.2.val, s.2.2.trans s.1.2⟩, s.1), s.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun s => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) k, Finset.sum_range_id, Nat.choose_two_right]

end PEqualNP.Outside.L_pcx_356_aux

open PEqualNP.Outside.L_pcx_356_aux in
theorem PEqualNP.Outside.L_pcx_356 : (∀ k : ℕ, 2 ≤ k →
  let E := {p : Fin k × Fin k // p.1 < p.2}
  let q := k.choose 2
  let n := 12*q
  let V := Bool × Fin n
  let X := V → Bool
  ∃ (M : Fin 3 → Equiv.Perm (Fin n)) (observe : Fin k ↪ V)
    (port : V → Option E) (fixed : V → Bool),
    ∀ (G : E → Bool) (x : Fin k → Bool),
      let edges := (Finset.univ : Finset E).filter (fun e => G e = true)
      let cut := (edges.filter (fun e => x e.val.1 ≠ x e.val.2)).card
      let cost := fun (y : X) (j : Fin 3) =>
        (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,M j i))).card
      let fiber := (Finset.univ : Finset X).filter (fun y =>
        (∀ v, ∀ e : E, port v = some e → G e = false → y v = fixed v) ∧
        (∀ u, y (observe u) = x u) ∧ cost y 0 = 0 ∧ cost y 1 = 0)
      (∀ y ∈ fiber, cost y 2 ≤ 8*q + 4*cut) ∧
        (fiber.filter (fun y => cost y 2 = 8*q + 4*cut)).card = 9^(edges.card-cut)) := by
  intro k hk E q n V X
  have hI : Fintype.card (Fin n) = Fintype.card (I k) := by
    simp [n, q, cardE]
    ring
  let φ : Fin n ≃ I k := Fintype.equivOfCardEq hI
  obtain ⟨σ, hσ1, hσ2⟩ := rot (fun i : Fin n => vtx (φ i))
  have hsur : ∀ w : W k, ∃ i, vtx (φ i) = w := by
    intro w
    suffices ∃ c : I k, vtx c = w by
      obtain ⟨c, hc⟩ := this
      exact ⟨φ.symm c, by simpa using hc⟩
    rcases w with a | ⟨e, p, t⟩
    · have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
      obtain ⟨b, hb⟩ := exists_ne a
      rcases lt_or_gt_of_ne hb with h | h
      · exact ⟨(⟨(b,a), h⟩, false, 2, true), rfl⟩
      · exact ⟨(⟨(a,b), h⟩, false, 0, false), rfl⟩
    · exact ⟨(e, p, 1, t), rfl⟩
  choose r hr using hsur
  let M : Fin 3 → Equiv.Perm (Fin n) := ![1, σ, φ.trans ((fl k).trans φ.symm)]
  let observe : Fin k ↪ V := ⟨fun a => (false, r (.inl a)), fun a b h => by
    have := congrArg (fun v : Bool × Fin n => vtx (φ v.2)) h
    simpa [hr] using this⟩
  let port : V → Option E := fun v => Sum.elim (fun _ => none) (fun w => some w.1) (vtx (φ v.2))
  let fixed : V → Bool := fun v =>
    Sum.elim (fun _ => false) (fun w => w.2.1 != w.2.2) (vtx (φ v.2))
  refine ⟨M, observe, port, fixed, fun G x => ?_⟩
  intro edges cut cost fiber
  let Y : (E → Bool → Bool → Bool) → X := fun h v =>
    Sum.elim x (fun w => h w.1 w.2.1 w.2.2) (vtx (φ v.2))
  have hfib : fiber = (Fintype.piFinset (fun e : E => A (G e))).image Y := by
    ext y
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Fintype.mem_piFinset]
    constructor
    · rintro ⟨hp, ho, h0, h1⟩
      have e0 : ∀ i, y (false,i) = y (true,i) := by
        intro i
        have := Finset.card_eq_zero.1 h0
        rw [Finset.filter_eq_empty_iff] at this
        simpa [M] using this (Finset.mem_univ i)
      have e1 : ∀ i, y (false,i) = y (true,σ i) := by
        intro i
        have := Finset.card_eq_zero.1 h1
        rw [Finset.filter_eq_empty_iff] at this
        simpa [M] using this (Finset.mem_univ i)
      have con := hσ2 (fun i => y (false,i)) (fun i => (e0 (σ i)).trans (e1 i).symm)
      let z : W k → Bool := fun w => y (false, r w)
      have hz : ∀ b i, y (b,i) = z (vtx (φ i)) := by
        intro b i
        have : y (false,i) = z (vtx (φ i)) := con _ _ (hr _).symm
        cases b
        · exact this
        · rw [← e0]; exact this
      refine ⟨fun e p t => z (.inr (e,p,t)), fun e => ?_, ?_⟩
      · unfold A
        split_ifs with hg
        · exact Finset.mem_univ _
        · rw [Finset.mem_singleton]
          funext p t
          have hv := hr (.inr (e,p,t))
          have := hp (false, r (.inr (e,p,t))) e (by simp [port, hv]) (by simpa using hg)
          simpa [fixed, hv, z] using this
      · funext v
        obtain ⟨b, i⟩ := v
        rw [hz b i]
        dsimp only [Y]
        rcases vtx (φ i) with a | w
        · exact (ho a).symm
        · rfl
    · rintro ⟨h, hh, rfl⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro v e hv hg
        dsimp only [port] at hv
        dsimp only [Y, fixed]
        rcases hw : vtx (φ v.2) with a | w
        · rw [hw] at hv
          simp at hv
        · rw [hw] at hv
          have he : w.1 = e := by simpa using hv
          have h2 := hh w.1
          rw [he] at h2
          simp [A, hg] at h2
          simp [he, h2]
      · intro a
        change Sum.elim x _ (vtx (φ (r (.inl a)))) = x a
        rw [hr]
        rfl
      · change (Finset.univ.filter _).card = 0
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        simp [M, Y]
      · change (Finset.univ.filter _).card = 0
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        simp [M, Y, hσ1]
  have hY : Function.Injective Y := by
    intro h h' hh
    funext e p t
    have := congrFun hh (false, r (.inr (e,p,t)))
    simpa [Y, hr] using this
  have hc : ∀ h, cost (Y h) 2 = ∑ e : E, cst (x e.1.1) (x e.1.2) (h e) := by
    intro h
    have hg : ∀ (e : E) l, Sum.elim x (fun w => h w.1 w.2.1 w.2.2) (gl e l)
        = val (x e.1.1) (x e.1.2) (h e) l := by
      intro e l
      rcases l with b | w
      · cases b <;> rfl
      · rfl
    have : cost (Y h) 2 = (Finset.univ.filter (fun c : I k =>
        val (x c.1.1.1) (x c.1.1.2) (h c.1) (lv c.2)
          ≠ val (x c.1.1.1) (x c.1.1.2) (h c.1) (lv (c.2.1, c.2.2.1, !c.2.2.2)))).card := by
      refine Finset.card_equiv φ (fun i => ?_)
      have h2 : φ (M 2 i) = fl k (φ i) := by simp [M]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Y, h2]
      simp only [vtx, hg]
      rfl
    rw [this, Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [cst, Finset.card_filter]
  have hT : ∑ e : E, T (G e) (x e.1.1) (x e.1.2) = 8*q + 4*cut := by
    have h1 : ∀ e : E, T (G e) (x e.1.1) (x e.1.2)
        = 8 + 4 * (if G e = true ∧ x e.1.1 ≠ x e.1.2 then 1 else 0) := by
      intro e
      unfold T
      split_ifs <;> rfl
    have h2 : Fintype.card E = q := cardE k
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      h2, smul_eq_mul, ← Finset.card_filter, cut, edges, Finset.filter_filter]
    ring
  have hS : ∀ h ∈ Fintype.piFinset (fun e : E => A (G e)), ∀ e : E,
      cst (x e.1.1) (x e.1.2) (h e) ≤ T (G e) (x e.1.1) (x e.1.2) :=
    fun h hh e => (loc _ _ _).1 _ (Fintype.mem_piFinset.1 hh e)
  rw [hfib]
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hy
    rw [hc, ← hT]
    exact Finset.sum_le_sum (fun e _ => hS h hh e)
  · rw [Finset.filter_image, Finset.card_image_of_injective _ hY]
    have : (Fintype.piFinset (fun e : E => A (G e))).filter (fun h => cost (Y h) 2 = 8*q + 4*cut)
        = Fintype.piFinset (fun e : E => (A (G e)).filter
          (fun h => cst (x e.1.1) (x e.1.2) h = T (G e) (x e.1.1) (x e.1.2))) := by
      ext h
      rw [Finset.mem_filter, hc, ← hT]
      constructor
      · rintro ⟨hh, hs⟩
        refine Fintype.mem_piFinset.2 (fun e => Finset.mem_filter.2
          ⟨Fintype.mem_piFinset.1 hh e, ?_⟩)
        exact (Finset.sum_eq_sum_iff_of_le (fun e _ => hS h hh e)).1 hs e (Finset.mem_univ _)
      · intro hh
        have hh' := fun e => Finset.mem_filter.1 (Fintype.mem_piFinset.1 hh e)
        exact ⟨Fintype.mem_piFinset.2 (fun e => (hh' e).1),
          Finset.sum_congr rfl (fun e _ => (hh' e).2)⟩
    rw [this, Fintype.card_piFinset]
    simp only [fun e : E => (loc (G e) (x e.1.1) (x e.1.2)).2]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 1
    have := Finset.card_filter_add_card_filter_not (s := edges)
      (fun e => x e.val.1 ≠ x e.val.2)
    simp only [edges, cut, Finset.filter_filter, not_not] at this ⊢
    omega
