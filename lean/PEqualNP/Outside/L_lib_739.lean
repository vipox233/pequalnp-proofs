import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_739.Adapt

abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
abbrev E (n names : ℕ) := Fin names × V n

def fixed {n names m : ℕ} (q : ℕ) (negative : Finset (E n names))
    (positive : Fin m → Finset (E n names)) : Prop :=
  ∃ c : Fin names → Fin q → V (n+1),
    (∀ p ∈ negative, ∀ j, dotProduct (c p.1 j) (Fin.cons (1 : F) p.2) = 0) ∧
    ∀ cell, ∃ p ∈ positive cell, ∃ j, dotProduct (c p.1 j) (Fin.cons (1 : F) p.2) = 1

def history {q : ℕ} (a : Fin q → F) (j : Fin q) : Fin j.val → F :=
  fun k => a ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩

abbrev Questions (n names q : ℕ) :=
  (j : Fin q) → Fin names → (Fin j.val → F) → (V n →ₗ[F] F)

def adaptive {n names m : ℕ} (q : ℕ) (negative : Finset (E n names))
    (positive : Fin m → Finset (E n names)) : Prop :=
  ∃ (ask : Questions n names q) (ans : E n names → Fin q → F)
    (take : Fin names → (Fin q → F) → Bool),
    (∀ p j, ans p j = ask j p.1 (history (ans p) j) p.2) ∧
    (∀ p ∈ negative, take p.1 (ans p) = false) ∧
    ∀ cell, ∃ p ∈ positive cell, take p.1 (ans p) = true

lemma dual_eval {n : ℕ} (f : V n →ₗ[F] F) (x : V n) :
    dotProduct ((dotProductEquiv F (Fin n)).symm f) x = f x :=
  congrArg (fun (t : V n →ₗ[F] F) => t x) ((dotProductEquiv F (Fin n)).apply_symm_apply f)

lemma tail_eval {n : ℕ} (w : V (n+1)) (x : V n) :
    dotProduct w (Fin.cons (1 : F) x) =
      w 0 + dotProduct (fun i : Fin n => w i.succ) x := by
  simp [dotProduct, Fin.sum_univ_succ]

lemma cons_eval {n : ℕ} (b : F) (v x : V n) :
    dotProduct (Fin.cons b v) (Fin.cons (1 : F) x) = b + dotProduct v x := by
  simp [tail_eval]

lemma bit_one : ∀ z : F, z ≠ 0 → z = 1 := by decide

lemma shift_zero {a b : F} (h : -b + a = 0) : a = b := by
  calc
    a = b + (-b + a) := by rw [← add_assoc, add_neg_cancel, zero_add]
    _ = b := by rw [h, add_zero]

lemma same_answers {n names q : ℕ} (ask : Questions n names q) (ans : E n names → Fin q → F)
    (rule : ∀ p j, ans p j = ask j p.1 (history (ans p) j) p.2)
    (y : Fin names) (x b : V n)
    (h : ∀ j, ask j y (history (ans (y,b)) j) x = ask j y (history (ans (y,b)) j) b) :
    ans (y,x) = ans (y,b) := by
  funext j
  refine Fin.strong_induction_on (motive := fun k => ans (y,x) k = ans (y,b) k) ?_ j
  intro k ih
  have he : history (ans (y,x)) k = history (ans (y,b)) k := by
    funext l
    exact ih ⟨l.val, Nat.lt_trans l.isLt k.isLt⟩ l.isLt
  calc
    ans (y,x) k = ask k y (history (ans (y,x)) k) x := rule _ _
    _ = ask k y (history (ans (y,b)) k) x := by rw [he]
    _ = ask k y (history (ans (y,b)) k) b := h k
    _ = ans (y,b) k := (rule (y,b) k).symm

set_option maxHeartbeats 600000 in
theorem equivalence {n names m q : ℕ} (hq : 0 < q) (negative : Finset (E n names))
    (positive : Fin m → Finset (E n names))
    (single : ∀ y, (negative.filter (fun p => p.1 = y)).card ≤ 1) :
    adaptive q negative positive ↔ fixed q negative positive := by
  classical
  constructor
  · rintro ⟨ask, ans, take, rule, neg, pos⟩
    let present (y : Fin names) := ∃ x : V n, (y,x) ∈ negative
    let base (y : Fin names) : V n := if h : present y then Classical.choose h else 0
    have hb (y : Fin names) (h : present y) : (y,base y) ∈ negative := by
      simpa only [base, dite_eq_left h] using Classical.choose_spec h
    let row (y : Fin names) (j : Fin q) := ask j y (history (ans (y,base y)) j)
    let c (y : Fin names) (j : Fin q) : V (n+1) :=
      if present y then Fin.cons (-(row y j (base y))) ((dotProductEquiv F (Fin n)).symm (row y j))
      else Fin.cons 1 0
    have hc (y : Fin names) (j : Fin q) (x : V n) (h : present y) :
        dotProduct (c y j) (Fin.cons (1 : F) x) = -row y j (base y) + row y j x := by
      simp only [c, ite_eq_left h, cons_eval, dual_eval]
    refine ⟨c, ?_, ?_⟩
    · rintro ⟨y,x⟩ hx j
      have hy : present y := ⟨x,hx⟩
      have eq : (y,x) = (y,base y) :=
        (Finset.card_le_one_iff.mp (single y))
          (Finset.mem_filter.mpr ⟨hx,rfl⟩) (Finset.mem_filter.mpr ⟨hb y hy,rfl⟩)
      change dotProduct (c y j) (Fin.cons (1 : F) x) = 0
      rw [hc y j x hy, show x = base y from congrArg Prod.snd eq, neg_add_cancel]
    · intro cell
      obtain ⟨⟨y,x⟩, hp, yes⟩ := pos cell
      refine ⟨(y,x), hp, ?_⟩
      by_cases hy : present y
      · have different : ans (y,x) ≠ ans (y,base y) := by
          intro he
          have no := neg (y,base y) (hb y hy)
          change take y (ans (y,x)) = true at yes
          rw [he, no] at yes
          contradiction
        have hd : ∃ j, row y j x ≠ row y j (base y) := by
          by_contra! he
          exact different (same_answers ask ans rule y x (base y) he)
        obtain ⟨j,hj⟩ := hd
        refine ⟨j, ?_⟩
        change dotProduct (c y j) (Fin.cons (1 : F) x) = 1
        rw [hc y j x hy]
        apply bit_one
        intro he
        exact hj (shift_zero he)
      · refine ⟨⟨0,hq⟩, ?_⟩
        change dotProduct (c y _) (Fin.cons (1 : F) x) = 1
        simp [c, hy, cons_eval]
  · rintro ⟨c, neg, pos⟩
    let row (y : Fin names) (j : Fin q) :=
      dotProductEquiv F (Fin n) (fun i : Fin n => c y j i.succ)
    let ans (p : E n names) (j : Fin q) := row p.1 j p.2
    let take (y : Fin names) (a : Fin q → F) := decide (∃ j, c y j 0 + a j = 1)
    refine ⟨fun j y _ => row y j, ans, take, fun _ _ => rfl, ?_, ?_⟩
    · intro p hp
      change decide (∃ j, c p.1 j 0 + ans p j = 1) = false
      simp only [decide_eq_false_iff_not]
      rintro ⟨j,hj⟩
      exact zero_ne_one ((neg p hp j).symm.trans ((tail_eval (c p.1 j) p.2).trans hj))
    · intro cell
      obtain ⟨p,hp,j,hj⟩ := pos cell
      refine ⟨p,hp,decide_eq_true ?_⟩
      exact ⟨j, (tail_eval (c p.1 j) p.2).symm.trans hj⟩

end PEqualNP.Outside.L_lib_739.Adapt

namespace PEqualNP.Outside.L_lib_739.Bridge

open PEqualNP.Outside.L_lib_739.Adapt

def lift {n names : ℕ} (p : E n names) : V (n+1) := Fin.cons 1 p.2

def H {n names : ℕ} (D : Finset (E n names)) (y : Fin names) : Submodule F (V (n+1)) :=
  Submodule.span F (((D.filter (fun p => p.1 = y)).image lift : Finset (V (n+1))) : Set (V (n+1)))

lemma neg_mem {n names : ℕ} {D : Finset (E n names)} {p : E n names} (hp : p ∈ D) :
    lift p ∈ H D p.1 := by
  apply Submodule.subset_span
  exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩

theorem fixed_iff_maps {n names m q : ℕ} (D : Finset (E n names)) (P : Fin m → Finset (E n names)) :
    fixed q D P ↔ ∃ L : (y : Fin names) → (V (n+1) ⧸ H D y) →ₗ[F] V q,
      ∀ cell, ∃ p ∈ P cell, L p.1 ((H D p.1).mkQ (lift p)) ≠ 0 := by
  classical
  constructor
  · rintro ⟨c, hn, hp⟩
    let f (y : Fin names) : V (n+1) →ₗ[F] V q :=
      LinearMap.pi (fun j => dotProductEquiv F (Fin (n+1)) (c y j))
    have vanish (y : Fin names) : H D y ≤ LinearMap.ker (f y) := by
      apply Submodule.span_le.mpr
      intro z hz
      obtain ⟨p, hpD, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hpD, hy⟩ := Finset.mem_filter.mp hpD
      apply LinearMap.mem_ker.mpr
      funext j
      change dotProduct (c y j) (lift p) = 0
      rw [← hy]
      exact hn p hpD j
    refine ⟨fun y => (H D y).liftQ (f y) (vanish y), ?_⟩
    intro cell
    obtain ⟨p, hpP, j, hj⟩ := hp cell
    refine ⟨p, hpP, ?_⟩
    change f p.1 (lift p) ≠ 0
    intro he
    exact one_ne_zero (hj.symm.trans (congrFun he j))
  · rintro ⟨L,hL⟩
    let ell (y : Fin names) (j : Fin q) : V (n+1) →ₗ[F] F :=
      (LinearMap.proj j : V q →ₗ[F] F).comp ((L y).comp (H D y).mkQ)
    refine ⟨fun y j => (dotProductEquiv F (Fin (n+1))).symm (ell y j), ?_, ?_⟩
    · intro p hp j
      rw [dual_eval]
      change L p.1 ((H D p.1).mkQ (lift p)) j = 0
      have he : (H D p.1).mkQ (lift p) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (neg_mem hp)
      simp [he]
    · intro cell
      obtain ⟨p,hp,hn⟩ := hL cell
      have he : ∃ j, L p.1 ((H D p.1).mkQ (lift p)) j ≠ 0 := by
        by_contra! hall
        exact hn (funext hall)
      obtain ⟨j,hj⟩ := he
      refine ⟨p,hp,j,?_⟩
      rw [dual_eval]
      exact bit_one _ hj

theorem obstruction {n names m q : ℕ} (D : Finset (E n names)) (P : Fin m → Finset (E n names))
    (y : Fin names) (T : Submodule F (V (n+1) ⧸ H D y)) (d : Fin m → V (n+1) ⧸ H D y)
    (ht : Module.finrank F T = q+1) (hr : Set.range d = (T : Set (V (n+1) ⧸ H D y)) \ {0})
    (hall : ∀ i, ∀ p ∈ P i, lift p ∉ H D p.1 → p.1 = y ∧ (H D y).mkQ (lift p) = d i) :
    ¬fixed q D P := by
  classical
  intro hs
  obtain ⟨L,hL⟩ := (fixed_iff_maps D P).mp hs
  let f : T →ₗ[F] V q := (L y).comp T.subtype
  have hdim : Module.finrank F (V q) < Module.finrank F T := by
    rw [ht]
    change Module.finrank F (Fin q → F) < q + 1
    simp
  have hk : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨w,hw,hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have nz : (w : V (n+1) ⧸ H D y) ≠ 0 := fun e => hn (Subtype.ext e)
  have hrw : (w : V (n+1) ⧸ H D y) ∈ Set.range d := by
    rw [hr]
    exact ⟨w.property, nz⟩
  obtain ⟨i,hi⟩ := hrw
  obtain ⟨⟨z,x⟩,hp,hnz⟩ := hL i
  have survives : lift (z,x) ∉ H D z := by
    intro h
    apply hnz
    change L z ((H D z).mkQ (lift (z,x))) = 0
    rw [show (H D z).mkQ (lift (z,x)) = 0 from (Submodule.Quotient.mk_eq_zero _).mpr h, map_zero]
  obtain ⟨hy,hit⟩ := hall i (z,x) hp survives
  change z = y at hy
  subst z
  change L y ((H D y).mkQ (lift (y,x))) ≠ 0 at hnz
  rw [hit,hi] at hnz
  exact hnz (LinearMap.mem_ker.mp hw)

end PEqualNP.Outside.L_lib_739.Bridge

namespace PEqualNP.Outside.L_lib_739.Rigidity

open PEqualNP.Outside.L_lib_739.Adapt PEqualNP.Outside.L_lib_739.Bridge

def classification (U : Type) [AddCommGroup U] [Module F U] (q : ℕ) : Prop :=
  ∀ (k : ℕ) (b : Fin k → U), (∀ i, b i ≠ 0) → k < 2^(q+1) →
    (¬∃ f : U →ₗ[F] V q, ∀ i, f (b i) ≠ 0) →
    k+1 = 2^(q+1) ∧ Function.Injective b ∧
      ∃ T : Submodule F U, Module.finrank F T = q+1 ∧ Set.range b = (T : Set U) \ {0}

theorem selection {n names m q : ℕ} (D : Finset (E n names)) (P : Fin m → Finset (E n names))
    (classify : ∀ y, classification (V (n+1) ⧸ H D y) q)
    (s : Fin m → E n names) (hm : ∀ i, s i ∈ P i) (hs : ∀ i, lift (s i) ∉ H D (s i).1)
    (bound : m < 2^(q+1)) (hns : ¬fixed q D P) :
    m+1 = 2^(q+1) ∧ ∃ y : Fin names, (∀ i, (s i).1 = y) ∧
      Function.Injective (fun i => (H D y).mkQ (lift (s i))) ∧
      ∃ T : Submodule F (V (n+1) ⧸ H D y), Module.finrank F T = q+1 ∧
        Set.range (fun i => (H D y).mkQ (lift (s i))) = (T : Set (V (n+1) ⧸ H D y)) \ {0} := by
  classical
  have bad : ∃ y, ¬∃ L : (V (n+1) ⧸ H D y) →ₗ[F] V q,
      ∀ i, (s i).1 = y → L ((H D y).mkQ (lift (s i))) ≠ 0 := by
    by_contra! h
    choose L good using h
    apply hns
    exact (fixed_iff_maps D P).mpr ⟨L, fun i => ⟨s i, hm i, good _ i rfl⟩⟩
  obtain ⟨y,hy⟩ := bad
  let I := {i : Fin m // (s i).1 = y}
  let k := Fintype.card I
  let e : Fin k ≃ I := (Fintype.equivFin I).symm
  let b (i : Fin k) := (H D y).mkQ (lift (s (e i).val))
  have nonzero (i : Fin k) : b i ≠ 0 := by
    intro hz
    have h := hs (e i).val
    rw [(e i).property] at h
    exact h ((Submodule.Quotient.mk_eq_zero _).mp hz)
  have small : k ≤ m := by
    simpa only [k,Fintype.card_fin] using
      Fintype.card_le_of_injective (fun z : I => (z.val : Fin m)) Subtype.val_injective
  have blocks : ¬∃ L : (V (n+1) ⧸ H D y) →ₗ[F] V q, ∀ i, L (b i) ≠ 0 := by
    rintro ⟨L,hl⟩
    apply hy
    refine ⟨L, fun i hi => ?_⟩
    simpa only [b, Equiv.apply_symm_apply] using hl (e.symm ⟨i,hi⟩)
  have sharp := (classify y k b nonzero (lt_of_le_of_lt small bound) blocks).1
  have equal : k = m := by omega
  have surj : Function.Surjective (fun z : I => (z.val : Fin m)) := by
    apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨Subtype.val_injective, ?_⟩).surjective
    simpa only [Fintype.card_fin] using equal
  have same (i : Fin m) : (s i).1 = y := by
    obtain ⟨z,hz⟩ := surj i
    exact hz ▸ z.property
  let d (i : Fin m) := (H D y).mkQ (lift (s i))
  have nz (i : Fin m) : d i ≠ 0 := by
    intro hz
    have h := hs i
    rw [same i] at h
    exact h ((Submodule.Quotient.mk_eq_zero _).mp hz)
  have blocked : ¬∃ L : (V (n+1) ⧸ H D y) →ₗ[F] V q, ∀ i, L (d i) ≠ 0 := by
    rintro ⟨L,hl⟩
    exact hy ⟨L, fun i _ => hl i⟩
  obtain ⟨total, hinj, hT⟩ := classify y m d nz bound blocked
  exact ⟨total,y,same,hinj,hT⟩

lemma replace_forced {U : Type} [AddCommGroup U] [Module F U] {m : ℕ}
    (a b : Fin m → U) (i j : Fin m) (hji : j ≠ i) (hinj : Function.Injective a)
    (same : ∀ k, k ≠ i → b k = a k) (T T' : Submodule F U)
    (ha : Set.range a = (T : Set U) \ {0}) (hb : Set.range b = (T' : Set U) \ {0}) :
    b i = a i := by
  have am (k : Fin m) : a k ∈ T ∧ a k ≠ 0 := by
    have h : a k ∈ Set.range a := ⟨k,rfl⟩
    rwa [ha] at h
  have bm (k : Fin m) : b k ∈ T' := by
    have h : b k ∈ Set.range b := ⟨k,rfl⟩
    rw [hb] at h
    exact h.1
  let z := a i - a j
  have zn : z ≠ 0 := sub_ne_zero.mpr (fun h => hji (hinj h).symm)
  have other : z ≠ a i := by
    intro h
    exact (am j).2 (sub_eq_self.mp h)
  obtain ⟨k,hk⟩ : z ∈ Set.range a := by
    rw [ha]
    exact ⟨T.sub_mem (am i).1 (am j).1, zn⟩
  have hki : k ≠ i := fun e => other (by simpa only [e] using hk.symm)
  have zj : a j ∈ T' := same j hji ▸ bm j
  have zk : z ∈ T' := hk ▸ (same k hki ▸ bm k)
  have last : a i ∈ T' := by
    simpa only [z,sub_add_cancel] using T'.add_mem zk zj
  obtain ⟨l,hl⟩ : a i ∈ Set.range b := by
    rw [hb]
    exact ⟨last,(am i).2⟩
  by_cases e : l = i
  · simpa only [e] using hl
  · exact (e (hinj ((same l e).symm.trans hl))).elim

theorem forward {n names m q : ℕ} (hq : 0 < q) (D : Finset (E n names)) (P : Fin m → Finset (E n names))
    (classify : ∀ y, classification (V (n+1) ⧸ H D y) q)
    (surv : ∀ i, ∃ p ∈ P i, lift p ∉ H D p.1) (bound : m < 2^(q+1)) (hns : ¬fixed q D P) :
    m+1 = 2^(q+1) ∧
    ∃ (y : Fin names) (T : Submodule F (V (n+1) ⧸ H D y)) (d : Fin m → V (n+1) ⧸ H D y),
      Module.finrank F T = q+1 ∧ Function.Injective d ∧
      Set.range d = (T : Set (V (n+1) ⧸ H D y)) \ {0} ∧
      ∀ i, ∀ p ∈ P i, lift p ∉ H D p.1 → p.1 = y ∧ (H D y).mkQ (lift p) = d i := by
  classical
  choose s hm hs using surv
  obtain ⟨sharp,y,hy,hinj,T,ht,hr⟩ := selection D P classify s hm hs bound hns
  have hm2 : 1 < m := by
    have hpow : 2^2 ≤ 2^(q+1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  refine ⟨sharp,y,T,fun i => (H D y).mkQ (lift (s i)),ht,hinj,hr,?_⟩
  intro i p hp hsp
  let u := Function.update s i p
  have same (k : Fin m) (hk : k ≠ i) : u k = s k := Function.update_of_ne hk _ _
  have mem (k : Fin m) : u k ∈ P k := by
    by_cases hk : k = i
    · subst k
      simpa [u] using hp
    · rw [same k hk]
      exact hm k
  have nz (k : Fin m) : lift (u k) ∉ H D (u k).1 := by
    by_cases hk : k = i
    · subst k
      simpa [u] using hsp
    · rw [same k hk]
      exact hs k
  obtain ⟨_,z,hz,_,S,_,hr'⟩ := selection D P classify u mem nz bound hns
  obtain ⟨j,hji⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin m) (by simpa using hm2) i
  have zy : z = y := (hz j).symm.trans ((congrArg Prod.fst (same j hji)).trans (hy j))
  subst z
  refine ⟨by simpa [u] using hz i,?_⟩
  have forced := replace_forced _ _ i j hji hinj
    (fun k hk => congrArg (fun z => (H D y).mkQ (lift z)) (same k hk)) T S hr hr'
  simpa [u] using forced

end PEqualNP.Outside.L_lib_739.Rigidity

namespace PEqualNP.Outside.L_lib_739.Geometry
abbrev B := ZMod 2

variable {M : Type*} [AddCommGroup M] [Module B M]
variable {ι : Type*} [Fintype ι]

lemma bit (a : B) : a = 0 ∨ a = 1 := by
  exact (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) a

lemma twice (x : M) : x + x = 0 := by
  have h : (1 + 1 : B) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun a : B => a • x) h

variable [Finite M]

lemma projection {q : Nat} (d : ι → M) (hn : ∀ i, d i ≠ 0)
    (hm : Fintype.card ι < 2 ^ (q + 1))
    (hb : ∀ f : M →ₗ[B] (Fin q → B), ∃ i, f (d i) = 0)
    (u : M) (hu : ∀ i, d i ≠ u) :
    ∃ K : Submodule B M, u ∈ K ∧ Fintype.card ι + 1 = 2 ^ (q + 1) ∧
      Function.Injective (fun i => K.mkQ (d i)) := by
  classical
  let P := fun K : Submodule B M => ∀ i, d i ∉ K
  have hline : P (Submodule.span B {u}) := by
    intro i hi
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hi
    rcases bit a with rfl | rfl
    · exact hn i (by simpa using ha.symm)
    · exact hu i (by simpa using ha.symm)
  obtain ⟨K, hlineK, hK⟩ := Finite.exists_le_maximal hline
  have hcover : ∀ t : M ⧸ K, t ≠ 0 → ∃ i, K.mkQ (d i) = t := by
    intro t ht
    by_contra! hnone
    let L := (Submodule.span B {t}).comap K.mkQ
    have hKL : K ≤ L := by
      intro x hx
      change K.mkQ x ∈ Submodule.span B {t}
      rw [show K.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero K).2 hx]
      exact Submodule.zero_mem _
    have hL : P L := by
      intro i hi
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (show K.mkQ (d i) ∈ Submodule.span B {t} from hi)
      rcases bit a with rfl | rfl
      · exact hK.prop i ((Submodule.Quotient.mk_eq_zero K).1 (by simpa using ha.symm))
      · exact hnone i (by simpa using ha.symm)
    obtain ⟨v, hv⟩ := K.mkQ_surjective t
    have hvL : v ∈ L := by
      change K.mkQ v ∈ Submodule.span B {t}
      rw [hv]
      exact Submodule.mem_span_singleton_self _
    exact ht (hv.symm.trans ((Submodule.Quotient.mk_eq_zero K).2 (hK.le_of_ge hL hKL hvL)))
  have hd : q < Module.finrank B (M ⧸ K) := by
    by_contra! he
    obtain ⟨g, hg⟩ := (finrank_le_iff_exists_linearMap (R := B) (M := M ⧸ K) (M' := Fin q → B)).1 (by simpa using he)
    obtain ⟨i, hi⟩ := hb (g.comp K.mkQ)
    exact hK.prop i ((Submodule.Quotient.mk_eq_zero K).1 (hg (by simpa using hi)))
  let f : Option ι → M ⧸ K := fun i => i.elim 0 (fun j => K.mkQ (d j))
  have hf : Function.Surjective f := by
    intro t
    by_cases ht : t = 0
    · exact ⟨none, ht.symm⟩
    · obtain ⟨i, hi⟩ := hcover t ht
      exact ⟨some i, hi⟩
  let _ : Finite (M ⧸ K) := Finite.of_surjective K.mkQ K.mkQ_surjective
  let _ := Fintype.ofFinite (M ⧸ K)
  have hc : Fintype.card (M ⧸ K) = 2 ^ Module.finrank B (M ⧸ K) := by
    simpa [B] using (Module.card_eq_pow_finrank (K := B) (V := M ⧸ K))
  have ha := Fintype.card_le_of_surjective f hf
  rw [hc, Fintype.card_option] at ha
  have hq := Nat.pow_le_pow_right (n := 2) (by decide) hd
  have heq : Fintype.card ι + 1 = 2 ^ (q + 1) := by omega
  have hbij := (Fintype.bijective_iff_surjective_and_card f).2 ⟨hf, by rw [Fintype.card_option, hc]; omega⟩
  exact ⟨K, hlineK (Submodule.mem_span_singleton_self u), heq, fun i j h => Option.some.inj (hbij.1 (show f (some i) = f (some j) from h))⟩
lemma flat {q : Nat} (d : ι → M) (hn : ∀ i, d i ≠ 0)
    (hm : Fintype.card ι < 2 ^ (q + 1))
    (hb : ∀ f : M →ₗ[B] (Fin q → B), ∃ i, f (d i) = 0) :
    Fintype.card ι + 1 = 2 ^ (q + 1) ∧ Function.Injective d ∧
      ∃ T : Submodule B M, Module.finrank B T = q + 1 ∧
        Set.range d = (T : Set M) \ {0} := by
  classical
  obtain ⟨K, -, heq, hKI⟩ := projection d hn hm hb 0 hn
  have hd : Function.Injective d := fun _ _ h => hKI (congrArg K.mkQ h)
  have hadd (i j : ι) : d i + d j = 0 ∨ ∃ k, d k = d i + d j := by
    by_contra! h
    obtain ⟨J, hsum, -, hJI⟩ := projection d hn hm hb (d i + d j) h.2
    have hj : J.mkQ (d i) + J.mkQ (d j) = 0 := by
      rw [← map_add, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero J).2 hsum
    have hij : J.mkQ (d i) = J.mkQ (d j) := by
      calc
        _ = J.mkQ (d i) + (J.mkQ (d j) + J.mkQ (d j)) := by rw [twice, add_zero]
        _ = _ := by rw [← add_assoc, hj, zero_add]
    exact h.1 (by rw [hJI hij, twice])
  let T : Submodule B M := {
    carrier := {x | x = 0 ∨ ∃ i, d i = x}
    zero_mem' := Or.inl rfl, add_mem' := by
      rintro a b (rfl | ⟨i, rfl⟩) (rfl | ⟨j, rfl⟩)
      · exact Or.inl (zero_add _)
      · exact Or.inr ⟨j, (zero_add _).symm⟩
      · exact Or.inr ⟨i, (add_zero _).symm⟩
      · exact hadd i j
    smul_mem' := by
      intro c a ha
      rcases bit c with rfl | rfl
      · exact Or.inl (zero_smul _ _)
      · simpa only [one_smul] using ha }
  have hr : Set.range d = (T : Set M) \ {0} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Or.inr ⟨i, rfl⟩, hn i⟩
    · rintro ⟨h, hx⟩
      exact h.resolve_left hx
  let f : Option ι → T
    | none => ⟨0, T.zero_mem⟩
    | some i => ⟨d i, Or.inr ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hh := congrArg Subtype.val hab
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some j => exact False.elim (hn j hh.symm)
      | some i =>
        cases b with
        | none => exact False.elim (hn i hh)
        | some j => exact congrArg some (hd hh)
    · rintro ⟨x, hx⟩
      rcases hx with rfl | ⟨i, rfl⟩
      · exact ⟨none, rfl⟩
      · exact ⟨some i, rfl⟩
  let _ := Fintype.ofFinite T
  refine ⟨heq, hd, T, ?_, hr⟩
  apply Nat.pow_right_injective (a := 2) (by decide)
  calc
    2 ^ Module.finrank B T = Fintype.card T := by
      simpa [B] using (Module.card_eq_pow_finrank (K := B) (V := T)).symm
    _ = Fintype.card (Option ι) := (Fintype.card_congr (Equiv.ofBijective f hf)).symm
    _ = _ := by simpa using heq
lemma quotientClassified (K : Submodule B M) (q : Nat) :
    ∀ (k : Nat) (b : Fin k → M ⧸ K), (∀ i, b i ≠ 0) → k < 2 ^ (q + 1) →
      (¬∃ f : (M ⧸ K) →ₗ[B] (Fin q → B), ∀ i, f (b i) ≠ 0) →
      k + 1 = 2 ^ (q + 1) ∧ Function.Injective b ∧
        ∃ T : Submodule B (M ⧸ K), Module.finrank B T = q + 1 ∧
          Set.range b = (T : Set (M ⧸ K)) \ {0} := by
  classical
  let _ : Finite (M ⧸ K) := Finite.of_surjective K.mkQ K.mkQ_surjective
  intro k b hn hm hb
  have hblock (f : (M ⧸ K) →ₗ[B] (Fin q → B)) : ∃ i, f (b i) = 0 := by
    by_contra! h
    exact hb ⟨f, h⟩
  simpa only [Fintype.card_fin] using
    flat b hn (by simpa only [Fintype.card_fin] using hm) hblock

end PEqualNP.Outside.L_lib_739.Geometry

open PEqualNP.Outside.L_lib_739 in

theorem PEqualNP.Outside.L_lib_739 : (∀ (n names m q : Nat), 0 < q →
  let F := ZMod 2
  let V := Fin n → F
  let W := Fin (n+1) → F
  let E := Fin names × V
  let lift := fun (p : E) => Fin.cons (1 : F) p.2
  ∀ (negative : Finset E) (positive : Fin m → Finset E),
    let H := fun (y : Fin names) => Submodule.span F
      (((negative.filter (fun p => p.1 = y)).image lift : Finset W) : Set W)
    let safe := ∃ coeff : Fin names → Fin q → W,
      (∀ p ∈ negative, ∀ j, dotProduct (coeff p.1 j) (lift p) = 0) ∧
      (∀ cell, ∃ p ∈ positive cell, ∃ j, dotProduct (coeff p.1 j) (lift p) = 1)
    let adaptive := ∃
      (ask : (j : Fin q) → Fin names → (Fin j.val → F) → (V →ₗ[F] F))
      (ans : E → Fin q → F) (take : Fin names → (Fin q → F) → Bool),
      (∀ (p : E) (j : Fin q), ans p j =
        ask j p.1 (fun earlier => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p.2) ∧
      (∀ p ∈ negative, take p.1 (ans p) = false) ∧
      (∀ cell, ∃ p ∈ positive cell, take p.1 (ans p) = true)
    ((∀ y, (negative.filter (fun p => p.1 = y)).card ≤ 1) → (adaptive ↔ safe)) ∧
    ((∀ cell, ∃ p ∈ positive cell, lift p ∉ H p.1) → m < 2^(q+1) →
      ((¬safe) ↔
        m + 1 = 2^(q+1) ∧
        ∃ (y : Fin names) (T : Submodule F (W ⧸ H y)) (d : Fin m → W ⧸ H y),
          Module.finrank F T = q+1 ∧ Function.Injective d ∧
          Set.range d = (T : Set (W ⧸ H y)) \ {0} ∧
          ∀ cell, ∀ p ∈ positive cell, lift p ∉ H p.1 →
            p.1 = y ∧ (H y).mkQ (lift p) = d cell))) := by
  intro n names m q hq
  dsimp only
  intro D P
  constructor
  · intro hn
    exact Adapt.equivalence hq D P hn
  · intro survives bound
    constructor
    · intro hns
      exact Rigidity.forward hq D P (fun y => Geometry.quotientClassified (Bridge.H D y) q)
        survives bound hns
    · rintro ⟨_, y, T, d, hdim, _, hrange, hall⟩
      exact Bridge.obstruction D P y T d hdim hrange hall
