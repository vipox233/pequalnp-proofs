import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_881_aux

def Shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧ (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def Cons {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) : Prop :=
  ∀ (j : Fin p.length), q (List.take (↑j) p) x = p.get j

def AffQ (n : ℕ) (g : (Fin n → ZMod 2) → Bool) : Prop :=
  ∃ (l : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), g = fun x => decide (l x = b)

def Tree {n m : ℕ} (f : (Fin n → ZMod 2) → Fin m) (N J : Finset (List Bool))
    (q : List Bool → (Fin n → ZMod 2) → Bool) (out : List Bool → Fin m) : Prop :=
  Shape N J ∧ (∀ p ∈ J, AffQ n (q p)) ∧ ∀ p ∈ N \ J, ∀ x : Fin n → ZMod 2, Cons q p x → f x = out p

lemma ff_cons_iff {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) :
    Cons q p x ↔ ∀ (j : ℕ) (h : j < p.length), q (p.take j) x = p[j] := by
  constructor
  · intro h j hj
    exact h ⟨j, hj⟩
  · intro h j
    exact h j.1 j.2

lemma ff_cons_ext {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V)
    (h : Cons q p x) : Cons q (p ++ [q p x]) x := by
  rw [ff_cons_iff] at h ⊢
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h1 | h1
  · rw [List.take_append_of_le_length h1.le, List.getElem_append_left h1]
    exact h j h1
  · subst h1
    simp

lemma ff_reach_aux {V : Type} (N J : Finset (List Bool)) (hS : Shape N J)
    (q : List Bool → V → Bool) (x : V) (d : ℕ) :
    ∃ p ∈ N, Cons q p x ∧ (p ∉ J ∨ d ≤ p.length) := by
  induction d with
  | zero => exact ⟨[], hS.1, fun j => j.elim0, Or.inr (Nat.zero_le _)⟩
  | succ d ih =>
    obtain ⟨p, hp, hc, h⟩ := ih
    by_cases hJ : p ∈ J
    · refine ⟨p ++ [q p x], ?_, ff_cons_ext q p x hc, Or.inr ?_⟩
      · have h2 := hS.2.2.2 p hJ
        cases q p x
        · exact h2.1
        · exact h2.2
      · have h3 : d ≤ p.length := h.resolve_left (not_not.mpr hJ)
        rw [List.length_append, List.length_singleton]
        omega
    · exact ⟨p, hp, hc, Or.inl hJ⟩

lemma ff_reach {V : Type} (N J : Finset (List Bool)) (hS : Shape N J)
    (q : List Bool → V → Bool) (x : V) : ∃ p ∈ N \ J, Cons q p x := by
  obtain ⟨p, hp, hc, h⟩ := ff_reach_aux N J hS q x (N.sup List.length + 1)
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hp, ?_⟩, hc⟩
  rcases h with h | h
  · exact h
  · have h1 := Finset.le_sup (f := List.length) hp
    omega

lemma ff_internal (N J : Finset (List Bool)) (hS : Shape N J) (p s : List Bool)
    (hs : s ≠ []) (h : p ++ s ∈ N) : p ∈ J := by
  induction s using List.reverseRecOn with
  | nil => exact absurd rfl hs
  | append_singleton s b ih =>
    rw [← List.append_assoc] at h
    have h1 := hS.2.2.1 _ b h
    by_cases hs1 : s = []
    · subst hs1
      simpa using h1
    · exact ih hs1 (hS.2.1 h1)

lemma ff_pf (N J : Finset (List Bool)) (hS : Shape N J) (p r : List Bool)
    (hp : p ∈ N \ J) (hr : r ∈ N \ J) (h : p <+: r) : p = r := by
  obtain ⟨s, hs⟩ := h
  by_cases hs0 : s = []
  · subst hs0
    simpa using hs
  · have h3 : p ++ s ∈ N := by
      rw [hs]
      exact (Finset.mem_sdiff.mp hr).1
    exact absurd (ff_internal N J hS p s hs0 h3) (Finset.mem_sdiff.mp hp).2

lemma ff_take_J (N J : Finset (List Bool)) (hS : Shape N J) (p : List Bool) (hp : p ∈ N)
    (k : ℕ) (hk : k < p.length) : p.take k ∈ J := by
  apply ff_internal N J hS (p.take k) (p.drop k)
  · intro h
    have := congrArg List.length h
    simp at this
    omega
  · rw [List.take_append_drop]
    exact hp

theorem ff_z2 : ∀ s t b : ZMod 2, (decide (s = b) = decide (t = b)) ↔ s = t := by decide

lemma ff_aff {n : ℕ} (q : List Bool → (Fin n → ZMod 2) → Bool) (p : List Bool)
    (hq : ∀ j : Fin p.length, AffQ n (q (p.take j))) (v : Fin n → ZMod 2) (hv : Cons q p v) :
    ∃ A : Submodule (ZMod 2) (Fin n → ZMod 2), ∀ x, x - v ∈ A ↔ Cons q p x := by
  choose l b hl using hq
  refine ⟨⨅ j, LinearMap.ker (l j), fun x => ?_⟩
  rw [Submodule.mem_iInf]
  unfold Cons at hv ⊢
  apply forall_congr'
  intro j
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero, ← hv j, hl j]
  exact (ff_z2 _ _ _).symm

lemma ff_pre_succ (A B : List Bool) (k : ℕ) (hA : k < A.length) (hB : k < B.length)
    (h : A.take k <+: B) (he : B[k] = A[k]) : A.take (k+1) <+: B := by
  rw [List.prefix_iff_eq_take] at h
  have h1 : (A.take k).length = k := by simp; omega
  rw [h1] at h
  have h2 : A.take (k+1) = B.take (k+1) := by
    rw [List.take_add_one, List.take_add_one, h, List.getElem?_eq_getElem hA,
      List.getElem?_eq_getElem hB, he]
  rw [h2]
  exact List.take_prefix _ _

theorem fwd {n m : ℕ} (f : (Fin n → ZMod 2) → Fin m) (Q : Finset (Fin m))
    (hQ : Q ⊆ Finset.univ.image f) (N J : Finset (List Bool))
    (q : List Bool → (Fin n → ZMod 2) → Bool) (out : List Bool → Fin m)
    (hT : Tree f N J q out) (hc : ∀ a ∈ Q, ((N \ J).filter (fun p => out p = a)).card = 1) :
    (∀ a ∈ Q, ∃ (v : Fin n → ZMod 2) (A : Submodule (ZMod 2) (Fin n → ZMod 2)), ∀ x, x-v ∈ A ↔ f x = a) ∧
    ∀ S ⊆ Q, 1 < S.card → ∃ h : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      (∀ x y : Fin n → ZMod 2, f x ∈ S → f x = f y → h x = h y) ∧
      ∃ x y : Fin n → ZMod 2, f x ∈ S ∧ f y ∈ S ∧ h x ≠ h y := by
  classical
  obtain ⟨hS, hA, hL⟩ := hT
  have hex : ∀ a, ∃ p, a ∈ Q → p ∈ N \ J ∧ out p = a := by
    intro a
    by_cases ha : a ∈ Q
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (hc a ha)
      have hp' : p ∈ (N \ J).filter (fun p => out p = a) := by
        rw [hp]
        exact Finset.mem_singleton_self p
      exact ⟨p, fun _ => Finset.mem_filter.mp hp'⟩
    · exact ⟨[], fun h => absurd h ha⟩
  choose lf hlf using hex
  have hR : ∀ a ∈ Q, ∀ x, f x = a → Cons q (lf a) x := by
    intro a ha x hx
    obtain ⟨r, hr, hcr⟩ := ff_reach N J hS q x
    have h1 : out r = a := by
      rw [← hL r hr x hcr]
      exact hx
    have h2 : lf a = r := Finset.card_le_one.mp (hc a ha).le _
      (Finset.mem_filter.mpr ⟨(hlf a ha).1, (hlf a ha).2⟩) _ (Finset.mem_filter.mpr ⟨hr, h1⟩)
    rw [h2]
    exact hcr
  have hpt : ∀ a ∈ Q, ∃ x, f x = a := by
    intro a ha
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp (hQ ha)
    exact ⟨x, hx⟩
  refine ⟨fun a ha => ?_, fun S hSQ hS1 => ?_⟩
  · obtain ⟨v, hv⟩ := hpt a ha
    have hJ : ∀ j : Fin (lf a).length, AffQ n (q ((lf a).take j)) := fun j =>
      hA _ (ff_take_J N J hS (lf a) (Finset.mem_sdiff.mp (hlf a ha).1).1 j j.2)
    obtain ⟨A, hA'⟩ := ff_aff q (lf a) hJ v (hR a ha v hv)
    refine ⟨v, A, fun x => (hA' x).trans ⟨fun h => ?_, hR a ha x⟩⟩
    rw [hL _ (hlf a ha).1 x h]
    exact (hlf a ha).2
  · obtain ⟨a0, ha0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have hleaf : ∀ a ∈ S, lf a ∈ N \ J := fun a ha => (hlf a (hSQ ha)).1
    have hout : ∀ a ∈ S, out (lf a) = a := fun a ha => (hlf a (hSQ ha)).2
    obtain ⟨K, hKdef⟩ : ∃ K, K = Nat.findGreatest (fun k => ∀ a ∈ S, (lf a0).take k <+: lf a)
      (lf a0).length := ⟨_, rfl⟩
    have hPK : ∀ a ∈ S, (lf a0).take K <+: lf a := by
      rw [hKdef]
      exact Nat.findGreatest_spec (P := fun k => ∀ a ∈ S, (lf a0).take k <+: lf a)
        (Nat.zero_le _) (fun a _ => by simp)
    have hKle : K ≤ (lf a0).length := by
      rw [hKdef]
      exact Nat.findGreatest_le _
    have hKlt : K < (lf a0).length := by
      by_contra hcon
      have hK : K = (lf a0).length := by omega
      have hall : ∀ a ∈ S, a = a0 := by
        intro a ha
        have h1 := hPK a ha
        rw [hK, List.take_length] at h1
        have h2 := ff_pf N J hS _ _ (hleaf a0 ha0) (hleaf a ha) h1
        rw [← hout a ha, ← hout a0 ha0, h2]
      have : S.card ≤ 1 :=
        Finset.card_le_one.mpr (fun a ha b hb => (hall a ha).trans (hall b hb).symm)
      omega
    have hclen : ((lf a0).take K).length = K := by
      simp
      omega
    have hlong : ∀ a ∈ S, K < (lf a).length := by
      intro a ha
      by_contra hcon
      have h1 := hPK a ha
      have h2 : (lf a0).take K = lf a := h1.eq_of_length (by have := h1.length_le; omega)
      have h3 : lf a <+: lf a0 := h2 ▸ List.take_prefix _ _
      have h4 := ff_pf N J hS _ _ (hleaf a ha) (hleaf a0 ha0) h3
      rw [h4] at h2
      have := congrArg List.length h2
      omega
    have htake : ∀ a ∈ S, (lf a).take K = (lf a0).take K := by
      intro a ha
      have h1 := List.prefix_iff_eq_take.mp (hPK a ha)
      rw [hclen] at h1
      exact h1.symm
    obtain ⟨a1, ha1, hb1⟩ : ∃ a1, ∃ ha1 : a1 ∈ S, (lf a1)[K]'(hlong a1 ha1) ≠ (lf a0)[K]'hKlt := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      have h1 : ∀ a ∈ S, (lf a0).take (K+1) <+: lf a := fun a ha =>
        ff_pre_succ (lf a0) (lf a) K hKlt (hlong a ha) (hPK a ha) (hcon a ha)
      rw [hKdef] at h1 hKlt
      exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hKlt h1
    have hcJ : (lf a0).take K ∈ J :=
      ff_take_J N J hS (lf a0) (Finset.mem_sdiff.mp (hleaf a0 ha0)).1 K hKlt
    obtain ⟨l, β0, hq⟩ := hA _ hcJ
    have hkey : ∀ a (ha : a ∈ S), ∀ x, f x = a → decide (l x = β0) = (lf a)[K]'(hlong a ha) := by
      intro a ha x hx
      have h1 := (ff_cons_iff q (lf a) x).mp (hR a (hSQ ha) x hx) K (hlong a ha)
      rw [htake a ha, hq] at h1
      exact h1
    refine ⟨l, fun x y hx hxy => ?_, ?_⟩
    · have h1 := hkey _ hx x rfl
      have h2 := hkey _ hx y hxy.symm
      exact (ff_z2 _ _ _).mp (h1.trans h2.symm)
    · obtain ⟨x1, hx1⟩ := hpt a1 (hSQ ha1)
      obtain ⟨x0, hx0⟩ := hpt a0 (hSQ ha0)
      refine ⟨x1, x0, by rw [hx1]; exact ha1, by rw [hx0]; exact ha0, fun he => hb1 ?_⟩
      rw [← hkey a1 ha1 x1 hx1, he, hkey a0 ha0 x0 hx0]

def bb_nn (N0 N1 : Finset (List Bool)) : Finset (List Bool) :=
  insert [] (N0.image (List.cons false) ∪ N1.image (List.cons true))

theorem bb_nn_nil (N0 N1 : Finset (List Bool)) : [] ∈ bb_nn N0 N1 := by simp [bb_nn]

theorem bb_nn_false (N0 N1 : Finset (List Bool)) (r : List Bool) :
    (false :: r) ∈ bb_nn N0 N1 ↔ r ∈ N0 := by simp [bb_nn]

theorem bb_nn_true (N0 N1 : Finset (List Bool)) (r : List Bool) :
    (true :: r) ∈ bb_nn N0 N1 ↔ r ∈ N1 := by simp [bb_nn]

theorem bb_nn_shape (N0 J0 N1 J1 : Finset (List Bool)) (h0 : Shape N0 J0) (h1 : Shape N1 J1) :
    Shape (bb_nn N0 N1) (bb_nn J0 J1) := by
  refine ⟨bb_nn_nil _ _, ?_, ?_, ?_⟩
  · intro p hp
    rcases p with _ | ⟨c, r⟩
    · exact bb_nn_nil _ _
    · cases c
      · rw [bb_nn_false] at hp ⊢
        exact h0.2.1 hp
      · rw [bb_nn_true] at hp ⊢
        exact h1.2.1 hp
  · intro p b hp
    rcases p with _ | ⟨c, r⟩
    · exact bb_nn_nil _ _
    · cases c
      · rw [List.cons_append, bb_nn_false] at hp
        rw [bb_nn_false]
        exact h0.2.2.1 r b hp
      · rw [List.cons_append, bb_nn_true] at hp
        rw [bb_nn_true]
        exact h1.2.2.1 r b hp
  · intro p hp
    rcases p with _ | ⟨c, r⟩
    · exact ⟨(bb_nn_false _ _ _).2 h0.1, (bb_nn_true _ _ _).2 h1.1⟩
    · cases c
      · rw [bb_nn_false] at hp
        rw [List.cons_append, List.cons_append, bb_nn_false, bb_nn_false]
        exact h0.2.2.2 r hp
      · rw [bb_nn_true] at hp
        rw [List.cons_append, List.cons_append, bb_nn_true, bb_nn_true]
        exact h1.2.2.2 r hp

theorem bb_nn_leaves (N0 J0 N1 J1 : Finset (List Bool)) :
    bb_nn N0 N1 \ bb_nn J0 J1 =
      (N0 \ J0).image (List.cons false) ∪ (N1 \ J1).image (List.cons true) := by
  ext p
  rcases p with _ | ⟨c, r⟩
  · simp [bb_nn]
  · cases c <;> simp [bb_nn]

def bb_nq {V : Type} (f : V → Bool) (q0 q1 : List Bool → V → Bool) : List Bool → V → Bool
  | [] => f
  | false :: r => q0 r
  | true :: r => q1 r

def bb_nout {O : Type} (o0 o1 : List Bool → O) : List Bool → O
  | [] => o0 []
  | false :: r => o0 r
  | true :: r => o1 r

theorem bb_cons {V : Type} (q : List Bool → V → Bool) (c : Bool) (p : List Bool) (x : V) :
    Cons q (c :: p) x ↔ q [] x = c ∧ Cons (fun r => q (c :: r)) p x := by
  unfold Cons
  constructor
  · intro h
    refine ⟨by simpa using h ⟨0, by simp⟩, fun j => ?_⟩
    have := h ⟨j.1 + 1, by simp⟩
    simpa using this
  · rintro ⟨h0, h1⟩ ⟨j, hj⟩
    rcases j with _ | j
    · simpa using h0
    · have := h1 ⟨j, by simpa using hj⟩
      simpa using this

def bb_Inv {n m : ℕ} (f : (Fin n → ZMod 2) → Fin m) (Q : Finset (Fin m))
    (Z : Finset (Fin n → ZMod 2)) : Prop :=
  ∀ a ∈ Q, (∃ x ∈ Z, f x = a) → ∀ y, f y = a → y ∈ Z

def bb_Good {n m : ℕ} (f : (Fin n → ZMod 2) → Fin m) (Q : Finset (Fin m))
    (Z : Finset (Fin n → ZMod 2)) (N J : Finset (List Bool))
    (q : List Bool → (Fin n → ZMod 2) → Bool) (out : List Bool → Fin m) : Prop :=
  Shape N J ∧ (∀ p ∈ J, AffQ n (q p)) ∧ (∀ p ∈ N \ J, ∀ x ∈ Z, Cons q p x → f x = out p) ∧
    ∀ a ∈ Q, ((N \ J).filter (fun p => out p = a)).card = if (∃ x ∈ Z, f x = a) then 1 else 0

theorem bb_count {m : ℕ} (N0 J0 N1 J1 : Finset (List Bool)) (o0 o1 : List Bool → Fin m) (a : Fin m) :
    ((bb_nn N0 N1 \ bb_nn J0 J1).filter (fun p => bb_nout o0 o1 p = a)).card =
      ((N0 \ J0).filter (fun p => o0 p = a)).card + ((N1 \ J1).filter (fun p => o1 p = a)).card := by
  rw [bb_nn_leaves, Finset.filter_union, Finset.card_union_of_disjoint]
  · rw [Finset.filter_image, Finset.filter_image, Finset.card_image_of_injective _ (List.cons_injective),
      Finset.card_image_of_injective _ (List.cons_injective)]
    rfl
  · rw [Finset.disjoint_left]
    intro p h0 h1
    simp only [Finset.mem_filter, Finset.mem_image] at h0 h1
    obtain ⟨⟨r, -, rfl⟩, -⟩ := h0
    obtain ⟨⟨r', -, h⟩, -⟩ := h1
    simp at h

theorem bb_leaf {n m : ℕ} (f : (Fin n → ZMod 2) → Fin m) (Q : Finset (Fin m))
    (Z : Finset (Fin n → ZMod 2)) (x0 : Fin n → ZMod 2) (hx0 : x0 ∈ Z) (hall : ∀ x ∈ Z, f x = f x0) :
    ∃ N J q out, bb_Good f Q Z N J q out := by
  refine ⟨{[]}, ∅, fun _ _ => true, fun _ => f x0, ⟨by simp, by simp, ?_, by simp⟩, by simp, ?_, ?_⟩
  · intro p b hp
    simp at hp
  · intro p _ x hx _
    exact hall x hx
  · intro a _
    have : (∃ x ∈ Z, f x = a) ↔ f x0 = a :=
      ⟨fun ⟨x, hx, h⟩ => (hall x hx).symm.trans h, fun h => ⟨x0, hx0, h⟩⟩
    rw [if_congr this rfl rfl]
    simp
    split_ifs <;> simp

theorem bb_node {n m : ℕ} (f : (Fin n → ZMod 2) → Fin m) (Q : Finset (Fin m))
    (Z : Finset (Fin n → ZMod 2)) (h : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hc : ∀ a ∈ Q, (∃ x ∈ Z, f x = a) → ∀ y z, f y = a → f z = a → h y = h z)
    (N0 J0 N1 J1 : Finset (List Bool)) (q0 q1 : List Bool → (Fin n → ZMod 2) → Bool)
    (o0 o1 : List Bool → Fin m)
    (H0 : bb_Good f Q (Z.filter (fun x => h x ≠ 0)) N0 J0 q0 o0)
    (H1 : bb_Good f Q (Z.filter (fun x => h x = 0)) N1 J1 q1 o1) :
    ∃ N J q out, bb_Good f Q Z N J q out := by
  obtain ⟨s0, a0, k0, e0⟩ := H0
  obtain ⟨s1, a1, k1, e1⟩ := H1
  refine ⟨bb_nn N0 N1, bb_nn J0 J1, bb_nq (fun x => decide (h x = 0)) q0 q1, bb_nout o0 o1,
    bb_nn_shape _ _ _ _ s0 s1, ?_, ?_, ?_⟩
  · intro p hp
    rcases p with _ | ⟨c, r⟩
    · exact ⟨h, 0, rfl⟩
    · cases c
      · exact a0 r ((bb_nn_false _ _ _).1 hp)
      · exact a1 r ((bb_nn_true _ _ _).1 hp)
  · intro p hp x hz hcn
    rw [bb_nn_leaves] at hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hf, hc'⟩ := (bb_cons _ _ _ _).1 hcn
      exact k0 r hr x (Finset.mem_filter.2 ⟨hz, by simpa [bb_nq] using hf⟩) hc'
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hf, hc'⟩ := (bb_cons _ _ _ _).1 hcn
      exact k1 r hr x (Finset.mem_filter.2 ⟨hz, by simpa [bb_nq] using hf⟩) hc'
  · intro a ha
    rw [bb_count, e0 a ha, e1 a ha]
    have hdis : ¬ ((∃ x ∈ Z.filter (fun x => h x ≠ 0), f x = a) ∧ (∃ x ∈ Z.filter (fun x => h x = 0), f x = a)) := by
      rintro ⟨⟨x, hx, hfx⟩, ⟨y, hy, hfy⟩⟩
      rw [Finset.mem_filter] at hx hy
      exact hx.2 ((hc a ha ⟨x, hx.1, hfx⟩ x y hfx hfy).trans hy.2)
    have hor : (∃ x ∈ Z, f x = a) ↔ ((∃ x ∈ Z.filter (fun x => h x ≠ 0), f x = a) ∨ (∃ x ∈ Z.filter (fun x => h x = 0), f x = a)) := by
      constructor
      · rintro ⟨x, hx, hfx⟩
        by_cases hh : h x = 0
        · exact Or.inr ⟨x, Finset.mem_filter.2 ⟨hx, hh⟩, hfx⟩
        · exact Or.inl ⟨x, Finset.mem_filter.2 ⟨hx, hh⟩, hfx⟩
      · rintro (⟨x, hx, hfx⟩ | ⟨x, hx, hfx⟩) <;> exact ⟨x, (Finset.mem_filter.1 hx).1, hfx⟩
    rw [if_congr hor rfl rfl]
    by_cases p0 : ∃ x ∈ Z.filter (fun x => h x ≠ 0), f x = a <;>
      by_cases p1 : ∃ x ∈ Z.filter (fun x => h x = 0), f x = a
    · exact absurd ⟨p0, p1⟩ hdis
    all_goals simp only [p0, p1, ite_true, ite_false, or_true, or_false]

theorem bb_split {n m : ℕ} (f : (Fin n → ZMod 2) → Fin m) (Q : Finset (Fin m))
    (haff : ∀ a ∈ Q, ∃ (v : Fin n → ZMod 2) (A : Submodule (ZMod 2) (Fin n → ZMod 2)), ∀ x, x-v ∈ A ↔ f x = a)
    (hsep : ∀ S ⊆ Q, 1 < S.card → ∃ h : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      (∀ x y : Fin n → ZMod 2, f x ∈ S → f x = f y → h x = h y) ∧
      ∃ x y : Fin n → ZMod 2, f x ∈ S ∧ f y ∈ S ∧ h x ≠ h y)
    (Z : Finset (Fin n → ZMod 2)) (hinv : bb_Inv f Q Z) (x0 x1 : Fin n → ZMod 2)
    (h0 : x0 ∈ Z) (h1 : x1 ∈ Z) (hne : f x1 ≠ f x0) :
    ∃ h : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2, (∃ y ∈ Z, ∃ z ∈ Z, h y ≠ h z) ∧
      ∀ a ∈ Q, (∃ x ∈ Z, f x = a) → ∀ y z, f y = a → f z = a → h y = h z := by
  by_cases hS : 1 < (Q.filter (fun a => ∃ x ∈ Z, f x = a)).card
  · obtain ⟨h, hc, x, y, hx, hy, hxy⟩ := hsep _ (Finset.filter_subset _ _) hS
    rw [Finset.mem_filter] at hx hy
    refine ⟨h, ⟨x, hinv _ hx.1 hx.2 x rfl, y, hinv _ hy.1 hy.2 y rfl, hxy⟩, ?_⟩
    intro a ha hz y z hy hz'
    exact hc y z (by rw [Finset.mem_filter, hy]; exact ⟨ha, hz⟩) (hy.trans hz'.symm)
  · rw [not_lt, Finset.card_le_one] at hS
    by_cases hE : ∃ a ∈ Q, ∃ x ∈ Z, f x = a
    · obtain ⟨a, ha, y, hy, hfy⟩ := hE
      have uniq : ∀ b ∈ Q, (∃ x ∈ Z, f x = b) → b = a := fun b hb hbz =>
        hS b (Finset.mem_filter.2 ⟨hb, hbz⟩) a (Finset.mem_filter.2 ⟨ha, y, hy, hfy⟩)
      obtain ⟨w, hw, hfw⟩ : ∃ w ∈ Z, f w ≠ a := by
        by_cases e : f x0 = a
        · exact ⟨x1, h1, e ▸ hne⟩
        · exact ⟨x0, h0, e⟩
      obtain ⟨v, A, hA⟩ := haff a ha
      have hwA : w - v ∉ A := fun hh => hfw ((hA w).1 hh)
      obtain ⟨l, hl, hle⟩ := Submodule.exists_le_ker_of_notMem hwA
      have key : ∀ z, f z = a → l z = l v := by
        intro z hz
        have := hle ((hA z).2 hz)
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
        exact this
      refine ⟨l, ⟨y, hy, w, hw, ?_⟩, ?_⟩
      · rw [key y hfy]
        intro e
        apply hl
        rw [map_sub, e, sub_self]
      · intro b hb hbz y' z' hy' hz'
        have := uniq b hb hbz
        subst this
        rw [key y' hy', key z' hz']
    · have : x0 ≠ x1 := fun e => hne (e ▸ rfl)
      obtain ⟨i, hi⟩ := Function.ne_iff.1 this
      refine ⟨LinearMap.proj i, ⟨x0, h0, x1, h1, hi⟩, ?_⟩
      intro a ha hz
      exact absurd ⟨a, ha, hz⟩ hE

theorem bb_main {n m : ℕ} (f : (Fin n → ZMod 2) → Fin m) (Q : Finset (Fin m))
    (haff : ∀ a ∈ Q, ∃ (v : Fin n → ZMod 2) (A : Submodule (ZMod 2) (Fin n → ZMod 2)), ∀ x, x-v ∈ A ↔ f x = a)
    (hsep : ∀ S ⊆ Q, 1 < S.card → ∃ h : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      (∀ x y : Fin n → ZMod 2, f x ∈ S → f x = f y → h x = h y) ∧
      ∃ x y : Fin n → ZMod 2, f x ∈ S ∧ f y ∈ S ∧ h x ≠ h y) :
    ∀ (k : ℕ) (Z : Finset (Fin n → ZMod 2)), Z.card = k → Z.Nonempty → bb_Inv f Q Z →
      ∃ N J q out, bb_Good f Q Z N J q out := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro Z hk hZ hinv
  obtain ⟨x0, h0⟩ := hZ
  by_cases hall : ∀ x ∈ Z, f x = f x0
  · exact bb_leaf f Q Z x0 h0 hall
  push Not at hall
  obtain ⟨x1, h1, hne⟩ := hall
  obtain ⟨h, ⟨y, hy, z, hz, hyz⟩, hc⟩ := bb_split f Q haff hsep Z hinv x0 x1 h0 h1 hne
  have two : ∀ u v : ZMod 2, u ≠ v → (u = 0 ∧ v ≠ 0) ∨ (u ≠ 0 ∧ v = 0) := by decide
  obtain ⟨p0, hp0, hp0z, p1, hp1, hp1z⟩ : ∃ p0 ∈ Z, h p0 = 0 ∧ ∃ p1 ∈ Z, h p1 ≠ 0 := by
    rcases two _ _ hyz with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨y, hy, a, z, hz, b⟩
    · exact ⟨z, hz, b, y, hy, a⟩
  have inv0 : bb_Inv f Q (Z.filter (fun x => h x = 0)) := by
    intro a ha ⟨x, hx, hfx⟩ w hw
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hinv a ha ⟨x, hx.1, hfx⟩ w hw, (hc a ha ⟨x, hx.1, hfx⟩ w x hw hfx).trans hx.2⟩
  have inv1 : bb_Inv f Q (Z.filter (fun x => h x ≠ 0)) := by
    intro a ha ⟨x, hx, hfx⟩ w hw
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hinv a ha ⟨x, hx.1, hfx⟩ w hw, (hc a ha ⟨x, hx.1, hfx⟩ w x hw hfx).trans_ne hx.2⟩
  have c0 : (Z.filter (fun x => h x = 0)).card < k :=
    hk ▸ Finset.card_lt_card (Finset.filter_ssubset.2 ⟨p1, hp1, hp1z⟩)
  have c1 : (Z.filter (fun x => h x ≠ 0)).card < k :=
    hk ▸ Finset.card_lt_card (Finset.filter_ssubset.2 ⟨p0, hp0, fun e => e hp0z⟩)
  obtain ⟨N1, J1, q1, o1, G1⟩ := ih _ c0 _ rfl ⟨p0, Finset.mem_filter.2 ⟨hp0, hp0z⟩⟩ inv0
  obtain ⟨N0, J0, q0, o0, G0⟩ := ih _ c1 _ rfl ⟨p1, Finset.mem_filter.2 ⟨hp1, hp1z⟩⟩ inv1
  exact bb_node f Q Z h hc N0 J0 N1 J1 q0 q1 o0 o1 G0 G1

theorem bwd {n m : ℕ} (f : (Fin n → ZMod 2) → Fin m) (Q : Finset (Fin m))
    (hQ : Q ⊆ Finset.univ.image f)
    (haff : ∀ a ∈ Q, ∃ (v : Fin n → ZMod 2) (A : Submodule (ZMod 2) (Fin n → ZMod 2)), ∀ x, x-v ∈ A ↔ f x = a)
    (hsep : ∀ S ⊆ Q, 1 < S.card → ∃ h : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      (∀ x y : Fin n → ZMod 2, f x ∈ S → f x = f y → h x = h y) ∧
      ∃ x y : Fin n → ZMod 2, f x ∈ S ∧ f y ∈ S ∧ h x ≠ h y) :
    ∃ (N J : Finset (List Bool)) (q : List Bool → (Fin n → ZMod 2) → Bool) (out : List Bool → Fin m),
      Tree f N J q out ∧ ∀ a ∈ Q, ((N \ J).filter (fun p => out p = a)).card = 1 := by
  obtain ⟨N, J, q, out, s, a, k, e⟩ := bb_main f Q haff hsep _ Finset.univ rfl
    ⟨0, Finset.mem_univ _⟩ (fun _ _ _ y _ => Finset.mem_univ y)
  refine ⟨N, J, q, out, ⟨s, a, fun p hp x hc => k p hp x (Finset.mem_univ x) hc⟩, ?_⟩
  intro b hb
  rw [e b hb]
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (hQ hb)
  split_ifs with H
  · rfl
  · exact absurd ⟨x, Finset.mem_univ x, hx⟩ H

end PEqualNP.Outside.L_lib_881_aux

theorem PEqualNP.Outside.L_lib_881 : (∀ (n m : ℕ),
  let X := Fin n → ZMod 2
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  ∀ (f : X → Fin m) (Q : Finset (Fin m)) (_ : Q ⊆ Finset.univ.image f),
    (∃ (N J : Finset (List Bool)) (q : List Bool → X → Bool) (out : List Bool → Fin m),
      cert (queries X) (fun x a => f x = a) N J q out ∧
      ∀ a ∈ Q, ((N \ J).filter (fun p => out p = a)).card = 1) ↔
    (∀ a ∈ Q, ∃ (v : X) (A : Submodule (ZMod 2) X), ∀ x, x-v ∈ A ↔ f x = a) ∧
    ∀ S ⊆ Q, 1 < S.card → ∃ h : X →ₗ[ZMod 2] ZMod 2,
      (∀ x y : X, f x ∈ S → f x = f y → h x = h y) ∧
      ∃ x y : X, f x ∈ S ∧ f y ∈ S ∧ h x ≠ h y) := by
  intro n m
  dsimp only
  intro f Q hQ
  constructor
  · rintro ⟨N, J, q, out, ⟨hS, hq, hok⟩, hc⟩
    exact PEqualNP.Outside.L_lib_881_aux.fwd f Q hQ N J q out ⟨hS, hq, hok⟩ hc
  · rintro ⟨haff, hsep⟩
    obtain ⟨N, J, q, out, ⟨hS, hq, hok⟩, hc⟩ := PEqualNP.Outside.L_lib_881_aux.bwd f Q hQ haff hsep
    exact ⟨N, J, q, out, ⟨hS, hq, hok⟩, hc⟩
