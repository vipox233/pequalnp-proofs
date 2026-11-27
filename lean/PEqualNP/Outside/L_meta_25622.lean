import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25622_aux

private def idx (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k :=
  ⟨n % k, Nat.mod_lt _ hk⟩

private def addW {k : ℕ} (x y : Fin k → Bool) (i : Fin k) : Bool :=
  xor (x i) (y i)

private def rotW {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k → Bool) (i : Fin k) : Bool :=
  x (idx k hk (i.val + k - s % k))

private def mixW {k : ℕ} (hk : 0 < k) (d : ℕ) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (xor (x i) (x (idx k hk (i.val + d)))) (x (idx k hk (i.val + k - d)))

private def stepW {k : ℕ} (hk : 0 < k) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (x i) (!(x (idx k hk (i.val + 1))) && x (idx k hk (i.val + 2)))

private def plusB {q : ℕ} (u v : Fin q → Fin 4 → Bool) (b : Fin q) (l : Fin 4) : Bool :=
  xor (u b l) (v b l)

private def diffB {q : ℕ} (f : (Fin q → Fin 4 → Bool) → Bool)
    (v x : Fin q → Fin 4 → Bool) : Bool :=
  xor (f x) (f (plusB x v))

private def IsPoly {q : ℕ} : ℕ → ((Fin q → Fin 4 → Bool) → Bool) → Prop
  | 0, f => ∃ c : Bool, ∀ x, f x = c
  | d + 1, f => ∀ v, IsPoly d (diffB f v)

private instance : LeftCommutative xor :=
  ⟨fun a b c => by cases a <;> cases b <;> cases c <;> rfl⟩

private instance : Std.Commutative xor :=
  ⟨fun a b => by cases a <;> cases b <;> rfl⟩

private instance : Std.Associative xor :=
  ⟨fun a b c => by cases a <;> cases b <;> cases c <;> rfl⟩

private theorem isPoly_const {q : ℕ} (c : Bool) : IsPoly (q := q) 0 (fun _ => c) :=
  ⟨c, fun _ => rfl⟩

private theorem isPoly_false {q : ℕ} : ∀ d : ℕ, IsPoly (q := q) d (fun _ => false)
  | 0 => ⟨false, fun _ => rfl⟩
  | d + 1 => fun v => by
    have : diffB (fun _ => false) v = fun _ => false := by funext x; simp [diffB]
    rw [this]
    exact isPoly_false d

private theorem isPoly_mono {q : ℕ} :
    ∀ {d₁ d₂ : ℕ} {f : (Fin q → Fin 4 → Bool) → Bool}, d₁ ≤ d₂ → IsPoly d₁ f → IsPoly d₂ f := by
  intro d₁
  induction d₁ with
  | zero =>
    intro d₂ f _ hf
    obtain ⟨c, hc⟩ := hf
    cases d₂ with
    | zero => exact ⟨c, hc⟩
    | succ d₂ =>
      intro v
      have h0 : diffB f v = fun _ => false := by
        funext x
        simp [diffB, hc]
      rw [h0]
      exact isPoly_false d₂
  | succ d₁ ih =>
    intro d₂ f hle hf
    cases d₂ with
    | zero => omega
    | succ d₂ =>
      intro v
      exact ih (Nat.le_of_succ_le_succ hle) (hf v)

private theorem diffB_xor {q : ℕ} (f g : (Fin q → Fin 4 → Bool) → Bool) (v : Fin q → Fin 4 → Bool) :
    diffB (fun x => xor (f x) (g x)) v = fun x => xor (diffB f v x) (diffB g v x) := by
  funext x
  simp only [diffB]
  cases f x <;> cases g x <;> cases f (plusB x v) <;> cases g (plusB x v) <;> rfl

private theorem isPoly_xor {q : ℕ} :
    ∀ {d : ℕ} {f g : (Fin q → Fin 4 → Bool) → Bool},
      IsPoly d f → IsPoly d g → IsPoly d (fun x => xor (f x) (g x)) := by
  intro d
  induction d with
  | zero =>
    intro f g ⟨cf, hcf⟩ ⟨cg, hcg⟩
    exact ⟨xor cf cg, fun x => by dsimp only; rw [hcf, hcg]⟩
  | succ d ih =>
    intro f g hf hg v
    rw [diffB_xor]
    exact ih (hf v) (hg v)

private theorem isPoly_not {q : ℕ} {d : ℕ} {f : (Fin q → Fin 4 → Bool) → Bool} (hf : IsPoly d f) :
    IsPoly d (fun x => !(f x)) := by
  have h1 : (fun x => !(f x)) = (fun x => xor (f x) true) := by
    funext x; cases f x <;> rfl
  rw [h1]
  exact isPoly_xor hf (isPoly_mono (Nat.zero_le d) (isPoly_const true))

private theorem isPoly_const_and {q : ℕ} {d : ℕ} (c : Bool) {f : (Fin q → Fin 4 → Bool) → Bool}
    (hf : IsPoly d f) : IsPoly d (fun x => c && f x) := by
  cases c
  · simpa using isPoly_mono (Nat.zero_le d) (isPoly_const (q := q) false)
  · simpa using hf

private theorem isPoly_linear {q : ℕ} (L : (Fin q → Fin 4 → Bool) → Bool)
    (hL : ∀ x y, L (plusB x y) = xor (L x) (L y)) :
    IsPoly 1 L := by
  intro v
  refine ⟨L v, fun x => ?_⟩
  simp only [diffB, hL]
  cases L x <;> cases L v <;> rfl

private theorem isPoly_affine {q : ℕ} (c : Bool) (L : (Fin q → Fin 4 → Bool) → Bool)
    (hL : ∀ x y, L (plusB x y) = xor (L x) (L y)) :
    IsPoly 1 (fun x => xor c (L x)) :=
  isPoly_xor (isPoly_mono (by omega) (isPoly_const c)) (isPoly_linear L hL)

private theorem diffB_and {q : ℕ} (f g : (Fin q → Fin 4 → Bool) → Bool) (v : Fin q → Fin 4 → Bool) :
    diffB (fun x => f x && g x) v =
      fun x => xor (xor (f x && diffB g v x) (diffB f v x && g x)) (diffB f v x && diffB g v x) := by
  funext x
  simp only [diffB]
  cases f x <;> cases g x <;> cases f (plusB x v) <;> cases g (plusB x v) <;> rfl

private theorem isPoly_and {q : ℕ} :
    ∀ {s d₁ d₂ : ℕ} {f g : (Fin q → Fin 4 → Bool) → Bool},
      d₁ + d₂ = s → IsPoly d₁ f → IsPoly d₂ g → IsPoly s (fun x => f x && g x) := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro d₁ d₂ f g hs hf hg
    cases d₁ with
    | zero =>
      obtain ⟨cf, hcf⟩ := hf
      have heq : (fun x => f x && g x) = (fun x => cf && g x) := by
        funext x; rw [hcf]
      rw [heq]
      have hd2 : d₂ = s := by omega
      subst hd2
      exact isPoly_const_and cf hg
    | succ d₁ =>
      cases d₂ with
      | zero =>
        obtain ⟨cg, hcg⟩ := hg
        have heq : (fun x => f x && g x) = (fun x => cg && f x) := by
          funext x; rw [hcg, Bool.and_comm]
        rw [heq]
        have hd1 : d₁ + 1 = s := by omega
        rw [← hd1]
        exact isPoly_const_and cg hf
      | succ d₂ =>
        cases s with
        | zero => omega
        | succ s' =>
          intro v
          rw [diffB_and]
          have hA : IsPoly s' (fun x => f x && diffB g v x) :=
            ih s' (by omega) (d₁ := d₁ + 1) (d₂ := d₂) (by omega) hf (hg v)
          have hB : IsPoly s' (fun x => diffB f v x && g x) :=
            ih s' (by omega) (d₁ := d₁) (d₂ := d₂ + 1) (by omega) (hf v) hg
          have hC : IsPoly s' (fun x => diffB f v x && diffB g v x) :=
            isPoly_mono (by omega : d₁ + d₂ ≤ s')
              (ih (d₁ + d₂) (by omega) (d₁ := d₁) (d₂ := d₂) rfl (hf v) (hg v))
          exact isPoly_xor (isPoly_xor hA hB) hC

private theorem isPoly_foldl_xor {q : ℕ} {α : Type*} (l : List α)
    (F : α → (Fin q → Fin 4 → Bool) → Bool) (d : ℕ)
    (hF : ∀ a ∈ l, IsPoly d (F a)) :
    IsPoly d (fun x => (l.map (fun a => F a x)).foldl xor false) := by
  have hgen : ∀ (init : (Fin q → Fin 4 → Bool) → Bool), IsPoly d init →
      IsPoly d (fun x => l.foldl (fun acc a => xor acc (F a x)) (init x)) := by
    induction l with
    | nil => intro init hinit; simpa using hinit
    | cons a l ih =>
      intro init hinit
      simp only [List.foldl_cons]
      exact ih (fun a' ha' => hF a' (by simp [ha']))
        (fun x => xor (init x) (F a x))
        (isPoly_xor hinit (hF a (by simp)))
  have heq : (fun x => (l.map (fun a => F a x)).foldl xor false) =
      (fun x => l.foldl (fun acc a => xor acc (F a x)) false) := by
    funext x
    rw [List.foldl_map]
  rw [heq]
  exact hgen (fun _ => false) (isPoly_mono (Nat.zero_le d) (isPoly_const false))

private theorem vanishes4_of_isPoly3 {q : ℕ} {f : (Fin q → Fin 4 → Bool) → Bool}
    (hf : IsPoly 3 f) (v : Fin 4 → Fin q → Fin 4 → Bool) (x : Fin q → Fin 4 → Bool) :
    (List.ofFn v).foldl diffB f x = false := by
  have hlist : List.ofFn v = [v 0, v 1, v 2, v 3] := by
    simp [List.ofFn_succ]
  rw [hlist]
  simp only [List.foldl_cons, List.foldl_nil]
  obtain ⟨c, hc⟩ := hf (v 0) (v 1) (v 2)
  change xor (diffB (diffB (diffB f (v 0)) (v 1)) (v 2) x)
    (diffB (diffB (diffB f (v 0)) (v 1)) (v 2) (plusB x (v 3))) = false
  rw [hc, hc]
  cases c <;> rfl

private theorem foldl_xor_comm_init_list (l : List Bool) (b : Bool) :
    l.foldl xor b = xor b (l.foldl xor false) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (xor b a), ih a]
    cases b <;> cases a <;> cases l.foldl xor false <;> rfl

private theorem foldl_xor_map_eq_finset {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).foldl xor false =
      ((Finset.univ : Finset (Fin n)).val.map f).foldr xor false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons, Bool.false_xor, foldl_xor_comm_init_list, ih]
    have huniv : (Finset.univ : Finset (Fin (n + 1))) =
        insert 0 ((Finset.univ : Finset (Fin n)).image Fin.succ) := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_image, true_iff]
      exact Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j, trivial, rfl⟩) i
    have hnot : (0 : Fin (n + 1)) ∉ (Finset.univ : Finset (Fin n)).image Fin.succ := by
      simp
    rw [huniv, Finset.insert_val_of_notMem hnot, Multiset.map_cons, Multiset.foldr_cons]
    congr 1
    have hinj : Function.Injective (Fin.succ : Fin n → Fin (n + 1)) := Fin.succ_injective n
    rw [Finset.image_val_of_injOn (fun a _ b _ h => hinj h), Multiset.map_map]
    rfl

private theorem xor_foldl_ofFn_eq_of_inj {n m : ℕ} (g : Fin n → Bool) (h : Fin m → Bool)
    (e : Fin m → Fin n) (he : Function.Injective e)
    (hmatch : ∀ j : Fin n,
      (∀ b : Fin m, e b ≠ j) → g j = false)
    (hmatch2 : ∀ b : Fin m, g (e b) = h b) :
    xor ((List.ofFn g).foldl xor false) ((List.ofFn h).foldl xor false) = false := by
  have h1 : (List.ofFn g).foldl xor false = (List.ofFn h).foldl xor false := by
    rw [foldl_xor_map_eq_finset, foldl_xor_map_eq_finset]
    have hsplit : (Finset.univ : Finset (Fin n)) =
        ((Finset.univ : Finset (Fin m)).image e).disjUnion
        ((Finset.univ : Finset (Fin n)) \ ((Finset.univ : Finset (Fin m)).image e))
        Finset.disjoint_sdiff := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_disjUnion, Finset.mem_sdiff, true_iff]
      tauto
    have hval : (Finset.univ : Finset (Fin n)).val =
        ((Finset.univ : Finset (Fin m)).image e).val +
        ((Finset.univ : Finset (Fin n)) \ ((Finset.univ : Finset (Fin m)).image e)).val :=
      congrArg Finset.val hsplit
    rw [hval, Multiset.map_add, Multiset.foldr_add]
    have hrest : (((Finset.univ : Finset (Fin n)) \
        ((Finset.univ : Finset (Fin m)).image e)).val.map g).foldr xor false = false := by
      have hall : ∀ b ∈ (((Finset.univ : Finset (Fin n)) \
          ((Finset.univ : Finset (Fin m)).image e)).val.map g), b = false := by
        intro b hb
        obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hb
        have hnot : j ∉ (Finset.univ : Finset (Fin m)).image e := (Finset.mem_sdiff.1 (Finset.mem_def.2 hj)).2
        apply hmatch j
        intro c hc
        exact hnot (Finset.mem_image.2 ⟨c, Finset.mem_univ c, hc⟩)
      generalize (((Finset.univ : Finset (Fin n)) \
        ((Finset.univ : Finset (Fin m)).image e)).val.map g) = M at hall ⊢
      induction M using Multiset.induction_on with
      | empty => rfl
      | cons a s ih =>
        rw [Multiset.foldr_cons, hall a (Multiset.mem_cons_self _ _),
          ih (fun b hb => hall b (Multiset.mem_cons_of_mem hb))]
        rfl
    rw [hrest]
    rw [Finset.image_val_of_injOn (fun a _ b _ h => he h), Multiset.map_map]
    have hcomp : g ∘ e = h := funext hmatch2
    rw [hcomp]
  rw [h1]
  cases (List.ofFn h).foldl xor false <;> rfl

private theorem xor_foldl_ofFn_add {n : ℕ} (f g : Fin n → Bool) :
    xor ((List.ofFn f).foldl xor false) ((List.ofFn g).foldl xor false) =
      (List.ofFn (fun i => xor (f i) (g i))).foldl xor false := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
      List.foldl_cons, List.foldl_cons, List.foldl_cons,
      Bool.false_xor, Bool.false_xor, Bool.false_xor]
    rw [foldl_xor_comm_init_list (List.ofFn (fun i : Fin n => f i.succ)) (f 0),
      foldl_xor_comm_init_list (List.ofFn (fun i : Fin n => g i.succ)) (g 0),
      foldl_xor_comm_init_list (List.ofFn (fun i : Fin n => xor (f i.succ) (g i.succ))) (xor (f 0) (g 0)),
      ← ih (fun i => f i.succ) (fun i => g i.succ)]
    cases f 0 <;> cases g 0 <;>
      cases (List.ofFn (fun i : Fin n => f i.succ)).foldl xor false <;>
      cases (List.ofFn (fun i : Fin n => g i.succ)).foldl xor false <;> rfl

private def seq1D (L : ℕ) (hL : 0 < L) (a b : Bool) (y : Fin L → Bool) : ℕ → Bool
  | 0 => a
  | 1 => b
  | m + 2 => xor (xor (seq1D L hL a b y m) (seq1D L hL a b y (m + 1))) (y ⟨(m + 1) % L, Nat.mod_lt _ hL⟩)

private def segXor (L : ℕ) (hL : 0 < L) (y : Fin L → Bool) (r : ℕ) : ℕ → Bool
  | 0 => false
  | q + 1 => xor (segXor L hL y r q) (y ⟨(3 * q + r) % L, Nat.mod_lt _ hL⟩)

private theorem seq1D_mod3 (L : ℕ) (hL : 0 < L) (a b : Bool) (y : Fin L → Bool) (q : ℕ) :
    seq1D L hL a b y (3 * q) = xor a (xor (segXor L hL y 1 q) (segXor L hL y 2 q)) ∧
    seq1D L hL a b y (3 * q + 1) = xor b (xor (segXor L hL y 2 q) (segXor L hL y 3 q)) ∧
    seq1D L hL a b y (3 * q + 2) =
      xor (xor a b) (xor (y ⟨(3 * q + 1) % L, Nat.mod_lt _ hL⟩)
        (xor (segXor L hL y 1 q) (segXor L hL y 3 q))) := by
  induction q with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [segXor, seq1D, Bool.xor_false]
    · simp only [segXor, seq1D, Bool.xor_false]
    · simp only [Nat.mul_zero, Nat.zero_add, segXor, seq1D, Bool.xor_false]
  | succ q ih =>
    rcases ih with ⟨h0, h1, h2⟩
    have s0 : seq1D L hL a b y (3 * (q + 1)) =
        xor (xor (seq1D L hL a b y (3 * q + 1)) (seq1D L hL a b y (3 * q + 2)))
          (y ⟨(3 * q + 2) % L, Nat.mod_lt _ hL⟩) := rfl
    have s1 : seq1D L hL a b y (3 * (q + 1) + 1) =
        xor (xor (seq1D L hL a b y (3 * q + 2)) (seq1D L hL a b y (3 * (q + 1))))
          (y ⟨(3 * q + 3) % L, Nat.mod_lt _ hL⟩) := rfl
    have s2 : seq1D L hL a b y (3 * (q + 1) + 2) =
        xor (xor (seq1D L hL a b y (3 * (q + 1))) (seq1D L hL a b y (3 * (q + 1) + 1)))
          (y ⟨(3 * (q + 1) + 1) % L, Nat.mod_lt _ hL⟩) := rfl
    have e0 : seq1D L hL a b y (3 * (q + 1)) =
        xor a (xor (segXor L hL y 1 (q + 1)) (segXor L hL y 2 (q + 1))) := by
      rw [s0, h1, h2]
      simp only [segXor]
      cases a <;> cases b <;>
        cases segXor L hL y 1 q <;> cases segXor L hL y 2 q <;> cases segXor L hL y 3 q <;>
        cases y ⟨(3 * q + 1) % L, Nat.mod_lt _ hL⟩ <;> cases y ⟨(3 * q + 2) % L, Nat.mod_lt _ hL⟩ <;> rfl
    have e1 : seq1D L hL a b y (3 * (q + 1) + 1) =
        xor b (xor (segXor L hL y 2 (q + 1)) (segXor L hL y 3 (q + 1))) := by
      rw [s1, h2, e0]
      simp only [segXor]
      cases a <;> cases b <;>
        cases segXor L hL y 1 q <;> cases segXor L hL y 2 q <;> cases segXor L hL y 3 q <;>
        cases y ⟨(3 * q + 1) % L, Nat.mod_lt _ hL⟩ <;> cases y ⟨(3 * q + 2) % L, Nat.mod_lt _ hL⟩ <;>
        cases y ⟨(3 * q + 3) % L, Nat.mod_lt _ hL⟩ <;> rfl
    have e2 : seq1D L hL a b y (3 * (q + 1) + 2) =
        xor (xor a b) (xor (y ⟨(3 * (q + 1) + 1) % L, Nat.mod_lt _ hL⟩)
          (xor (segXor L hL y 1 (q + 1)) (segXor L hL y 3 (q + 1)))) := by
      rw [s2, e0, e1]
      cases a <;> cases b <;>
        cases segXor L hL y 1 (q + 1) <;> cases segXor L hL y 2 (q + 1) <;>
        cases segXor L hL y 3 (q + 1) <;>
        cases y ⟨(3 * (q + 1) + 1) % L, Nat.mod_lt _ hL⟩ <;> rfl
    exact ⟨e0, e1, e2⟩

private theorem segXor_shift3 (L : ℕ) (hL : 0 < L) (y : Fin L → Bool) (q : ℕ) (hLq : 3 * q = L) :
    segXor L hL y 3 q = segXor L hL y 0 q := by
  have h1 : ∀ m : ℕ, xor (y ⟨0, hL⟩) (segXor L hL y 3 m) =
      xor (segXor L hL y 0 m) (y ⟨(3 * m) % L, Nat.mod_lt _ hL⟩) := by
    intro m
    induction m with
    | zero =>
      simp only [segXor, Nat.mul_zero, Nat.zero_mod, Bool.xor_false, Bool.false_xor]
    | succ m ih =>
      simp only [segXor]
      have hf1 : (⟨(3 * m + 3) % L, Nat.mod_lt _ hL⟩ : Fin L) =
          ⟨(3 * (m + 1)) % L, Nat.mod_lt _ hL⟩ := Fin.ext (by dsimp only; ring_nf)
      have hf0 : (⟨(3 * m + 0) % L, Nat.mod_lt _ hL⟩ : Fin L) =
          ⟨(3 * m) % L, Nat.mod_lt _ hL⟩ := Fin.ext (by dsimp only; ring_nf)
      rw [hf1, hf0]
      generalize y ⟨0, hL⟩ = a at ih ⊢
      generalize segXor L hL y 3 m = b at ih ⊢
      generalize segXor L hL y 0 m = c at ih ⊢
      generalize y ⟨(3 * m) % L, Nat.mod_lt _ hL⟩ = d at ih ⊢
      generalize y ⟨(3 * (m + 1)) % L, Nat.mod_lt _ hL⟩ = e
      cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> revert ih <;> decide
  have hq := h1 q
  have hfq : (⟨(3 * q) % L, Nat.mod_lt _ hL⟩ : Fin L) = ⟨0, hL⟩ :=
    Fin.ext (by dsimp only; rw [hLq, Nat.mod_self])
  rw [hfq] at hq
  generalize y ⟨0, hL⟩ = a at hq ⊢
  generalize segXor L hL y 3 q = b at hq ⊢
  generalize segXor L hL y 0 q = c at hq ⊢
  cases a <;> cases b <;> cases c <;> revert hq <;> decide

private theorem solve_1D (L : ℕ) (hL : 3 ≤ L) (y : Fin L → Bool)
    (hcond : L % 3 = 0 →
      segXor L (by omega) y 0 (L / 3) = segXor L (by omega) y 1 (L / 3) ∧
      segXor L (by omega) y 1 (L / 3) = segXor L (by omega) y 2 (L / 3)) :
    ∃ x : Fin L → Bool, ∀ i : Fin L,
      xor (xor (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ (by omega)⟩))
        (x ⟨(i.val + L - 1) % L, Nat.mod_lt _ (by omega)⟩) = y i := by
  have hLpos : 0 < L := by omega
  have hfrom : ∀ a b : Bool,
      seq1D L hLpos a b y L = a → seq1D L hLpos a b y (L + 1) = b →
      ∃ x : Fin L → Bool, ∀ i : Fin L,
        xor (xor (x i) (x ⟨(i.val + 1) % L, Nat.mod_lt _ hLpos⟩))
          (x ⟨(i.val + L - 1) % L, Nat.mod_lt _ hLpos⟩) = y i := by
    intro a b hper0 hper1
    refine ⟨fun i => seq1D L hLpos a b y i.val, ?_⟩
    intro i
    by_cases hi0 : i.val = 0
    · have hi : i = ⟨0, hLpos⟩ := Fin.ext hi0
      subst hi
      have hrec : seq1D L hLpos a b y (L + 1) =
          xor (xor (seq1D L hLpos a b y (L - 1)) (seq1D L hLpos a b y L))
            (y ⟨0, hLpos⟩) := by
        have hL2 : L + 1 = (L - 1) + 2 := by omega
        have hL1 : (L - 1) + 1 = L := by omega
        have h0 := congrArg (seq1D L hLpos a b y) hL2
        simp only [seq1D, hL1] at h0
        have hf0 : (⟨L % L, Nat.mod_lt _ hLpos⟩ : Fin L) = ⟨0, hLpos⟩ := Fin.ext (Nat.mod_self L)
        rw [hf0] at h0
        exact h0
      rw [hper0, hper1] at hrec
      have hm1 : (0 + 1) % L = 1 := Nat.mod_eq_of_lt (by omega)
      have hm2 : (0 + L - 1) % L = L - 1 := by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
      simp only [hm1, hm2, seq1D]
      generalize seq1D L hLpos a b y (L - 1) = u at hrec ⊢
      generalize y ⟨0, hLpos⟩ = y0 at hrec ⊢
      cases a <;> cases b <;> cases u <;> cases y0 <;> revert hrec <;> decide
    · by_cases hiL : i.val = L - 1
      · have hrec : seq1D L hLpos a b y L =
            xor (xor (seq1D L hLpos a b y (L - 2)) (seq1D L hLpos a b y (L - 1)))
              (y i) := by
          have hL2 : L = (L - 2) + 2 := by omega
          have hL1 : (L - 2) + 1 = L - 1 := by omega
          have h0 := congrArg (seq1D L hLpos a b y) hL2
          simp only [seq1D, hL1] at h0
          have hfi : (⟨(L - 1) % L, Nat.mod_lt _ hLpos⟩ : Fin L) = i :=
            Fin.ext (by dsimp only; rw [hiL]; exact Nat.mod_eq_of_lt (by omega))
          rw [hfi] at h0
          exact h0
        rw [hper0] at hrec
        have hm1 : (i.val + 1) % L = 0 := by rw [hiL, show L - 1 + 1 = L by omega, Nat.mod_self]
        have hm2 : (i.val + L - 1) % L = L - 2 := by
          rw [hiL, show L - 1 + L - 1 = L + (L - 2) by omega, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt (by omega)
        dsimp only
        rw [hm1, hm2, hiL]
        simp only [seq1D]
        generalize seq1D L hLpos a b y (L - 2) = u2 at hrec ⊢
        generalize seq1D L hLpos a b y (L - 1) = u1 at hrec ⊢
        generalize y i = yi at hrec ⊢
        cases a <;> cases u2 <;> cases u1 <;> cases yi <;> revert hrec <;> decide
      · have hilt : i.val + 1 < L := by omega
        have hm1 : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt hilt
        have hm2 : (i.val + L - 1) % L = i.val - 1 := by
          rw [show i.val + L - 1 = L + (i.val - 1) by omega, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt (by omega)
        have hrec : seq1D L hLpos a b y (i.val + 1) =
            xor (xor (seq1D L hLpos a b y (i.val - 1)) (seq1D L hLpos a b y i.val))
              (y i) := by
          have h2 : i.val + 1 = (i.val - 1) + 2 := by omega
          have h1 : (i.val - 1) + 1 = i.val := by omega
          have h0 := congrArg (seq1D L hLpos a b y) h2
          simp only [seq1D, h1] at h0
          have hfi : (⟨i.val % L, Nat.mod_lt _ hLpos⟩ : Fin L) = i :=
            Fin.ext (Nat.mod_eq_of_lt i.isLt)
          rw [hfi] at h0
          exact h0
        simp only [hm1, hm2]
        generalize seq1D L hLpos a b y (i.val - 1) = u0 at hrec ⊢
        generalize seq1D L hLpos a b y i.val = u1 at hrec ⊢
        generalize seq1D L hLpos a b y (i.val + 1) = u2 at hrec ⊢
        generalize y i = yi at hrec ⊢
        cases u0 <;> cases u1 <;> cases u2 <;> cases yi <;> revert hrec <;> decide
  set q := L / 3
  have hmod : L % 3 = 0 ∨ L % 3 = 1 ∨ L % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · have hLq : 3 * q = L := by omega
    obtain ⟨hc01, hc12⟩ := hcond h0
    have hshift := segXor_shift3 L hLpos y q hLq
    have h3 := seq1D_mod3 L hLpos false false y q
    apply hfrom false false
    · rw [congrArg (seq1D L hLpos false false y) hLq.symm, h3.1, hc12]
      cases segXor L hLpos y 2 q <;> rfl
    · rw [congrArg (seq1D L hLpos false false y) (show L + 1 = 3 * q + 1 by omega), h3.2.1, hshift, hc01, hc12]
      cases segXor L hLpos y 2 q <;> rfl
  · have hLq : 3 * q + 1 = L := by omega
    set C1 := xor (segXor L hLpos y 2 q) (segXor L hLpos y 3 q)
    set C2 := xor (y ⟨(3 * q + 1) % L, Nat.mod_lt _ hLpos⟩)
      (xor (segXor L hLpos y 1 q) (segXor L hLpos y 3 q))
    have h3 := seq1D_mod3 L hLpos C2 (xor C1 C2) y q
    apply hfrom C2 (xor C1 C2)
    · rw [congrArg (seq1D L hLpos C2 (xor C1 C2) y) hLq.symm, h3.2.1]
      change xor (xor C1 C2) C1 = C2
      cases C1 <;> cases C2 <;> rfl
    · rw [congrArg (seq1D L hLpos C2 (xor C1 C2) y) (show L + 1 = 3 * q + 2 by omega), h3.2.2]
      change xor (xor C2 (xor C1 C2)) C2 = xor C1 C2
      cases C1 <;> cases C2 <;> rfl
  · have hLq : 3 * q + 2 = L := by omega
    set C2 := xor (y ⟨(3 * q + 1) % L, Nat.mod_lt _ hLpos⟩)
      (xor (segXor L hLpos y 1 q) (segXor L hLpos y 3 q))
    set C0 := xor (segXor L hLpos y 1 (q + 1)) (segXor L hLpos y 2 (q + 1))
    have h3 := seq1D_mod3 L hLpos (xor C0 C2) C2 y q
    have h3' := seq1D_mod3 L hLpos (xor C0 C2) C2 y (q + 1)
    apply hfrom (xor C0 C2) C2
    · rw [congrArg (seq1D L hLpos (xor C0 C2) C2 y) hLq.symm, h3.2.2]
      change xor (xor (xor C0 C2) C2) C2 = xor C0 C2
      cases C0 <;> cases C2 <;> rfl
    · rw [congrArg (seq1D L hLpos (xor C0 C2) C2 y) (show L + 1 = 3 * (q + 1) by omega), h3'.1]
      change xor (xor C0 C2) C0 = C2
      cases C0 <;> cases C2 <;> rfl

private theorem segXor_eq_xor_fin {L : ℕ} (hL : 0 < L) (y : Fin L → Bool) (r q : ℕ)
    (hLq : 3 * q = L) (hr : r < 3) :
    segXor L hL y r q =
      ((Finset.univ.filter (fun m : Fin L => m.val % 3 = r)).val.map y).foldr xor false := by
  have hcomm : Std.Commutative xor := ⟨fun a b => by cases a <;> cases b <;> rfl⟩
  have hassoc : Std.Associative xor := ⟨fun a b c => by cases a <;> cases b <;> cases c <;> rfl⟩
  have hgen : ∀ t ≤ q, segXor L hL y r t =
      ((Finset.univ.filter (fun m : Fin L => m.val < 3 * t ∧ m.val % 3 = r)).val.map y).foldr xor false := by
    intro t
    induction t with
    | zero =>
      intro _
      have hempty : Finset.univ.filter (fun m : Fin L => m.val < 3 * 0 ∧ m.val % 3 = r) = ∅ := by
        ext m; simp
      rw [hempty]; rfl
    | succ t ih =>
      intro ht
      simp only [segXor]
      rw [ih (by omega)]
      set p : Fin L := ⟨3 * t + r, by omega⟩
      have hS : Finset.univ.filter (fun m : Fin L => m.val < 3 * (t + 1) ∧ m.val % 3 = r) =
          insert p (Finset.univ.filter (fun m : Fin L => m.val < 3 * t ∧ m.val % 3 = r)) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, p]
        omega
      have hnot : p ∉ Finset.univ.filter (fun m : Fin L => m.val < 3 * t ∧ m.val % 3 = r) := by
        simp [p]
      rw [hS, Finset.insert_val_of_notMem hnot, Multiset.map_cons, Multiset.foldr_cons]
      have hmod : (3 * t + r) % L = 3 * t + r := Nat.mod_eq_of_lt (by omega)
      have hpeq : (⟨(3 * t + r) % L, Nat.mod_lt _ hL⟩ : Fin L) = p := Fin.ext hmod
      rw [hpeq]
      cases y p <;> cases ((Finset.univ.filter (fun m : Fin L => m.val < 3 * t ∧ m.val % 3 = r)).val.map y).foldr xor false <;> rfl
  rw [hgen q le_rfl]
  have hset : Finset.univ.filter (fun m : Fin L => m.val < 3 * q ∧ m.val % 3 = r) =
      Finset.univ.filter (fun m : Fin L => m.val % 3 = r) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := m.isLt
    omega
  rw [hset]

private theorem segXor_of_two_eq {L : ℕ} (hL : 0 < L) (hL3 : L % 3 = 0)
    (a b : Fin L) (hab : a ≠ b) (hmod : a.val % 3 = b.val % 3) (r : ℕ) (hr : r < 3) :
    segXor L hL (fun m => decide (m = a) || decide (m = b)) r (L / 3) = false := by
  rw [segXor_eq_xor_fin hL _ r (L / 3) (by omega) hr]
  have hcomm : Std.Commutative xor := ⟨fun x y => by cases x <;> cases y <;> rfl⟩
  have hassoc : Std.Associative xor := ⟨fun x y z => by cases x <;> cases y <;> cases z <;> rfl⟩
  set S := Finset.univ.filter (fun m : Fin L => m.val % 3 = r)
  by_cases har : a.val % 3 = r
  · have haS : a ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, har⟩
    have hbS : b ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hmod.symm.trans har⟩
    have hsplit : S = insert a (insert b ((S.erase a).erase b)) := by
      ext m
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · intro hm
        by_cases h1 : m = a
        · exact Or.inl h1
        · by_cases h2 : m = b
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr ⟨h2, h1, hm⟩)
      · rintro (rfl | rfl | ⟨_, _, hm⟩) <;> assumption
    have hna : a ∉ insert b ((S.erase a).erase b) := by simp [hab]
    have hnb : b ∉ (S.erase a).erase b := by simp
    rw [hsplit, Finset.insert_val_of_notMem hna, Finset.insert_val_of_notMem hnb,
      Multiset.map_cons, Multiset.map_cons, Multiset.foldr_cons, Multiset.foldr_cons]
    have hrest : (((S.erase a).erase b).val.map (fun m => decide (m = a) || decide (m = b))).foldr xor false = false := by
      have hall : ∀ v ∈ (((S.erase a).erase b).val.map (fun m => decide (m = a) || decide (m = b))), v = false := by
        intro v hv
        obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.1 hv
        have hm1 : m ≠ b := (Finset.mem_erase.1 (Finset.mem_def.2 hm)).1
        have hm2 : m ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 (Finset.mem_def.2 hm)).2).1
        simp [hm1, hm2]
      generalize (((S.erase a).erase b).val.map (fun m => decide (m = a) || decide (m = b))) = M at hall ⊢
      induction M using Multiset.induction_on with
      | empty => rfl
      | cons x s ih =>
        rw [Multiset.foldr_cons, hall x (Multiset.mem_cons_self _ _),
          ih (fun v hv => hall v (Multiset.mem_cons_of_mem hv))]
        rfl
    rw [hrest]
    simp
  · have hall : ∀ v ∈ (S.val.map (fun m => decide (m = a) || decide (m = b))), v = false := by
      intro v hv
      obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.1 hv
      have hmr : m.val % 3 = r := (Finset.mem_filter.1 (Finset.mem_def.2 hm)).2
      have hma : m ≠ a := fun h => har (h ▸ hmr)
      have hmb : m ≠ b := fun h => har (hmod.trans (h ▸ hmr))
      simp [hma, hmb]
    generalize (S.val.map (fun m => decide (m = a) || decide (m = b))) = M at hall ⊢
    induction M using Multiset.induction_on with
    | empty => rfl
    | cons x s ih =>
      rw [Multiset.foldr_cons, hall x (Multiset.mem_cons_self _ _),
        ih (fun v hv => hall v (Multiset.mem_cons_of_mem hv))]
      rfl

private theorem segXor_of_three_classes {L : ℕ} (hL : 0 < L) (hL3 : L % 3 = 0)
    (a b c : Fin L) (hab : a.val % 3 ≠ b.val % 3) (hac : a.val % 3 ≠ c.val % 3)
    (hbc : b.val % 3 ≠ c.val % 3) (r : ℕ) (hr : r < 3) :
    segXor L hL (fun m => decide (m = a) || decide (m = b) || decide (m = c)) r (L / 3) = true := by
  rw [segXor_eq_xor_fin hL _ r (L / 3) (by omega) hr]
  have hcomm : Std.Commutative xor := ⟨fun x y => by cases x <;> cases y <;> rfl⟩
  have hassoc : Std.Associative xor := ⟨fun x y z => by cases x <;> cases y <;> cases z <;> rfl⟩
  set S := Finset.univ.filter (fun m : Fin L => m.val % 3 = r)
  have hex : ∃ u ∈ ({a, b, c} : Finset (Fin L)), u.val % 3 = r ∧
      ∀ v ∈ ({a, b, c} : Finset (Fin L)), v ≠ u → v.val % 3 ≠ r := by
    have hcases : a.val % 3 = r ∨ b.val % 3 = r ∨ c.val % 3 = r := by omega
    rcases hcases with h | h | h
    · refine ⟨a, by simp, h, fun v hv hne => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact absurd rfl hne
      · omega
      · omega
    · refine ⟨b, by simp, h, fun v hv hne => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · omega
      · exact absurd rfl hne
      · omega
    · refine ⟨c, by simp, h, fun v hv hne => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · omega
      · omega
      · exact absurd rfl hne
  obtain ⟨u, huM, hur, huniq⟩ := hex
  have huS : u ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hur⟩
  have hsplit : S = insert u (S.erase u) := (Finset.insert_erase huS).symm
  rw [hsplit, Finset.insert_val_of_notMem (Finset.notMem_erase u S),
    Multiset.map_cons, Multiset.foldr_cons]
  have hu_val : (decide (u = a) || decide (u = b) || decide (u = c)) = true := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at huM
    rcases huM with rfl | rfl | rfl <;> simp
  have hrest : ((S.erase u).val.map (fun m => decide (m = a) || decide (m = b) || decide (m = c))).foldr xor false = false := by
    have hall : ∀ v ∈ ((S.erase u).val.map (fun m => decide (m = a) || decide (m = b) || decide (m = c))), v = false := by
      intro v hv
      obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.1 hv
      have hmu : m ≠ u := (Finset.mem_erase.1 (Finset.mem_def.2 hm)).1
      have hmr : m.val % 3 = r := (Finset.mem_filter.1 (Finset.mem_erase.1 (Finset.mem_def.2 hm)).2).2
      have hma : m ≠ a := fun h => huniq a (by simp) (by rwa [← h]) (h ▸ hmr)
      have hmb : m ≠ b := fun h => huniq b (by simp) (by rwa [← h]) (h ▸ hmr)
      have hmc : m ≠ c := fun h => huniq c (by simp) (by rwa [← h]) (h ▸ hmr)
      simp [hma, hmb, hmc]
    generalize ((S.erase u).val.map (fun m => decide (m = a) || decide (m = b) || decide (m = c))) = M at hall ⊢
    induction M using Multiset.induction_on with
    | empty => rfl
    | cons x s ih =>
      rw [Multiset.foldr_cons, hall x (Multiset.mem_cons_self _ _),
        ih (fun v hv => hall v (Multiset.mem_cons_of_mem hv))]
      rfl
  rw [hu_val, hrest]
  rfl

private theorem solve_mix_of_parity (k d : ℕ) (hk : 0 < k) (hd : d = 1 ∨ d = 2) (hbig : 4 * d + 4 < k)
    (y : Fin k → Bool)
    (hpar1 : d = 1 → k % 3 = 0 →
      segXor k hk y 0 (k / 3) = segXor k hk y 1 (k / 3) ∧
      segXor k hk y 1 (k / 3) = segXor k hk y 2 (k / 3))
    (hpar2_odd : d = 2 → k % 2 = 1 → k % 3 = 0 →
      let y' : Fin k → Bool := fun m => y (idx k hk (2 * m.val))
      segXor k hk y' 0 (k / 3) = segXor k hk y' 1 (k / 3) ∧
      segXor k hk y' 1 (k / 3) = segXor k hk y' 2 (k / 3))
    (hpar2_even : d = 2 → k % 2 = 0 → k % 3 = 0 →
      let L := k / 2
      have hL : 0 < L := by omega
      let ye : Fin L → Bool := fun m => y (idx k hk (2 * m.val))
      let yo : Fin L → Bool := fun m => y (idx k hk (2 * m.val + 1))
      (segXor L hL ye 0 (L / 3) = segXor L hL ye 1 (L / 3) ∧
       segXor L hL ye 1 (L / 3) = segXor L hL ye 2 (L / 3)) ∧
      (segXor L hL yo 0 (L / 3) = segXor L hL yo 1 (L / 3) ∧
       segXor L hL yo 1 (L / 3) = segXor L hL yo 2 (L / 3))) :
    ∃ x : Fin k → Bool, mixW hk d x = y := by
  rcases hd with rfl | rfl
  · obtain ⟨x, hx⟩ := solve_1D k (by omega) y (hpar1 rfl)
    refine ⟨x, funext fun i => ?_⟩
    exact hx i
  · by_cases hodd : k % 2 = 1
    · set y' : Fin k → Bool := fun m => y (idx k hk (2 * m.val))
      obtain ⟨x', hx'⟩ := solve_1D k (by omega) y' (hpar2_odd rfl hodd)
      let inv2 : Fin k → Fin k := fun i =>
        ⟨if i.val % 2 = 0 then i.val / 2 else (i.val + k) / 2, by
          split_ifs <;> omega⟩
      have hinv_left : ∀ m : Fin k, inv2 (idx k hk (2 * m.val)) = m := by
        intro m
        apply Fin.ext
        dsimp only [inv2, idx]
        have hm := m.isLt
        by_cases h2m : 2 * m.val < k
        · have hmod : (2 * m.val) % k = 2 * m.val := Nat.mod_eq_of_lt h2m
          simp only [hmod]
          have hev : (2 * m.val) % 2 = 0 := by omega
          rw [if_pos hev]; omega
        · have hsub : (2 * m.val) % k = 2 * m.val - k := by
            conv_lhs => rw [show 2 * m.val = k + (2 * m.val - k) by omega, Nat.add_mod_left]
            exact Nat.mod_eq_of_lt (by omega)
          simp only [hsub]
          have hno : ¬ ((2 * m.val - k) % 2 = 0) := by omega
          rw [if_neg hno]; omega
      have hinv_right : ∀ i : Fin k, idx k hk (2 * (inv2 i).val) = i := by
        intro i
        apply Fin.ext
        dsimp only [inv2, idx]
        have hi := i.isLt
        split_ifs with hev
        · rw [show 2 * (i.val / 2) = i.val by omega]; exact Nat.mod_eq_of_lt hi
        · rw [show 2 * ((i.val + k) / 2) = k + i.val by omega, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt hi
      refine ⟨fun i => x' (inv2 i), funext fun i => ?_⟩
      set m := inv2 i
      have hmi : idx k hk (2 * m.val) = i := hinv_right i
      have hstep1 : inv2 (idx k hk (i.val + 2)) = ⟨(m.val + 1) % k, Nat.mod_lt _ hk⟩ := by
        have h1 : idx k hk (i.val + 2) = idx k hk (2 * ((m.val + 1) % k)) := by
          apply Fin.ext
          dsimp only [idx]
          have hi_eq : i.val = (2 * m.val) % k := by simpa [idx] using congrArg Fin.val hmi.symm
          rw [hi_eq, Nat.mod_add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
            show 2 * (m.val + 1) = 2 * m.val + 2 by ring]
        rw [h1]
        exact hinv_left ⟨(m.val + 1) % k, Nat.mod_lt _ hk⟩
      have hstep2 : inv2 (idx k hk (i.val + k - 2)) = ⟨(m.val + k - 1) % k, Nat.mod_lt _ hk⟩ := by
        have h1 : idx k hk (i.val + k - 2) = idx k hk (2 * ((m.val + k - 1) % k)) := by
          apply Fin.ext
          dsimp only [idx]
          have hi_eq : i.val = (2 * m.val) % k := by simpa [idx] using congrArg Fin.val hmi.symm
          have h2 : (2 * ((m.val + k - 1) % k)) % k = (2 * (m.val + k - 1)) % k := by
            rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
          rw [h2, show 2 * (m.val + k - 1) = 2 * m.val + k + (k - 2) by omega]
          have h3 : (2 * m.val + k + (k - 2)) % k = (i.val + (k - 2)) % k := by
            rw [Nat.add_mod, Nat.add_mod (2 * m.val), Nat.mod_self, Nat.add_zero, Nat.mod_mod,
              ← hi_eq, Nat.add_mod_mod]
          rw [h3, show i.val + k - 2 = i.val + (k - 2) by omega]
        rw [h1]
        exact hinv_left ⟨(m.val + k - 1) % k, Nat.mod_lt _ hk⟩
      simp only [mixW]
      rw [hstep1, hstep2]
      have hres := hx' m
      simpa only [y', hmi] using hres
    · have heven : k % 2 = 0 := by omega
      set L := k / 2
      have hL : 3 ≤ L := by omega
      have hLpos : 0 < L := by omega
      have h2L : 2 * L = k := by omega
      set ye : Fin L → Bool := fun m => y (idx k hk (2 * m.val))
      set yo : Fin L → Bool := fun m => y (idx k hk (2 * m.val + 1))
      have hL3_iff : L % 3 = 0 → k % 3 = 0 := by omega
      obtain ⟨xe, hxe⟩ := solve_1D L hL ye (fun hL3 => (hpar2_even rfl heven (hL3_iff hL3)).1)
      obtain ⟨xo, hxo⟩ := solve_1D L hL yo (fun hL3 => (hpar2_even rfl heven (hL3_iff hL3)).2)
      refine ⟨fun i => if i.val % 2 = 0 then xe ⟨i.val / 2, by omega⟩ else xo ⟨i.val / 2, by omega⟩,
        funext fun i => ?_⟩
      simp only [mixW]
      have hi := i.isLt
      have hp1 : (idx k hk (i.val + 2)).val % 2 = i.val % 2 := by
        dsimp only [idx]
        by_cases h2 : i.val + 2 < k
        · rw [Nat.mod_eq_of_lt h2]; omega
        · rw [show i.val + 2 = k + (i.val + 2 - k) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (show i.val + 2 - k < k by omega)]
          omega
      have hp2 : (idx k hk (i.val + k - 2)).val % 2 = i.val % 2 := by
        dsimp only [idx]
        by_cases h2 : 2 ≤ i.val
        · rw [show i.val + k - 2 = k + (i.val - 2) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (show i.val - 2 < k by omega)]
          omega
        · rw [Nat.mod_eq_of_lt (show i.val + k - 2 < k by omega)]; omega
      have hd1 : (idx k hk (i.val + 2)).val / 2 = (i.val / 2 + 1) % L := by
        dsimp only [idx]
        by_cases h2 : i.val + 2 < k
        · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (show i.val / 2 + 1 < L by omega)]; omega
        · rw [show i.val + 2 = k + (i.val + 2 - k) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (show i.val + 2 - k < k by omega)]
          have : i.val / 2 + 1 = L := by omega
          rw [this, Nat.mod_self]; omega
      have hd2 : (idx k hk (i.val + k - 2)).val / 2 = (i.val / 2 + L - 1) % L := by
        dsimp only [idx]
        by_cases h2 : 2 ≤ i.val
        · rw [show i.val + k - 2 = k + (i.val - 2) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (show i.val - 2 < k by omega)]
          rw [show i.val / 2 + L - 1 = L + (i.val / 2 - 1) by omega, Nat.add_mod_left,
            Nat.mod_eq_of_lt (show i.val / 2 - 1 < L by omega)]
          omega
        · rw [Nat.mod_eq_of_lt (show i.val + k - 2 < k by omega),
            Nat.mod_eq_of_lt (show i.val / 2 + L - 1 < L by omega)]; omega
      by_cases hev : i.val % 2 = 0
      · simp only [hp1, hp2, if_pos hev]
        have hf1 : (⟨(idx k hk (i.val + 2)).val / 2, by omega⟩ : Fin L) =
            ⟨(i.val / 2 + 1) % L, Nat.mod_lt _ hLpos⟩ := Fin.ext hd1
        have hf2 : (⟨(idx k hk (i.val + k - 2)).val / 2, by omega⟩ : Fin L) =
            ⟨(i.val / 2 + L - 1) % L, Nat.mod_lt _ hLpos⟩ := Fin.ext hd2
        rw [hf1, hf2, hxe ⟨i.val / 2, by omega⟩]
        simp only [ye]
        congr 1
        apply Fin.ext
        simp only [idx]
        rw [show 2 * (i.val / 2) = i.val by omega, Nat.mod_eq_of_lt hi]
      · simp only [hp1, hp2, if_neg hev]
        have hf1 : (⟨(idx k hk (i.val + 2)).val / 2, by omega⟩ : Fin L) =
            ⟨(i.val / 2 + 1) % L, Nat.mod_lt _ hLpos⟩ := Fin.ext hd1
        have hf2 : (⟨(idx k hk (i.val + k - 2)).val / 2, by omega⟩ : Fin L) =
            ⟨(i.val / 2 + L - 1) % L, Nat.mod_lt _ hLpos⟩ := Fin.ext hd2
        rw [hf1, hf2, hxo ⟨i.val / 2, by omega⟩]
        simp only [yo]
        congr 1
        apply Fin.ext
        simp only [idx]
        rw [show 2 * (i.val / 2) + 1 = i.val by omega, Nat.mod_eq_of_lt hi]

private def primaryOff (d : ℕ) (l : Fin 4) : ℕ :=
  if l.val = 0 then 0 else if l.val = 1 then 1 else if l.val = 2 then 2 * d + 1 else 2 * d + 2

private theorem primaryOff_0 (d : ℕ) : primaryOff d 0 = 0 := rfl
private theorem primaryOff_1 (d : ℕ) : primaryOff d 1 = 1 := rfl
private theorem primaryOff_2 (d : ℕ) : primaryOff d 2 = 2 * d + 1 := rfl
private theorem primaryOff_3 (d : ℕ) : primaryOff d 3 = 2 * d + 2 := rfl

private theorem primaryOff_val (d : ℕ) (l : Fin 4) :
    (l.val = 0 ∧ primaryOff d l = 0) ∨
    (l.val = 1 ∧ primaryOff d l = 1) ∨
    (l.val = 2 ∧ primaryOff d l = 2 * d + 1) ∨
    (l.val = 3 ∧ primaryOff d l = 2 * d + 2) := by
  rcases l with ⟨v, hv⟩
  interval_cases v <;> simp [primaryOff]

private theorem primaryOff_cases (d : ℕ) (l : Fin 4) :
    primaryOff d l = 0 ∨ primaryOff d l = 1 ∨ primaryOff d l = 2 * d + 1 ∨ primaryOff d l = 2 * d + 2 := by
  rcases primaryOff_val d l with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

private def primarySite (k d : ℕ) (hk : 0 < k) (b : Fin (k / (4 * d + 5))) (l : Fin 4) : Fin k :=
  idx k hk (b.val * (4 * d + 5) + primaryOff d l)

private def repA (k d : ℕ) (p : ℕ) : ℕ :=
  if d = 1 then
    if 2 ≤ k / (4 * d + 5) then 6 else 5
  else
    if k % 2 = 1 then 3
    else if p % 2 = 1 then 3
    else if 2 ≤ k / (4 * d + 5) then 16 else 8

private def repB (k d : ℕ) (p : ℕ) : ℕ :=
  if d = 1 then
    if 2 ≤ k / (4 * d + 5) then 16 else 7
  else
    if k % 2 = 1 then 11
    else if p % 2 = 1 then 11
    else if 2 ≤ k / (4 * d + 5) then 24 else 16

private def orbitClass (k d : ℕ) (p : ℕ) : ℕ :=
  if d = 1 then p % 3
  else if k % 2 = 1 then p % 3
  else (p / 2) % 3

private def basisEmbed0 (k d : ℕ) (hk : 0 < k) (b : Fin (k / (4 * d + 5))) (l : Fin 4)
    (i : Fin k) : Bool :=
  let p := b.val * (4 * d + 5) + primaryOff d l
  if k % 3 = 0 then
    let rA := repA k d p
    let rB := repB k d p
    if orbitClass k d p = orbitClass k d rA then
      decide (i.val = p) || decide (i.val = rA)
    else if orbitClass k d p = orbitClass k d rB then
      decide (i.val = p) || decide (i.val = rB)
    else
      decide (i.val = p) || decide (i.val = rA) || decide (i.val = rB)
  else
    decide (i.val = p)

private def isRepair (k d i : ℕ) : Prop :=
  k % 3 = 0 ∧
    (if d = 1 then
      if 2 ≤ k / (4 * d + 5) then i = 6 ∨ i = 16 else i = 5 ∨ i = 7
    else if k % 2 = 1 then i = 3 ∨ i = 11
    else if 2 ≤ k / (4 * d + 5) then i = 3 ∨ i = 11 ∨ i = 16 ∨ i = 24
    else i = 3 ∨ i = 11 ∨ i = 8 ∨ i = 16)

private def isPrimary (k d i : ℕ) : Prop :=
  ∃ (b : Fin (k / (4 * d + 5))) (l : Fin 4), i = b.val * (4 * d + 5) + primaryOff d l

private def isActive (k d i : ℕ) : Prop :=
  isPrimary k d i ∨ isRepair k d i

private theorem primary_lt_k (k d : ℕ) (b : Fin (k / (4 * d + 5))) (l : Fin 4) :
    b.val * (4 * d + 5) + primaryOff d l < k := by
  have hb : b.val + 1 ≤ k / (4 * d + 5) := b.isLt
  have hmul : b.val * (4 * d + 5) + (4 * d + 5) ≤ k := by
    rw [← Nat.succ_mul]
    exact le_trans (Nat.mul_le_mul_right _ hb) (Nat.div_mul_le_self k (4 * d + 5))
  rcases primaryOff_cases d l with hp | hp | hp | hp <;> (rw [hp]; omega)

private theorem repair_not_primary (k d i : ℕ) (hd : d = 1 ∨ d = 2) (hbig : 4 * d + 4 < k)
    (hrep : isRepair k d i) : ¬ isPrimary k d i := by
  rintro ⟨b, l, rfl⟩
  have h1 := hrep.2
  rcases hd with rfl | rfl
  · simp only [↓reduceIte] at h1
    rcases primaryOff_cases 1 l with hp | hp | hp | hp <;>
      (rw [hp] at h1; split_ifs at h1 with hq <;> rcases h1 with h | h <;> omega)
  · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at h1
    rcases primaryOff_cases 2 l with hp | hp | hp | hp <;>
      (rw [hp] at h1; split_ifs at h1 with hodd hq
       · rcases h1 with h | h <;> omega
       · rcases h1 with h | h | h | h <;> omega
       · rcases h1 with h | h | h | h <;> omega)

private theorem repA_isRepair (k d p : ℕ) (hd : d = 1 ∨ d = 2) (hk3 : k % 3 = 0) :
    isRepair k d (repA k d p) := by
  refine ⟨hk3, ?_⟩
  rcases hd with rfl | rfl
  · unfold repA; simp only [↓reduceIte]; split_ifs <;> simp
  · unfold repA
    simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
    split_ifs <;> simp

private theorem repB_isRepair (k d p : ℕ) (hd : d = 1 ∨ d = 2) (hk3 : k % 3 = 0) :
    isRepair k d (repB k d p) := by
  refine ⟨hk3, ?_⟩
  rcases hd with rfl | rfl
  · unfold repB; simp only [↓reduceIte]; split_ifs <;> simp
  · unfold repB
    simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
    split_ifs <;> simp

private theorem rep_lt_k (k d p : ℕ) (hd : d = 1 ∨ d = 2) (hbig : 4 * d + 4 < k) (hk3 : k % 3 = 0) :
    repA k d p < k ∧ repB k d p < k := by
  rcases hd with rfl | rfl
  · unfold repA repB
    simp only [↓reduceIte]
    split_ifs with hq
    · have : 2 * 9 ≤ k := le_trans (Nat.mul_le_mul_right 9 hq) (Nat.div_mul_le_self k 9)
      omega
    · omega
  · unfold repA repB
    simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
    split_ifs with hodd hp hq
    · omega
    · omega
    · have : 2 * 13 ≤ k := le_trans (Nat.mul_le_mul_right 13 hq) (Nat.div_mul_le_self k 13)
      omega
    · omega

private theorem basisEmbed0_at_primary (k d : ℕ) (hk : 0 < k) (hd : d = 1 ∨ d = 2)
    (hbig : 4 * d + 4 < k) (b b' : Fin (k / (4 * d + 5))) (l l' : Fin 4) :
    basisEmbed0 k d hk b l (primarySite k d hk b' l') = decide (b = b' ∧ l = l') := by
  have hp' : b'.val * (4 * d + 5) + primaryOff d l' < k := primary_lt_k k d b' l'
  have hval : (primarySite k d hk b' l').val = b'.val * (4 * d + 5) + primaryOff d l' :=
    Nat.mod_eq_of_lt hp'
  have heq_iff : b'.val * (4 * d + 5) + primaryOff d l' =
      b.val * (4 * d + 5) + primaryOff d l ↔ b = b' ∧ l = l' := by
    constructor
    · intro h
      have hpair : b.val = b'.val ∧ l.val = l'.val := by
        rcases primaryOff_val d l with ⟨hl, hp⟩ | ⟨hl, hp⟩ | ⟨hl, hp⟩ | ⟨hl, hp⟩ <;>
          rcases primaryOff_val d l' with ⟨hl', hpo'⟩ | ⟨hl', hpo'⟩ | ⟨hl', hpo'⟩ | ⟨hl', hpo'⟩ <;>
          (rw [hp, hpo'] at h; rcases hd with rfl | rfl <;> omega)
      exact ⟨Fin.ext hpair.1, Fin.ext hpair.2⟩
    · rintro ⟨rfl, rfl⟩; rfl
  dsimp only [basisEmbed0]
  rw [hval]
  by_cases hk3 : k % 3 = 0
  · have hnoA : b'.val * (4 * d + 5) + primaryOff d l' ≠
        repA k d (b.val * (4 * d + 5) + primaryOff d l) := fun h =>
      repair_not_primary k d _ hd hbig (h ▸ repA_isRepair k d _ hd hk3) ⟨b', l', rfl⟩
    have hnoB : b'.val * (4 * d + 5) + primaryOff d l' ≠
        repB k d (b.val * (4 * d + 5) + primaryOff d l) := fun h =>
      repair_not_primary k d _ hd hbig (h ▸ repB_isRepair k d _ hd hk3) ⟨b', l', rfl⟩
    simp only [if_pos hk3]
    split_ifs <;> simp [hnoA, hnoB, heq_iff]
  · simp [if_neg hk3, heq_iff]

private theorem basisEmbed0_zero_outside (k d : ℕ) (hk : 0 < k) (hd : d = 1 ∨ d = 2)
    (b : Fin (k / (4 * d + 5))) (l : Fin 4) (i : Fin k) (hnot : ¬ isActive k d i.val) :
    basisEmbed0 k d hk b l i = false := by
  have hnp : ¬ isPrimary k d i.val := fun h => hnot (Or.inl h)
  have hnr : ¬ isRepair k d i.val := fun h => hnot (Or.inr h)
  have hneP : i.val ≠ b.val * (4 * d + 5) + primaryOff d l := fun h => hnp ⟨b, l, h⟩
  unfold basisEmbed0
  by_cases hk3 : k % 3 = 0
  · have hneA : i.val ≠ repA k d (b.val * (4 * d + 5) + primaryOff d l) := fun h =>
      hnr (h ▸ repA_isRepair k d _ hd hk3)
    have hneB : i.val ≠ repB k d (b.val * (4 * d + 5) + primaryOff d l) := fun h =>
      hnr (h ▸ repB_isRepair k d _ hd hk3)
    simp only [if_pos hk3]
    split_ifs <;> simp [hneP, hneA, hneB]
  · simp [if_neg hk3, hneP]

private theorem basisEmbed0_in_mix (k d : ℕ) (hk : 0 < k) (hd : d = 1 ∨ d = 2)
    (hbig : 4 * d + 4 < k) (b : Fin (k / (4 * d + 5))) (l : Fin 4) :
    ∃ x : Fin k → Bool, mixW hk d x = basisEmbed0 k d hk b l := by
  set p := b.val * (4 * d + 5) + primaryOff d l
  have hp : p < k := primary_lt_k k d b l
  apply solve_mix_of_parity k d hk hd hbig
  · intro hd1 hk3
    subst hd1
    have hlt := rep_lt_k k 1 p (Or.inl rfl) hbig hk3
    have hdisjA : p ≠ repA k 1 p := fun h =>
      repair_not_primary k 1 p (Or.inl rfl) hbig (h ▸ repA_isRepair k 1 p (Or.inl rfl) hk3) ⟨b, l, rfl⟩
    have hdisjB : p ≠ repB k 1 p := fun h =>
      repair_not_primary k 1 p (Or.inl rfl) hbig (h ▸ repB_isRepair k 1 p (Or.inl rfl) hk3) ⟨b, l, rfl⟩
    have hAB_cls : (repA k 1 p) % 3 ≠ (repB k 1 p) % 3 := by
      unfold repA repB; simp only [↓reduceIte]; split_ifs <;> omega
    set fp : Fin k := ⟨p, hp⟩
    set fA : Fin k := ⟨repA k 1 p, hlt.1⟩
    set fB : Fin k := ⟨repB k 1 p, hlt.2⟩
    unfold basisEmbed0
    simp only [if_pos hk3, orbitClass, ↓reduceIte]
    split_ifs with h1 h2
    · have heq : (fun i : Fin k => decide (i.val = p) || decide (i.val = repA k 1 p)) =
          (fun m : Fin k => decide (m = fp) || decide (m = fA)) := by
        funext m; simp [Fin.ext_iff, fp, fA]
      rw [heq]
      have h0 := segXor_of_two_eq hk hk3 fp fA (fun h => hdisjA (congrArg Fin.val h)) h1 0 (by omega)
      have h1' := segXor_of_two_eq hk hk3 fp fA (fun h => hdisjA (congrArg Fin.val h)) h1 1 (by omega)
      have h2' := segXor_of_two_eq hk hk3 fp fA (fun h => hdisjA (congrArg Fin.val h)) h1 2 (by omega)
      exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
    · have heq : (fun i : Fin k => decide (i.val = p) || decide (i.val = repB k 1 p)) =
          (fun m : Fin k => decide (m = fp) || decide (m = fB)) := by
        funext m; simp [Fin.ext_iff, fp, fB]
      rw [heq]
      have h0 := segXor_of_two_eq hk hk3 fp fB (fun h => hdisjB (congrArg Fin.val h)) h2 0 (by omega)
      have h1' := segXor_of_two_eq hk hk3 fp fB (fun h => hdisjB (congrArg Fin.val h)) h2 1 (by omega)
      have h2' := segXor_of_two_eq hk hk3 fp fB (fun h => hdisjB (congrArg Fin.val h)) h2 2 (by omega)
      exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
    · have heq : (fun i : Fin k => decide (i.val = p) || decide (i.val = repA k 1 p) || decide (i.val = repB k 1 p)) =
          (fun m : Fin k => decide (m = fp) || decide (m = fA) || decide (m = fB)) := by
        funext m; simp [Fin.ext_iff, fp, fA, fB]
      rw [heq]
      have h0 := segXor_of_three_classes hk hk3 fp fA fB h1 h2 hAB_cls 0 (by omega)
      have h1' := segXor_of_three_classes hk hk3 fp fA fB h1 h2 hAB_cls 1 (by omega)
      have h2' := segXor_of_three_classes hk hk3 fp fA fB h1 h2 hAB_cls 2 (by omega)
      exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
  · intro hd2 hodd hk3
    subst hd2
    dsimp only
    have hlt := rep_lt_k k 2 p (Or.inr rfl) hbig hk3
    have hdisjA : p ≠ repA k 2 p := fun h =>
      repair_not_primary k 2 p (Or.inr rfl) hbig (h ▸ repA_isRepair k 2 p (Or.inr rfl) hk3) ⟨b, l, rfl⟩
    have hdisjB : p ≠ repB k 2 p := fun h =>
      repair_not_primary k 2 p (Or.inr rfl) hbig (h ▸ repB_isRepair k 2 p (Or.inr rfl) hk3) ⟨b, l, rfl⟩
    have hAB_cls : (repA k 2 p) % 3 ≠ (repB k 2 p) % 3 := by
      unfold repA repB; simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, hodd]; omega
    let inv2 : ℕ → Fin k := fun a =>
      ⟨(if a % 2 = 0 then a / 2 else (a + k) / 2) % k, Nat.mod_lt _ hk⟩
    have hinv_val : ∀ (a : ℕ), a < k →
        (inv2 a).val = if a % 2 = 0 then a / 2 else (a + k) / 2 := by
      intro a ha
      dsimp only [inv2]
      exact Nat.mod_eq_of_lt (by split_ifs <;> omega)
    have hinv_eq : ∀ (a : ℕ) (ha : a < k) (m : Fin k),
        ((idx k hk (2 * m.val)).val = a) ↔ (m = inv2 a) := by
      intro a ha m
      have hm := m.isLt
      constructor
      · intro h
        apply Fin.ext
        dsimp only [idx] at h
        rw [hinv_val a ha]
        by_cases h2m : 2 * m.val < k
        · rw [Nat.mod_eq_of_lt h2m] at h
          have hev : a % 2 = 0 := by omega
          rw [if_pos hev]; omega
        · have hsub : (2 * m.val) % k = 2 * m.val - k := by
            conv_lhs => rw [show 2 * m.val = k + (2 * m.val - k) by omega, Nat.add_mod_left]
            exact Nat.mod_eq_of_lt (by omega)
          rw [hsub] at h
          have hno : ¬ (a % 2 = 0) := by omega
          rw [if_neg hno]; omega
      · rintro rfl
        dsimp only [idx]
        rw [hinv_val a ha]
        split_ifs with hev
        · rw [show 2 * (a / 2) = a by omega]; exact Nat.mod_eq_of_lt ha
        · rw [show 2 * ((a + k) / 2) = k + a by omega, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt ha
    have hinv_mod3 : ∀ (a : ℕ), a < k → (inv2 a).val % 3 = (2 * a) % 3 := by
      intro a ha
      rw [hinv_val a ha]
      split_ifs with hev <;> omega
    set fp := inv2 p
    set fA := inv2 (repA k 2 p)
    set fB := inv2 (repB k 2 p)
    have hmod_iff : ∀ a c : ℕ, a < k → c < k → ((inv2 a).val % 3 = (inv2 c).val % 3 ↔ a % 3 = c % 3) := by
      intro a c ha hc; rw [hinv_mod3 a ha, hinv_mod3 c hc]; omega
    unfold basisEmbed0
    simp only [if_pos hk3, orbitClass, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, hodd]
    split_ifs with h1 h2
    · have heq : (fun m : Fin k => decide ((idx k hk (2 * m.val)).val = p) ||
          decide ((idx k hk (2 * m.val)).val = repA k 2 p)) =
          (fun m : Fin k => decide (m = fp) || decide (m = fA)) := by
        funext m; simp [hinv_eq p hp m, hinv_eq (repA k 2 p) hlt.1 m, fp, fA]
      rw [heq]
      have hne : fp ≠ fA := fun h => hdisjA (by
        have h1' := (hinv_eq p hp fp).2 rfl
        have h2' := (hinv_eq (repA k 2 p) hlt.1 fA).2 rfl
        rw [h] at h1'; exact h1'.symm.trans h2')
      have hm3 : fp.val % 3 = fA.val % 3 := (hmod_iff p (repA k 2 p) hp hlt.1).2 h1
      have h0 := segXor_of_two_eq hk hk3 fp fA hne hm3 0 (by omega)
      have h1' := segXor_of_two_eq hk hk3 fp fA hne hm3 1 (by omega)
      have h2' := segXor_of_two_eq hk hk3 fp fA hne hm3 2 (by omega)
      exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
    · have heq : (fun m : Fin k => decide ((idx k hk (2 * m.val)).val = p) ||
          decide ((idx k hk (2 * m.val)).val = repB k 2 p)) =
          (fun m : Fin k => decide (m = fp) || decide (m = fB)) := by
        funext m; simp [hinv_eq p hp m, hinv_eq (repB k 2 p) hlt.2 m, fp, fB]
      rw [heq]
      have hne : fp ≠ fB := fun h => hdisjB (by
        have h1' := (hinv_eq p hp fp).2 rfl
        have h2' := (hinv_eq (repB k 2 p) hlt.2 fB).2 rfl
        rw [h] at h1'; exact h1'.symm.trans h2')
      have hm3 : fp.val % 3 = fB.val % 3 := (hmod_iff p (repB k 2 p) hp hlt.2).2 h2
      have h0 := segXor_of_two_eq hk hk3 fp fB hne hm3 0 (by omega)
      have h1' := segXor_of_two_eq hk hk3 fp fB hne hm3 1 (by omega)
      have h2' := segXor_of_two_eq hk hk3 fp fB hne hm3 2 (by omega)
      exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
    · have heq : (fun m : Fin k => decide ((idx k hk (2 * m.val)).val = p) ||
          decide ((idx k hk (2 * m.val)).val = repA k 2 p) ||
          decide ((idx k hk (2 * m.val)).val = repB k 2 p)) =
          (fun m : Fin k => decide (m = fp) || decide (m = fA) || decide (m = fB)) := by
        funext m; simp [hinv_eq p hp m, hinv_eq (repA k 2 p) hlt.1 m, hinv_eq (repB k 2 p) hlt.2 m, fp, fA, fB]
      rw [heq]
      have hab : fp.val % 3 ≠ fA.val % 3 := fun h => h1 ((hmod_iff p (repA k 2 p) hp hlt.1).1 h)
      have hac : fp.val % 3 ≠ fB.val % 3 := fun h => h2 ((hmod_iff p (repB k 2 p) hp hlt.2).1 h)
      have hbc : fA.val % 3 ≠ fB.val % 3 := fun h => hAB_cls ((hmod_iff (repA k 2 p) (repB k 2 p) hlt.1 hlt.2).1 h)
      have h0 := segXor_of_three_classes hk hk3 fp fA fB hab hac hbc 0 (by omega)
      have h1' := segXor_of_three_classes hk hk3 fp fA fB hab hac hbc 1 (by omega)
      have h2' := segXor_of_three_classes hk hk3 fp fA fB hab hac hbc 2 (by omega)
      exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
  · intro hd2 heven hk3
    subst hd2
    dsimp only
    set L := k / 2
    have hL : 0 < L := by omega
    have hL3 : L % 3 = 0 := by omega
    have h2L : 2 * L = k := by omega
    have hlt := rep_lt_k k 2 p (Or.inr rfl) hbig hk3
    have hdisjA : p ≠ repA k 2 p := fun h =>
      repair_not_primary k 2 p (Or.inr rfl) hbig (h ▸ repA_isRepair k 2 p (Or.inr rfl) hk3) ⟨b, l, rfl⟩
    have hdisjB : p ≠ repB k 2 p := fun h =>
      repair_not_primary k 2 p (Or.inr rfl) hbig (h ▸ repB_isRepair k 2 p (Or.inr rfl) hk3) ⟨b, l, rfl⟩
    have hpar_same : repA k 2 p % 2 = p % 2 ∧ repB k 2 p % 2 = p % 2 := by
      unfold repA repB
      simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, show ¬ (k % 2 = 1) by omega]
      split_ifs <;> omega
    have hAB_cls : (repA k 2 p / 2) % 3 ≠ (repB k 2 p / 2) % 3 := by
      unfold repA repB
      simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, show ¬ (k % 2 = 1) by omega]
      split_ifs <;> omega
    have hzero_seg : ∀ r : ℕ, segXor L hL (fun _ => false) r (L / 3) = false := by
      intro r
      generalize (L / 3) = t
      induction t with
      | zero => rfl
      | succ t ih => simp [segXor, ih]
    set fp : Fin L := ⟨p / 2, by omega⟩
    set fA : Fin L := ⟨repA k 2 p / 2, by omega⟩
    set fB : Fin L := ⟨repB k 2 p / 2, by omega⟩
    have hneA_L : fp ≠ fA := fun h => hdisjA (by
      have h1 : p / 2 = repA k 2 p / 2 := congrArg Fin.val h
      omega)
    have hneB_L : fp ≠ fB := fun h => hdisjB (by
      have h1 : p / 2 = repB k 2 p / 2 := congrArg Fin.val h
      omega)
    have hsame_even : ∀ (a : ℕ) (ha : a < k), a % 2 = 0 → ∀ m : Fin L,
        ((idx k hk (2 * m.val)).val = a) ↔ (m = ⟨a / 2, by omega⟩) := by
      intro a ha ha0 m
      simp only [idx, Fin.ext_iff]
      rw [Nat.mod_eq_of_lt (by have := m.isLt; omega)]
      omega
    have hsame_odd : ∀ (a : ℕ) (ha : a < k), a % 2 = 1 → ∀ m : Fin L,
        ((idx k hk (2 * m.val + 1)).val = a) ↔ (m = ⟨a / 2, by omega⟩) := by
      intro a ha ha1 m
      simp only [idx, Fin.ext_iff]
      rw [Nat.mod_eq_of_lt (by have := m.isLt; omega)]
      omega
    have hdiff_eo : ∀ (a : ℕ), a % 2 = 1 → ∀ m : Fin L, (idx k hk (2 * m.val)).val ≠ a := by
      intro a ha1 m
      simp only [idx]
      rw [Nat.mod_eq_of_lt (by have := m.isLt; omega)]
      omega
    have hdiff_oe : ∀ (a : ℕ), a % 2 = 0 → ∀ m : Fin L, (idx k hk (2 * m.val + 1)).val ≠ a := by
      intro a ha0 m
      simp only [idx]
      rw [Nat.mod_eq_of_lt (by have := m.isLt; omega)]
      omega
    by_cases hp_ev : p % 2 = 0
    · constructor
      · unfold basisEmbed0
        simp only [if_pos hk3, orbitClass, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte,
          show ¬ (k % 2 = 1) by omega]
        split_ifs with h1 h2
        · have heq : (fun m : Fin L => decide ((idx k hk (2 * m.val)).val = p) ||
              decide ((idx k hk (2 * m.val)).val = repA k 2 p)) =
              (fun m : Fin L => decide (m = fp) || decide (m = fA)) := by
            funext m; simp [hsame_even p hp hp_ev m, hsame_even _ hlt.1 (by omega) m, fp, fA]
          rw [heq]
          have h0 := segXor_of_two_eq hL hL3 fp fA hneA_L h1 0 (by omega)
          have h1' := segXor_of_two_eq hL hL3 fp fA hneA_L h1 1 (by omega)
          have h2' := segXor_of_two_eq hL hL3 fp fA hneA_L h1 2 (by omega)
          exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
        · have heq : (fun m : Fin L => decide ((idx k hk (2 * m.val)).val = p) ||
              decide ((idx k hk (2 * m.val)).val = repB k 2 p)) =
              (fun m : Fin L => decide (m = fp) || decide (m = fB)) := by
            funext m; simp [hsame_even p hp hp_ev m, hsame_even _ hlt.2 (by omega) m, fp, fB]
          rw [heq]
          have h0 := segXor_of_two_eq hL hL3 fp fB hneB_L h2 0 (by omega)
          have h1' := segXor_of_two_eq hL hL3 fp fB hneB_L h2 1 (by omega)
          have h2' := segXor_of_two_eq hL hL3 fp fB hneB_L h2 2 (by omega)
          exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
        · have heq : (fun m : Fin L => decide ((idx k hk (2 * m.val)).val = p) ||
              decide ((idx k hk (2 * m.val)).val = repA k 2 p) ||
              decide ((idx k hk (2 * m.val)).val = repB k 2 p)) =
              (fun m : Fin L => decide (m = fp) || decide (m = fA) || decide (m = fB)) := by
            funext m
            simp [hsame_even p hp hp_ev m, hsame_even _ hlt.1 (by omega) m,
              hsame_even _ hlt.2 (by omega) m, fp, fA, fB]
          rw [heq]
          have h0 := segXor_of_three_classes hL hL3 fp fA fB h1 h2 hAB_cls 0 (by omega)
          have h1' := segXor_of_three_classes hL hL3 fp fA fB h1 h2 hAB_cls 1 (by omega)
          have h2' := segXor_of_three_classes hL hL3 fp fA fB h1 h2 hAB_cls 2 (by omega)
          exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
      · have hzero : (fun m : Fin L => basisEmbed0 k 2 hk b l (idx k hk (2 * m.val + 1))) =
            fun _ => false := by
          funext m
          dsimp only [basisEmbed0]
          simp only [if_pos hk3]
          have h1 := hdiff_oe (b.val * (4 * 2 + 5) + primaryOff 2 l) hp_ev m
          have h2 := hdiff_oe (repA k 2 (b.val * (4 * 2 + 5) + primaryOff 2 l)) (hpar_same.1.trans hp_ev) m
          have h3 := hdiff_oe (repB k 2 (b.val * (4 * 2 + 5) + primaryOff 2 l)) (hpar_same.2.trans hp_ev) m
          split_ifs <;> simp [h1, h2, h3]
        rw [hzero, hzero_seg 0, hzero_seg 1, hzero_seg 2]
        exact ⟨rfl, rfl⟩
    · have hp_od : p % 2 = 1 := by omega
      constructor
      · have hzero : (fun m : Fin L => basisEmbed0 k 2 hk b l (idx k hk (2 * m.val))) =
            fun _ => false := by
          funext m
          dsimp only [basisEmbed0]
          simp only [if_pos hk3]
          have h1 := hdiff_eo (b.val * (4 * 2 + 5) + primaryOff 2 l) hp_od m
          have h2 := hdiff_eo (repA k 2 (b.val * (4 * 2 + 5) + primaryOff 2 l)) (hpar_same.1.trans hp_od) m
          have h3 := hdiff_eo (repB k 2 (b.val * (4 * 2 + 5) + primaryOff 2 l)) (hpar_same.2.trans hp_od) m
          split_ifs <;> simp [h1, h2, h3]
        rw [hzero, hzero_seg 0, hzero_seg 1, hzero_seg 2]
        exact ⟨rfl, rfl⟩
      · unfold basisEmbed0
        simp only [if_pos hk3, orbitClass, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte,
          show ¬ (k % 2 = 1) by omega]
        split_ifs with h1 h2
        · have heq : (fun m : Fin L => decide ((idx k hk (2 * m.val + 1)).val = p) ||
              decide ((idx k hk (2 * m.val + 1)).val = repA k 2 p)) =
              (fun m : Fin L => decide (m = fp) || decide (m = fA)) := by
            funext m; simp [hsame_odd p hp hp_od m, hsame_odd _ hlt.1 (by omega) m, fp, fA]
          rw [heq]
          have h0 := segXor_of_two_eq hL hL3 fp fA hneA_L h1 0 (by omega)
          have h1' := segXor_of_two_eq hL hL3 fp fA hneA_L h1 1 (by omega)
          have h2' := segXor_of_two_eq hL hL3 fp fA hneA_L h1 2 (by omega)
          exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
        · have heq : (fun m : Fin L => decide ((idx k hk (2 * m.val + 1)).val = p) ||
              decide ((idx k hk (2 * m.val + 1)).val = repB k 2 p)) =
              (fun m : Fin L => decide (m = fp) || decide (m = fB)) := by
            funext m; simp [hsame_odd p hp hp_od m, hsame_odd _ hlt.2 (by omega) m, fp, fB]
          rw [heq]
          have h0 := segXor_of_two_eq hL hL3 fp fB hneB_L h2 0 (by omega)
          have h1' := segXor_of_two_eq hL hL3 fp fB hneB_L h2 1 (by omega)
          have h2' := segXor_of_two_eq hL hL3 fp fB hneB_L h2 2 (by omega)
          exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩
        · have heq : (fun m : Fin L => decide ((idx k hk (2 * m.val + 1)).val = p) ||
              decide ((idx k hk (2 * m.val + 1)).val = repA k 2 p) ||
              decide ((idx k hk (2 * m.val + 1)).val = repB k 2 p)) =
              (fun m : Fin L => decide (m = fp) || decide (m = fA) || decide (m = fB)) := by
            funext m
            simp [hsame_odd p hp hp_od m, hsame_odd _ hlt.1 (by omega) m,
              hsame_odd _ hlt.2 (by omega) m, fp, fA, fB]
          rw [heq]
          have h0 := segXor_of_three_classes hL hL3 fp fA fB h1 h2 hAB_cls 0 (by omega)
          have h1' := segXor_of_three_classes hL hL3 fp fA fB h1 h2 hAB_cls 1 (by omega)
          have h2' := segXor_of_three_classes hL hL3 fp fA fB h1 h2 hAB_cls 2 (by omega)
          exact ⟨h0.trans h1'.symm, h1'.trans h2'.symm⟩

private theorem pairStart_classify (k d p : ℕ) (hd : d = 1 ∨ d = 2) (hbig : 4 * d + 4 < k)
    (hpk : p < k) (hp : isActive k d p) (hp1 : isActive k d ((p + 1) % k)) :
    (∃ b : Fin (k / (4 * d + 5)), p = b.val * (4 * d + 5) ∨ p = b.val * (4 * d + 5) + 2 * d + 1) ∨
    (d = 1 ∧ k % 3 = 0 ∧ k / (4 * d + 5) = 1 ∧ p = 4) := by
  have hmod1 : ∀ x, x < k - 1 → (x + 1) % k = x + 1 := fun x hx => Nat.mod_eq_of_lt (by omega)
  have hnot_last : p ≠ k - 1 := by
    intro hlast
    subst hlast
    rcases hp with ⟨b, l, h⟩ | ⟨hk3, h⟩
    · have hlt := primary_lt_k k d b l
      have hb : (b.val + 1) * (4 * d + 5) ≤ k :=
        le_trans (Nat.mul_le_mul_right _ b.isLt) (Nat.div_mul_le_self k (4 * d + 5))
      rcases primaryOff_cases d l with hp | hp | hp | hp <;>
        (rw [hp] at h; rcases hd with rfl | rfl <;> omega)
    · rcases hd with rfl | rfl
      · simp only [↓reduceIte] at h
        split_ifs at h with hq
        · have : 2 * 9 ≤ k := le_trans (Nat.mul_le_mul_right 9 hq) (Nat.div_mul_le_self k 9)
          omega
        · omega
      · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at h
        split_ifs at h with hodd hq
        · omega
        · have : 2 * 13 ≤ k := le_trans (Nat.mul_le_mul_right 13 hq) (Nat.div_mul_le_self k 13)
          omega
        · omega
  have hp1_eq : (p + 1) % k = p + 1 := hmod1 p (by omega)
  rw [hp1_eq] at hp1
  rcases hp with ⟨b, l, rfl⟩ | ⟨hk3, hr⟩
  · rcases primaryOff_cases d l with hpo | hpo | hpo | hpo
    · exact Or.inl ⟨b, Or.inl (by rw [hpo]; omega)⟩
    · exfalso
      rw [hpo] at hp1
      rcases hp1 with ⟨b', l', h⟩ | ⟨hk3, hr'⟩
      · rcases primaryOff_cases d l' with hp' | hp' | hp' | hp' <;>
          (rw [hp'] at h; rcases hd with rfl | rfl <;> omega)
      · rcases hd with rfl | rfl
        · simp only [↓reduceIte] at hr'
          split_ifs at hr' with hq <;> omega
        · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hr'
          split_ifs at hr' with hodd hq <;> omega
    · exact Or.inl ⟨b, Or.inr (by rw [hpo]; omega)⟩
    · rw [hpo] at hp1 ⊢
      rcases hp1 with ⟨b', l', h⟩ | ⟨hk3, hr'⟩
      · exfalso
        rcases primaryOff_cases d l' with hp' | hp' | hp' | hp' <;>
          (rw [hp'] at h; rcases hd with rfl | rfl <;> omega)
      · rcases hd with rfl | rfl
        · simp only [↓reduceIte] at hr'
          split_ifs at hr' with hq
          · omega
          · have hq1 : k / 9 = 1 := by
              have : 1 ≤ k / 9 := Nat.div_pos (by omega) (by omega)
              omega
            have hb0 : b.val = 0 := by omega
            exact Or.inr ⟨rfl, hk3, hq1, by omega⟩
        · exfalso
          simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hr'
          split_ifs at hr' with hodd hq <;> omega
  · exfalso
    rcases hd with rfl | rfl
    · simp only [↓reduceIte] at hr
      split_ifs at hr with hq
      · rcases hr with rfl | rfl
        · rcases hp1 with ⟨b', l', h⟩ | ⟨_, hr'⟩
          · rcases primaryOff_cases 1 l' with hp' | hp' | hp' | hp' <;> (rw [hp'] at h; omega)
          · simp only [↓reduceIte, if_pos hq] at hr'; omega
        · rcases hp1 with ⟨b', l', h⟩ | ⟨_, hr'⟩
          · rcases primaryOff_cases 1 l' with hp' | hp' | hp' | hp' <;> (rw [hp'] at h; omega)
          · simp only [↓reduceIte, if_pos hq] at hr'; omega
      · rcases hr with rfl | rfl
        · rcases hp1 with ⟨b', l', h⟩ | ⟨_, hr'⟩
          · rcases primaryOff_cases 1 l' with hp' | hp' | hp' | hp' <;> (rw [hp'] at h; omega)
          · simp only [↓reduceIte, if_neg hq] at hr'; omega
        · rcases hp1 with ⟨b', l', h⟩ | ⟨_, hr'⟩
          · rcases primaryOff_cases 1 l' with hp' | hp' | hp' | hp' <;> (rw [hp'] at h; omega)
          · simp only [↓reduceIte, if_neg hq] at hr'; omega
    · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hr
      split_ifs at hr with hodd hq
      · rcases hr with rfl | rfl <;>
        · rcases hp1 with ⟨b', l', h⟩ | ⟨_, hr'⟩
          · rcases primaryOff_cases 2 l' with hp' | hp' | hp' | hp' <;> (rw [hp'] at h; omega)
          · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, if_pos hodd] at hr'; omega
      · rcases hr with rfl | rfl | rfl | rfl <;>
        · rcases hp1 with ⟨b', l', h⟩ | ⟨_, hr'⟩
          · rcases primaryOff_cases 2 l' with hp' | hp' | hp' | hp' <;> (rw [hp'] at h; omega)
          · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, if_neg hodd, if_pos hq] at hr'; omega
      · rcases hr with rfl | rfl | rfl | rfl <;>
        · rcases hp1 with ⟨b', l', h⟩ | ⟨_, hr'⟩
          · rcases primaryOff_cases 2 l' with hp' | hp' | hp' | hp' <;> (rw [hp'] at h; omega)
          · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, if_neg hodd, if_neg hq] at hr'; omega

private theorem quartic_hit_unique (k d : ℕ) (hk : 0 < k) (hd : d = 1 ∨ d = 2)
    (hbig : 4 * d + 4 < k) (j : Fin k) (d1 d2 : ℕ)
    (hd1 : d1 = 0 ∨ d1 = d ∨ d1 = k - d) (hd2 : d2 = 0 ∨ d2 = d ∨ d2 = k - d)
    (s1 s2 s3 s4 : Fin k)
    (hs1 : s1 = idx k hk (j.val + 2 + d1))
    (hs2 : s2 = idx k hk (j.val + 3 + d1))
    (hs3 : s3 = idx k hk (j.val + 3 + d2))
    (hs4 : s4 = idx k hk (j.val + 4 + d2))
    (hdist13 : s1 ≠ s3) (hdist14 : s1 ≠ s4) (hdist23 : s2 ≠ s3)
    (ha1 : isActive k d s1.val) (ha2 : isActive k d s2.val)
    (ha3 : isActive k d s3.val) (ha4 : isActive k d s4.val) :
    d1 = k - d ∧ d2 = d ∧
      ∃ b : Fin (k / (4 * d + 5)),
        j = idx k hk (b.val * (4 * d + 5) + k + d - 2) ∧
        s1 = primarySite k d hk b 0 ∧ s2 = primarySite k d hk b 1 ∧
        s3 = primarySite k d hk b 2 ∧ s4 = primarySite k d hk b 3 := by
  have hs2_eq : s2.val = (s1.val + 1) % k := by
    rw [hs1, hs2]; simp only [idx]
    rw [Nat.mod_add_mod, show j.val + 2 + d1 + 1 = j.val + 3 + d1 by omega]
  have hs4_eq : s4.val = (s3.val + 1) % k := by
    rw [hs3, hs4]; simp only [idx]
    rw [Nat.mod_add_mod, show j.val + 3 + d2 + 1 = j.val + 4 + d2 by omega]
  have hc1 := pairStart_classify k d s1.val hd hbig s1.isLt ha1 (hs2_eq ▸ ha2)
  have hc3 := pairStart_classify k d s3.val hd hbig s3.isLt ha3 (hs4_eq ▸ ha4)
  have hdiff : (s3.val + k - s1.val) % k = (1 + d2 + k - d1) % k := by
    have h1 : s1.val = (j.val + 2 + d1) % k := by rw [hs1]; rfl
    have h3 : s3.val = (j.val + 3 + d2) % k := by rw [hs3]; rfl
    have hd1_le : d1 ≤ k := by rcases hd1 with rfl | rfl | rfl <;> omega
    have hmod_add : (s1.val + (1 + d2 + k - d1)) % k = s3.val := by
      rw [h1, Nat.mod_add_mod, show j.val + 2 + d1 + (1 + d2 + k - d1) = k + (j.val + 3 + d2) by omega,
        Nat.add_mod_left, ← h3]
    have hlt1 := s1.isLt
    have hlt3 := s3.isLt
    have hval : (s3.val + k - s1.val) % k =
        ((s1.val + (1 + d2 + k - d1)) % k + k - s1.val) % k := by rw [hmod_add]
    rw [hval]
    have h2 : ((s1.val + (1 + d2 + k - d1)) % k + (k - s1.val)) % k =
        (s1.val + (1 + d2 + k - d1) + (k - s1.val)) % k := Nat.mod_add_mod _ _ _
    rw [show (s1.val + (1 + d2 + k - d1)) % k + k - s1.val =
      (s1.val + (1 + d2 + k - d1)) % k + (k - s1.val) by omega, h2,
      show s1.val + (1 + d2 + k - d1) + (k - s1.val) = k + (1 + d2 + k - d1) by omega,
      Nat.add_mod_left]
  have hdist_vals : (d = 1 ∧ ((s3.val + k - s1.val) % k = 2 ∨ (s3.val + k - s1.val) % k = 3)) ∨
      (d = 2 ∧ ((s3.val + k - s1.val) % k = 3 ∨ (s3.val + k - s1.val) % k = 5 ∨
        (s3.val + k - s1.val) % k = k - 3)) := by
    rcases hd with rfl | rfl
    · left; refine ⟨rfl, ?_⟩
      rcases hd1 with rfl | rfl | rfl <;> rcases hd2 with rfl | rfl | rfl
      · exfalso; apply hdist23; rw [hs2, hs3]
      · left; rw [hdiff, show 1 + 1 + k - 0 = k + 2 by omega, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      · exfalso; apply hdist13; apply Fin.ext; rw [hs1, hs3]; dsimp only [idx]
        rw [show j.val + 3 + (k - 1) = k + (j.val + 2) by omega, Nat.add_mod_left]
      · exfalso; apply hdist13; apply Fin.ext; rw [hs1, hs3]
      · exfalso; apply hdist23; rw [hs2, hs3]
      · exfalso; apply hdist14; apply Fin.ext; rw [hs1, hs4]; dsimp only [idx]
        rw [show j.val + 4 + (k - 1) = k + (j.val + 2 + 1) by omega, Nat.add_mod_left]
      · left; rw [hdiff]
        rw [show 1 + 0 + k - (k - 1) = 2 by omega]; exact Nat.mod_eq_of_lt (by omega)
      · right; rw [hdiff]
        rw [show 1 + 1 + k - (k - 1) = 3 by omega]; exact Nat.mod_eq_of_lt (by omega)
      · exfalso; apply hdist23; rw [hs2, hs3]
    · right; refine ⟨rfl, ?_⟩
      rcases hd1 with rfl | rfl | rfl <;> rcases hd2 with rfl | rfl | rfl
      · exfalso; apply hdist23; rw [hs2, hs3]
      · left; rw [hdiff, show 1 + 2 + k - 0 = k + 3 by omega, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      · exfalso; apply hdist14; apply Fin.ext; rw [hs1, hs4]; dsimp only [idx]
        rw [show j.val + 4 + (k - 2) = k + (j.val + 2 + 0) by omega, Nat.add_mod_left]
      · exfalso; apply hdist14; apply Fin.ext; rw [hs1, hs4]
      · exfalso; apply hdist23; rw [hs2, hs3]
      · right; right; rw [hdiff]
        rw [show 1 + (k - 2) + k - 2 = k + (k - 3) by omega, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      · left; rw [hdiff]
        rw [show 1 + 0 + k - (k - 2) = 3 by omega]; exact Nat.mod_eq_of_lt (by omega)
      · right; left; rw [hdiff]
        rw [show 1 + 2 + k - (k - 2) = 5 by omega]; exact Nat.mod_eq_of_lt (by omega)
      · exfalso; apply hdist23; rw [hs2, hs3]
  have hblocks_eq : ∃ b : Fin (k / (4 * d + 5)),
      s1.val = b.val * (4 * d + 5) ∧ s3.val = b.val * (4 * d + 5) + 2 * d + 1 := by
    have hqmul : (k / (4 * d + 5)) * (4 * d + 5) ≤ k := Nat.div_mul_le_self k (4 * d + 5)
    have hmod_sub : ∀ x y : ℕ, x < k → y < k →
        (y + k - x) % k = if x ≤ y then y - x else y + k - x := by
      intro x y hx hy
      split_ifs with hxy
      · rw [show y + k - x = k + (y - x) by omega, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      · exact Nat.mod_eq_of_lt (by omega)
    rw [hmod_sub s1.val s3.val s1.isLt s3.isLt] at hdist_vals
    rcases hdist_vals with ⟨rfl, hdv⟩ | ⟨rfl, hdv⟩
    · rcases hc1 with ⟨b1, h1 | h1⟩ | ⟨_, _, hq1, h1⟩ <;>
        rcases hc3 with ⟨b3, h3 | h3⟩ | ⟨_, _, hq3, h3⟩
      · exfalso
        have hb1 := b1.isLt; have hb3 := b3.isLt
        rw [h1, h3] at hdv; split_ifs at hdv <;> omega
      · have hb1 := b1.isLt; have hb3 := b3.isLt
        rw [h1, h3] at hdv
        have hbeq : b1 = b3 := Fin.ext (by split_ifs at hdv <;> omega)
        subst hbeq
        exact ⟨b1, h1, h3⟩
      · exfalso
        have hb1 := b1.isLt
        rw [h1, h3] at hdv; split_ifs at hdv <;> omega
      · exfalso
        have hb1 := b1.isLt; have hb3 := b3.isLt
        rw [h1, h3] at hdv; split_ifs at hdv <;> omega
      · exfalso
        have hb1 := b1.isLt; have hb3 := b3.isLt
        rw [h1, h3] at hdv; split_ifs at hdv <;> omega
      · exfalso
        have hb1 := b1.isLt
        rw [h1, h3] at hdv; split_ifs at hdv <;> omega
      · exfalso
        have hb3 := b3.isLt
        rw [h1, h3] at hdv; split_ifs at hdv <;> omega
      · exfalso
        have hb3 := b3.isLt
        rw [h1, h3] at hdv; split_ifs at hdv <;> omega
      · exfalso
        rw [h1, h3] at hdv; split_ifs at hdv <;> omega
    · rcases hc1 with ⟨b1, h1 | h1⟩ | ⟨habs, _, _, _⟩
      · rcases hc3 with ⟨b3, h3 | h3⟩ | ⟨habs, _, _, _⟩
        · exfalso
          have hb1 := b1.isLt; have hb3 := b3.isLt
          rw [h1, h3] at hdv; split_ifs at hdv <;> omega
        · have hb1 := b1.isLt; have hb3 := b3.isLt
          rw [h1, h3] at hdv
          have hbeq : b1 = b3 := Fin.ext (by split_ifs at hdv <;> omega)
          subst hbeq
          exact ⟨b1, h1, h3⟩
        · omega
      · rcases hc3 with ⟨b3, h3 | h3⟩ | ⟨habs, _, _, _⟩
        · exfalso
          have hb1 := b1.isLt; have hb3 := b3.isLt
          rw [h1, h3] at hdv; split_ifs at hdv <;> omega
        · exfalso
          have hb1 := b1.isLt; have hb3 := b3.isLt
          rw [h1, h3] at hdv; split_ifs at hdv <;> omega
        · omega
      · omega
  obtain ⟨b, hb1, hb3⟩ := hblocks_eq
  have hdiff_exact : (s3.val + k - s1.val) % k = 2 * d + 1 := by
    rw [hb1, hb3, show b.val * (4 * d + 5) + 2 * d + 1 + k - b.val * (4 * d + 5) =
      k + (2 * d + 1) by omega, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hd_exact : d1 = k - d ∧ d2 = d := by
    rw [hdiff_exact] at hdiff
    rcases hd with rfl | rfl <;> rcases hd1 with rfl | rfl | rfl <;> rcases hd2 with rfl | rfl | rfl
    all_goals first
      | exact ⟨rfl, rfl⟩
      | (exfalso;
         have hlt := Nat.mod_lt (1 + 0 + k - 0) hk;
         try rw [show 1 + 0 + k - 0 = k + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + 1 + k - 0 = k + 2 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + (k - 1) + k - 0 = k + k by omega, Nat.add_mod_left, Nat.mod_self] at hdiff
         try rw [show 1 + 0 + k - 1 = k by omega, Nat.mod_self] at hdiff
         try rw [show 1 + 1 + k - 1 = k + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + (k - 1) + k - 1 = k + (k - 1) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + 0 + k - (k - 1) = 2 by omega, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + (k - 1) + k - (k - 1) = k + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + 2 + k - 0 = k + 3 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + (k - 2) + k - 0 = k + (k - 1) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + 0 + k - 2 = k - 1 by omega, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + 2 + k - 2 = k + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + (k - 2) + k - 2 = k + (k - 3) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + 0 + k - (k - 2) = 3 by omega, Nat.mod_eq_of_lt (by omega)] at hdiff
         try rw [show 1 + (k - 2) + k - (k - 2) = k + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hdiff
         omega)
  refine ⟨hd_exact.1, hd_exact.2, b, ?_, ?_, ?_, ?_, ?_⟩
  · apply Fin.ext
    dsimp only [idx]
    have hs1_val : (j.val + 2 + (k - d)) % k = b.val * (4 * d + 5) := by
      rw [← hb1, hs1, hd_exact.1]; rfl
    have h1 : (b.val * (4 * d + 5) + k + d - 2) % k =
        ((j.val + 2 + (k - d)) % k + (k + d - 2)) % k := by
      rw [hs1_val, show b.val * (4 * d + 5) + k + d - 2 = b.val * (4 * d + 5) + (k + d - 2) by omega]
    rw [h1, Nat.mod_add_mod,
      show j.val + 2 + (k - d) + (k + d - 2) = j.val + k * 2 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  · apply Fin.ext
    dsimp only [primarySite, idx]
    rw [primaryOff_0, hb1]
    simp only [Nat.add_zero]
    exact (Nat.mod_eq_of_lt (by have := primary_lt_k k d b 0; rw [primaryOff_0] at this; omega)).symm
  · apply Fin.ext
    dsimp only [primarySite, idx]
    rw [primaryOff_1, hs2_eq, hb1]
  · apply Fin.ext
    dsimp only [primarySite, idx]
    rw [primaryOff_2, hb3,
      Nat.mod_eq_of_lt (by have := primary_lt_k k d b 2; rw [primaryOff_2] at this; omega)]
    omega
  · apply Fin.ext
    dsimp only [primarySite, idx]
    rw [primaryOff_3, hs4_eq, hb3,
      show b.val * (4 * d + 5) + 2 * d + 1 + 1 = b.val * (4 * d + 5) + (2 * d + 2) by omega]

private theorem rot_rot_cancel (k : ℕ) (hk : 0 < k) (s : ℕ) (x : Fin k → Bool) :
    rotW hk s (rotW hk (k - s % k) x) = x := by
  funext i
  dsimp only [rotW, idx]
  congr 1
  apply Fin.ext
  dsimp only
  have hi := i.isLt
  have hs := Nat.mod_lt s hk
  by_cases hs0 : s % k = 0
  · rw [hs0, Nat.sub_zero, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right,
      Nat.mod_mod, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have hmod : (k - s % k) % k = k - s % k := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    have h1 : ((i.val + k - s % k) % k + k - (k - s % k)) % k =
        ((i.val + k - s % k) % k + s % k) % k := by congr 1; omega
    rw [h1, Nat.mod_add_mod, show i.val + k - s % k + s % k = i.val + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hi]

private theorem rot_add (k : ℕ) (hk : 0 < k) (s : ℕ) (x y : Fin k → Bool) :
    rotW hk s (addW x y) = addW (rotW hk s x) (rotW hk s y) := rfl

private theorem mix_add (k d : ℕ) (hk : 0 < k) (x y : Fin k → Bool) :
    mixW hk d (addW x y) = addW (mixW hk d x) (mixW hk d y) := by
  funext i
  simp only [mixW, addW]
  cases x i <;> cases y i <;>
    cases x (idx k hk (i.val + d)) <;> cases y (idx k hk (i.val + d)) <;>
    cases x (idx k hk (i.val + k - d)) <;> cases y (idx k hk (i.val + k - d)) <;> rfl

private theorem mix_rot (k d : ℕ) (hk : 0 < k) (hd : d < k) (s : ℕ) (x : Fin k → Bool) :
    mixW hk d (rotW hk s x) = rotW hk s (mixW hk d x) := by
  funext i
  simp only [mixW, rotW, idx]
  have hs := Nat.mod_lt s hk
  have hi := i.isLt
  have h1 : ((i.val + d) % k + k - s % k) % k = ((i.val + k - s % k) % k + d) % k := by
    rw [show (i.val + d) % k + k - s % k = (i.val + d) % k + (k - s % k) by omega,
      Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1; omega
  have h2 : ((i.val + k - d) % k + k - s % k) % k = ((i.val + k - s % k) % k + k - d) % k := by
    rw [show (i.val + k - d) % k + k - s % k = (i.val + k - d) % k + (k - s % k) by omega,
      show (i.val + k - s % k) % k + k - d = (i.val + k - s % k) % k + (k - d) by omega,
      Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1; omega
  have hf1 : (⟨((i.val + d) % k + k - s % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      ⟨((i.val + k - s % k) % k + d) % k, Nat.mod_lt _ hk⟩ := Fin.ext h1
  have hf2 : (⟨((i.val + k - d) % k + k - s % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      ⟨((i.val + k - s % k) % k + k - d) % k, Nat.mod_lt _ hk⟩ := Fin.ext h2
  rw [hf1, hf2]

private theorem linear_fold_W {k q : ℕ} (basis : Fin q → Fin 4 → (Fin k → Bool)) :
    let F : (Fin q → Fin 4 → Bool) → (Fin k → Bool) := fun u i =>
      (List.ofFn (fun b : Fin q =>
        (List.ofFn (fun l : Fin 4 => if u b l then basis b l i else false)).foldl xor false)).foldl xor false
    ∀ u v, F (plusB u v) = addW (F u) (F v) := by
  intro F u v
  funext i
  simp only [F, addW]
  rw [xor_foldl_ofFn_add]
  congr 2
  funext b
  rw [xor_foldl_ofFn_add]
  congr 2
  funext l
  simp only [plusB]
  by_cases h1 : u b l = true <;> by_cases h2 : v b l = true <;> simp [h1, h2]

private theorem linear_fold_mix {k d q : ℕ} (hk : 0 < k)
    (pre emb : Fin q → Fin 4 → (Fin k → Bool))
    (hpre : ∀ b l, mixW hk d (pre b l) = emb b l)
    (u : Fin q → Fin 4 → Bool) :
    let Fpre : (Fin q → Fin 4 → Bool) → (Fin k → Bool) := fun u i =>
      (List.ofFn (fun b : Fin q =>
        (List.ofFn (fun l : Fin 4 => if u b l then pre b l i else false)).foldl xor false)).foldl xor false
    let Femb : (Fin q → Fin 4 → Bool) → (Fin k → Bool) := fun u i =>
      (List.ofFn (fun b : Fin q =>
        (List.ofFn (fun l : Fin 4 => if u b l then emb b l i else false)).foldl xor false)).foldl xor false
    mixW hk d (Fpre u) = Femb u := by
  intro Fpre Femb
  funext i
  simp only [mixW, Fpre, Femb]
  rw [xor_foldl_ofFn_add, xor_foldl_ofFn_add]
  congr 2
  funext b
  rw [xor_foldl_ofFn_add, xor_foldl_ofFn_add]
  congr 2
  funext l
  cases h : u b l
  · rfl
  · simp only [↓reduceIte]
    exact congrFun (hpre b l) i

private theorem fold_at_primary {k d : ℕ} (hk : 0 < k) (hd : d = 1 ∨ d = 2)
    (hbig : 4 * d + 4 < k) (u : Fin (k / (4 * d + 5)) → Fin 4 → Bool)
    (b' : Fin (k / (4 * d + 5))) (l' : Fin 4) :
    (List.ofFn (fun b : Fin (k / (4 * d + 5)) =>
      (List.ofFn (fun l : Fin 4 =>
        if u b l then basisEmbed0 k d hk b l (primarySite k d hk b' l') else false)).foldl xor false)).foldl xor false =
    u b' l' := by
  have hinner : ∀ b : Fin (k / (4 * d + 5)),
      (List.ofFn (fun l : Fin 4 =>
        if u b l then basisEmbed0 k d hk b l (primarySite k d hk b' l') else false)).foldl xor false =
      if b = b' then u b' l' else false := by
    intro b
    have hcon : (fun l : Fin 4 =>
        if u b l then basisEmbed0 k d hk b l (primarySite k d hk b' l') else false) =
        (fun l : Fin 4 => if b = b' ∧ l = l' then u b' l' else false) := by
      funext l
      rw [basisEmbed0_at_primary k d hk hd hbig b b' l l']
      by_cases h1 : b = b' ∧ l = l'
      · rcases h1 with ⟨rfl, rfl⟩; simp
      · simp [h1]
    rw [hcon]
    simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil]
    by_cases hbb : b = b'
    · subst hbb
      fin_cases l' <;> simp
    · simp [hbb]
  simp_rw [hinner]
  rw [foldl_xor_map_eq_finset]
  have hcomm : Std.Commutative xor := ⟨fun x y => by cases x <;> cases y <;> rfl⟩
  have hassoc : Std.Associative xor := ⟨fun x y z => by cases x <;> cases y <;> cases z <;> rfl⟩
  have hsplit : (Finset.univ : Finset (Fin (k / (4 * d + 5)))) =
      insert b' (Finset.univ.erase b') := (Finset.insert_erase (Finset.mem_univ b')).symm
  rw [hsplit, Finset.insert_val_of_notMem (Finset.notMem_erase b' _),
    Multiset.map_cons, Multiset.foldr_cons, if_pos rfl]
  have hrest : ((Finset.univ.erase b').val.map (fun b => if b = b' then u b' l' else false)).foldr xor false = false := by
    have hall : ∀ v ∈ ((Finset.univ.erase b').val.map (fun b => if b = b' then u b' l' else false)), v = false := by
      intro v hv
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hv
      have hne : b ≠ b' := (Finset.mem_erase.1 (Finset.mem_def.2 hb)).1
      simp [hne]
    generalize ((Finset.univ.erase b').val.map (fun b => if b = b' then u b' l' else false)) = M at hall ⊢
    induction M using Multiset.induction_on with
    | empty => rfl
    | cons x s ih =>
      rw [Multiset.foldr_cons, hall x (Multiset.mem_cons_self _ _),
        ih (fun v hv => hall v (Multiset.mem_cons_of_mem hv))]
      rfl
  rw [hrest, Bool.xor_false]

private theorem fold_zero_outside {k d : ℕ} (hk : 0 < k) (hd : d = 1 ∨ d = 2)
    (u : Fin (k / (4 * d + 5)) → Fin 4 → Bool) (i : Fin k) (hnot : ¬ isActive k d i.val) :
    (List.ofFn (fun b : Fin (k / (4 * d + 5)) =>
      (List.ofFn (fun l : Fin 4 =>
        if u b l then basisEmbed0 k d hk b l i else false)).foldl xor false)).foldl xor false = false := by
  have hzero_in : ∀ b : Fin (k / (4 * d + 5)),
      (List.ofFn (fun l : Fin 4 =>
        if u b l then basisEmbed0 k d hk b l i else false)).foldl xor false = false := by
    intro b
    have h1 : (fun l : Fin 4 => if u b l then basisEmbed0 k d hk b l i else false) = fun _ => false := by
      funext l
      rw [basisEmbed0_zero_outside k d hk hd b l i hnot]
      simp
    rw [h1]
    rfl
  simp_rw [hzero_in]
  have hgen : ∀ n : ℕ, (List.ofFn (fun _ : Fin n => false)).foldl xor false = false := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.ofFn_succ, List.foldl_cons, Bool.false_xor, ih]
  exact hgen _

private theorem step_not_and_decomp (a b c d : Bool) :
    (!(xor a b) && xor c d) = xor (b && d) (xor (xor (!a && c) (!a && d)) (b && c)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem main_theorem_core (k d : ℕ) (hk : 0 < k) (hd : d = 1 ∨ d = 2)
    (hbig : 4 * d + 4 < k) (s shift : ℕ) :
    let W := Fin k → Bool
    let blocks := k / (4 * d + 5)
    let B := Fin blocks → Fin 4 → Bool
    ∃ lift : B → W, Function.Injective lift ∧
      (∀ x y, lift (plusB x y) = addW (lift x) (lift y)) ∧
      ∀ (t h : ℕ) (name c₁ c₂ mask base : W),
        let observed := fun (key : W) =>
          let initial := mixW hk d (addW (rotW hk s key) name)
          let middle := addW (stepW hk initial) (addW (rotW hk t key) c₁)
          let out := addW (stepW hk (mixW hk d middle)) (addW (rotW hk h key) c₂)
          (List.ofFn (fun bit : Fin k => mask bit && out bit)).foldl xor false
        let target := fun (input : B) =>
          (List.ofFn (fun b : Fin blocks =>
            mask (idx k hk (shift + b.val * (4 * d + 5) + k + d - 2)) &&
            (List.ofFn (input b)).all id)).foldl xor false
        let residual := fun (input : B) => xor (observed (addW base (lift input))) (target input)
        ∀ (v : Fin 4 → B) (x : B), (List.ofFn v).foldl diffB residual x = false := by
  intro W blocks B
  have hd_lt : d < k := by rcases hd with rfl | rfl <;> omega
  let pre0 : Fin blocks → Fin 4 → W := fun b l =>
    Classical.choose (basisEmbed0_in_mix k d hk hd hbig b l)
  have hpre0 : ∀ b l, mixW hk d (pre0 b l) = basisEmbed0 k d hk b l := fun b l =>
    Classical.choose_spec (basisEmbed0_in_mix k d hk hd hbig b l)
  let emb0 : B → W := fun u i =>
    (List.ofFn (fun b : Fin blocks =>
      (List.ofFn (fun l : Fin 4 => if u b l then basisEmbed0 k d hk b l i else false)).foldl xor false)).foldl xor false
  let preFold : B → W := fun u i =>
    (List.ofFn (fun b : Fin blocks =>
      (List.ofFn (fun l : Fin 4 => if u b l then pre0 b l i else false)).foldl xor false)).foldl xor false
  let emb : B → W := fun u => rotW hk shift (emb0 u)
  let lift : B → W := fun u => rotW hk (k - s % k) (rotW hk shift (preFold u))
  have hpreFold_lin : ∀ x y, preFold (plusB x y) = addW (preFold x) (preFold y) :=
    linear_fold_W pre0
  have hemb0_lin : ∀ x y, emb0 (plusB x y) = addW (emb0 x) (emb0 y) :=
    linear_fold_W (basisEmbed0 k d hk)
  have hlift_lin : ∀ x y, lift (plusB x y) = addW (lift x) (lift y) := by
    intro x y
    simp only [lift, hpreFold_lin, rot_add]
  have hmix_lift : ∀ u, mixW hk d (rotW hk s (lift u)) = emb u := by
    intro u
    simp only [lift, emb]
    rw [rot_rot_cancel k hk s, mix_rot k d hk hd_lt shift, linear_fold_mix hk pre0 _ hpre0 u]
  have hemb_lin : ∀ x y, emb (plusB x y) = addW (emb x) (emb y) := by
    intro x y
    simp only [emb, hemb0_lin, rot_add]
  have hemb0_inj : Function.Injective emb0 := by
    intro u v huv
    funext b l
    have h1 := congrFun huv (primarySite k d hk b l)
    dsimp only [emb0] at h1
    rw [fold_at_primary hk hd hbig u b l, fold_at_primary hk hd hbig v b l] at h1
    exact h1
  have hlift_inj : Function.Injective lift := by
    intro u v huv
    apply hemb0_inj
    have h1 : emb u = emb v := by rw [← hmix_lift u, ← hmix_lift v, huv]
    have h2 : rotW hk (k - shift % k) (emb u) = rotW hk (k - shift % k) (emb v) := by rw [h1]
    have hcancel : ∀ z : W, rotW hk (k - shift % k) (rotW hk shift z) = z := by
      intro z
      funext i
      dsimp only [rotW, idx]
      congr 1
      apply Fin.ext
      dsimp only
      have hi := i.isLt
      have hs := Nat.mod_lt shift hk
      by_cases hs0 : shift % k = 0
      · rw [hs0, Nat.sub_zero, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right,
          Nat.mod_mod, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · have hmod : (k - shift % k) % k = k - shift % k := Nat.mod_eq_of_lt (by omega)
        rw [hmod, show (i.val + k - (k - shift % k)) % k + k - shift % k =
          (i.val + k - (k - shift % k)) % k + (k - shift % k) by omega,
          Nat.mod_add_mod, show i.val + k - (k - shift % k) + (k - shift % k) = i.val + k by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    simpa only [emb, hcancel] using h2
  refine ⟨lift, hlift_inj, hlift_lin, ?_⟩
  intro t h name c₁ c₂ mask base observed target residual v x
  apply vanishes4_of_isPoly3
  let init0 : W := mixW hk d (addW (rotW hk s base) name)
  have hinit : ∀ u, mixW hk d (addW (rotW hk s (addW base (lift u))) name) = addW init0 (emb u) := by
    intro u
    have hre : addW (rotW hk s (addW base (lift u))) name =
        addW (addW (rotW hk s base) name) (rotW hk s (lift u)) := by
      funext i; simp only [addW, rotW]
      cases base (idx k hk (i.val + k - s % k)) <;>
        cases lift u (idx k hk (i.val + k - s % k)) <;> cases name i <;> rfl
    rw [hre, mix_add, hmix_lift u]
  let P : B → Fin k → Bool := fun u r =>
    emb u (idx k hk (r.val + 1)) && emb u (idx k hk (r.val + 2))
  let Q : B → Fin k → Bool := fun u r =>
    xor (xor (P u r) (P u (idx k hk (r.val + d)))) (P u (idx k hk (r.val + k - d)))
  have hemb_poly : ∀ i : Fin k, IsPoly 1 (fun u => emb u i) := fun i =>
    isPoly_linear (fun u => emb u i) (fun u₁ u₂ => congrFun (hemb_lin u₁ u₂) i)
  have hlift_poly : ∀ (r : ℕ) (i : Fin k), IsPoly 1 (fun u => rotW hk r (lift u) i) := fun r i =>
    isPoly_linear (fun u => rotW hk r (lift u) i) (fun u₁ u₂ => by
      simp only [rotW, hlift_lin, addW])
  have hP_poly : ∀ r : Fin k, IsPoly 2 (fun u => P u r) := fun r =>
    isPoly_and (d₁ := 1) (d₂ := 1) rfl (hemb_poly _) (hemb_poly _)
  have hQ_poly : ∀ r : Fin k, IsPoly 2 (fun u => Q u r) := fun r =>
    isPoly_xor (isPoly_xor (hP_poly _) (hP_poly _)) (hP_poly _)
  have hmid_decomp : ∀ j : Fin k,
      IsPoly 1 (fun u => xor (stepW hk (addW init0 (emb u)) j) (P u j)) := by
    intro j
    have hre : (fun u => xor (stepW hk (addW init0 (emb u)) j) (P u j)) =
        (fun u => xor (xor (init0 j) (emb u j))
          (xor (xor (!(init0 (idx k hk (j.val + 1))) && init0 (idx k hk (j.val + 2)))
            (!(init0 (idx k hk (j.val + 1))) && emb u (idx k hk (j.val + 2))))
            (emb u (idx k hk (j.val + 1)) && init0 (idx k hk (j.val + 2))))) := by
      funext u
      simp only [stepW, addW, P]
      rw [step_not_and_decomp]
      cases init0 j <;> cases emb u j <;>
        cases init0 (idx k hk (j.val + 1)) <;> cases emb u (idx k hk (j.val + 1)) <;>
        cases init0 (idx k hk (j.val + 2)) <;> cases emb u (idx k hk (j.val + 2)) <;> rfl
    rw [hre]
    apply isPoly_xor
    · exact isPoly_xor (isPoly_mono (by omega) (isPoly_const _)) (hemb_poly j)
    · apply isPoly_xor
      · apply isPoly_xor
        · exact isPoly_mono (by omega) (isPoly_const _)
        · exact isPoly_const_and _ (hemb_poly _)
      · have hcomm : (fun u => emb u (idx k hk (j.val + 1)) && init0 (idx k hk (j.val + 2))) =
            (fun u => init0 (idx k hk (j.val + 2)) && emb u (idx k hk (j.val + 1))) := by
          funext u; exact Bool.and_comm _ _
        rw [hcomm]
        exact isPoly_const_and _ (hemb_poly _)
  let mid : B → W := fun u =>
    addW (stepW hk (addW init0 (emb u))) (addW (rotW hk t (addW base (lift u))) c₁)
  have hmix_mid_decomp : ∀ j : Fin k, IsPoly 1 (fun u => xor (mixW hk d (mid u) j) (Q u j)) := by
    intro j
    have hlin_part : ∀ r : Fin k, IsPoly 1 (fun u => xor (mid u r) (P u r)) := by
      intro r
      have hre : (fun u => xor (mid u r) (P u r)) =
          (fun u => xor (xor (stepW hk (addW init0 (emb u)) r) (P u r))
            (xor (xor (rotW hk t base r) (c₁ r)) (rotW hk t (lift u) r))) := by
        funext u
        simp only [mid, addW, rotW]
        cases stepW hk (addW init0 (emb u)) r <;> cases P u r <;>
          cases base (idx k hk (r.val + k - t % k)) <;>
          cases lift u (idx k hk (r.val + k - t % k)) <;> cases c₁ r <;> rfl
      rw [hre]
      exact isPoly_xor (hmid_decomp r)
        (isPoly_xor (isPoly_mono (by omega) (isPoly_const _)) (hlift_poly t r))
    have hre : (fun u => xor (mixW hk d (mid u) j) (Q u j)) =
        (fun u => xor (xor (xor (mid u j) (P u j)) (xor (mid u (idx k hk (j.val + d))) (P u (idx k hk (j.val + d)))))
          (xor (mid u (idx k hk (j.val + k - d))) (P u (idx k hk (j.val + k - d))))) := by
      funext u
      simp only [mixW, Q]
      cases mid u j <;> cases P u j <;>
        cases mid u (idx k hk (j.val + d)) <;> cases P u (idx k hk (j.val + d)) <;>
        cases mid u (idx k hk (j.val + k - d)) <;> cases P u (idx k hk (j.val + k - d)) <;> rfl
    rw [hre]
    exact isPoly_xor (isPoly_xor (hlin_part _) (hlin_part _)) (hlin_part _)
  let outU : B → W := fun u =>
    addW (stepW hk (mixW hk d (mid u))) (addW (rotW hk h (addW base (lift u))) c₂)
  have hout_decomp : ∀ j : Fin k,
      IsPoly 3 (fun u => xor (outU u j)
        (Q u (idx k hk (j.val + 1)) && Q u (idx k hk (j.val + 2)))) := by
    intro j
    let A1 : B → Bool := fun u => xor (mixW hk d (mid u) (idx k hk (j.val + 1))) (Q u (idx k hk (j.val + 1)))
    let A2 : B → Bool := fun u => xor (mixW hk d (mid u) (idx k hk (j.val + 2))) (Q u (idx k hk (j.val + 2)))
    have hA1 : IsPoly 1 A1 := hmix_mid_decomp (idx k hk (j.val + 1))
    have hA2 : IsPoly 1 A2 := hmix_mid_decomp (idx k hk (j.val + 2))
    have hmid_j : IsPoly 2 (fun u => mixW hk d (mid u) j) := by
      have : (fun u => mixW hk d (mid u) j) =
          (fun u => xor (xor (mixW hk d (mid u) j) (Q u j)) (Q u j)) := by
        funext u; cases mixW hk d (mid u) j <;> cases Q u j <;> rfl
      rw [this]
      exact isPoly_xor (isPoly_mono (by omega) (hmix_mid_decomp j)) (hQ_poly j)
    have hre : (fun u => xor (outU u j) (Q u (idx k hk (j.val + 1)) && Q u (idx k hk (j.val + 2)))) =
        (fun u =>
          xor (xor (mixW hk d (mid u) j) (xor (xor (rotW hk h base j) (c₂ j)) (rotW hk h (lift u) j)))
            (xor (xor (xor (Q u (idx k hk (j.val + 1)) && A2 u) (A1 u && Q u (idx k hk (j.val + 2))))
              (A1 u && A2 u))
              (xor (Q u (idx k hk (j.val + 2))) (A2 u)))) := by
      funext u
      simp only [outU, stepW, addW, rotW, A1, A2]
      cases mixW hk d (mid u) j <;>
        cases mixW hk d (mid u) (idx k hk (j.val + 1)) <;>
        cases Q u (idx k hk (j.val + 1)) <;>
        cases mixW hk d (mid u) (idx k hk (j.val + 2)) <;>
        cases Q u (idx k hk (j.val + 2)) <;>
        cases base (idx k hk (j.val + k - h % k)) <;>
        cases lift u (idx k hk (j.val + k - h % k)) <;>
        cases c₂ j <;> rfl
    rw [hre]
    apply isPoly_xor
    · exact isPoly_xor (isPoly_mono (by omega) hmid_j)
        (isPoly_mono (by omega) (isPoly_xor (isPoly_mono (by omega) (isPoly_const _)) (hlift_poly h j)))
    · apply isPoly_xor
      · apply isPoly_xor
        · exact isPoly_xor (isPoly_and (d₁ := 2) (d₂ := 1) rfl (hQ_poly _) hA2)
            (isPoly_and (d₁ := 1) (d₂ := 2) rfl hA1 (hQ_poly _))
        · exact isPoly_mono (by omega) (isPoly_and (d₁ := 1) (d₂ := 1) rfl hA1 hA2)
      · exact isPoly_xor (isPoly_mono (by omega) (hQ_poly _)) (isPoly_mono (by omega) hA2)
  let blockJ : Fin blocks → Fin k := fun b =>
    idx k hk (shift + b.val * (4 * d + 5) + k + d - 2)
  have hblockJ_inj : Function.Injective blockJ := by
    intro b1 b2 h
    have hv := congrArg Fin.val h
    dsimp only [blockJ, idx] at hv
    have h1 := primary_lt_k k d b1 0
    have h2 := primary_lt_k k d b2 0
    rw [primaryOff_0, Nat.add_zero] at h1 h2
    have hmod_cancel : ∀ a c : ℕ, a < k → c < k →
        (shift + a + k + d - 2) % k = (shift + c + k + d - 2) % k → a = c := by
      intro a c ha hc heq
      have hre : (shift + a + k + d - 2) % k = (a + (shift + k + d - 2)) % k := by congr 1; omega
      have hre2 : (shift + c + k + d - 2) % k = (c + (shift + k + d - 2)) % k := by congr 1; omega
      rw [hre, hre2] at heq
      have hadd := congrArg (fun z => (z + (k - (shift + k + d - 2) % k)) % k) heq
      rw [Nat.mod_add_mod, Nat.mod_add_mod] at hadd
      have hs := Nat.mod_lt (shift + k + d - 2) hk
      have hstep : ∀ z : ℕ, z < k →
          (z + (shift + k + d - 2) + (k - (shift + k + d - 2) % k)) % k = z := by
        intro z hz
        rw [Nat.add_assoc, Nat.add_mod z, Nat.add_mod (shift + k + d - 2),
          show ((shift + k + d - 2) % k + (k - (shift + k + d - 2) % k) % k) % k = 0 by
            by_cases h0 : (shift + k + d - 2) % k = 0
            · rw [h0, Nat.sub_zero, Nat.mod_self]; simp
            · rw [Nat.mod_eq_of_lt (show k - (shift + k + d - 2) % k < k by omega),
                show (shift + k + d - 2) % k + (k - (shift + k + d - 2) % k) = k by omega,
                Nat.mod_self],
          Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hz]
      rw [hstep a ha, hstep c hc] at hadd
      exact hadd
    have heq_mul := hmod_cancel (b1.val * (4 * d + 5)) (b2.val * (4 * d + 5)) h1 h2 hv
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega : 0 < 4 * d + 5) heq_mul)
  have hQ_prod : ∀ (j : Fin k),
      (∀ b : Fin blocks, blockJ b ≠ j) →
        IsPoly 3 (fun u => Q u (idx k hk (j.val + 1)) && Q u (idx k hk (j.val + 2))) := by
    intro j hnotb
    let j0 : Fin k := idx k hk (j.val + k - shift % k)
    have hshift_back : ∀ m : ℕ, idx k hk ((idx k hk (j.val + m)).val + k - shift % k) =
        idx k hk (j0.val + m) := by
      intro m
      apply Fin.ext
      dsimp only [j0, idx]
      have hs := Nat.mod_lt shift hk
      rw [show (j.val + m) % k + k - shift % k = (j.val + m) % k + (k - shift % k) by omega,
        Nat.mod_add_mod, Nat.mod_add_mod]
      congr 1; omega
    have hterm : ∀ d1 d2 : ℕ, (d1 = 0 ∨ d1 = d ∨ d1 = k - d) → (d2 = 0 ∨ d2 = d ∨ d2 = k - d) →
        IsPoly 3 (fun u => P u (idx k hk ((idx k hk (j.val + 1)).val + d1)) &&
          P u (idx k hk ((idx k hk (j.val + 2)).val + d2))) := by
      intro d1 d2 hd1 hd2
      set s1 := idx k hk (j0.val + 2 + d1)
      set s2 := idx k hk (j0.val + 3 + d1)
      set s3 := idx k hk (j0.val + 3 + d2)
      set s4 := idx k hk (j0.val + 4 + d2)
      have heq_fn : (fun u => P u (idx k hk ((idx k hk (j.val + 1)).val + d1)) &&
          P u (idx k hk ((idx k hk (j.val + 2)).val + d2))) =
          (fun u => (emb0 u s1 && emb0 u s2) && (emb0 u s3 && emb0 u s4)) := by
        funext u
        simp only [P, emb, rotW]
        have hf : ∀ (a b c : ℕ),
            idx k hk ((idx k hk ((idx k hk ((idx k hk (j.val + a)).val + b)).val + c)).val + k - shift % k) =
            idx k hk (j0.val + (a + c) + b) := by
          intro a b c
          have h1 : idx k hk ((idx k hk ((idx k hk (j.val + a)).val + b)).val + c) =
              idx k hk (j.val + (a + b + c)) := by
            apply Fin.ext; dsimp only [idx]
            rw [Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod]; congr 1; omega
          rw [h1, hshift_back (a + b + c)]
          apply Fin.ext; dsimp only [idx]; congr 1; omega
        rw [hf 1 d1 1, hf 1 d1 2, hf 2 d2 1, hf 2 d2 2]
      rw [heq_fn]
      have hemb0_poly : ∀ r : Fin k, IsPoly 1 (fun u => emb0 u r) := fun r =>
        isPoly_linear (fun u => emb0 u r) (fun u₁ u₂ => congrFun (hemb0_lin u₁ u₂) r)
      by_cases hact : isActive k d s1.val ∧ isActive k d s2.val ∧ isActive k d s3.val ∧ isActive k d s4.val
      · by_cases hdist : s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3
        · exfalso
          obtain ⟨_, _, b, hb, _, _, _, _⟩ := quartic_hit_unique k d hk hd hbig j0 d1 d2 hd1 hd2
            s1 s2 s3 s4 rfl rfl rfl rfl hdist.1 hdist.2.1 hdist.2.2 hact.1 hact.2.1 hact.2.2.1 hact.2.2.2
          apply hnotb b
          apply Fin.ext
          dsimp only [blockJ, idx]
          have hjb : (j.val + k - shift % k) % k = (b.val * (4 * d + 5) + k + d - 2) % k := by
            simpa only [j0, idx] using congrArg Fin.val hb
          have hs := Nat.mod_lt shift hk
          have h1 : (shift + b.val * (4 * d + 5) + k + d - 2) % k =
              (shift % k + (b.val * (4 * d + 5) + k + d - 2) % k) % k := by
            rw [Nat.add_mod_mod, Nat.mod_add_mod]; congr 1; omega
          rw [h1, ← hjb, Nat.add_mod_mod,
            show shift % k + (j.val + k - shift % k) = j.val + k by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
        · push_neg at hdist
          by_cases h13 : s1 = s3
          · have hred : (fun u => (emb0 u s1 && emb0 u s2) && (emb0 u s3 && emb0 u s4)) =
                (fun u => (emb0 u s1 && emb0 u s2) && emb0 u s4) := by
              funext u; rw [h13]; cases emb0 u s3 <;> cases emb0 u s2 <;> cases emb0 u s4 <;> rfl
            rw [hred]
            exact isPoly_and (d₁ := 2) (d₂ := 1) rfl
              (isPoly_and (d₁ := 1) (d₂ := 1) rfl (hemb0_poly _) (hemb0_poly _)) (hemb0_poly _)
          · by_cases h14 : s1 = s4
            · have hred : (fun u => (emb0 u s1 && emb0 u s2) && (emb0 u s3 && emb0 u s4)) =
                  (fun u => (emb0 u s1 && emb0 u s2) && emb0 u s3) := by
                funext u; rw [h14]; cases emb0 u s4 <;> cases emb0 u s2 <;> cases emb0 u s3 <;> rfl
              rw [hred]
              exact isPoly_and (d₁ := 2) (d₂ := 1) rfl
                (isPoly_and (d₁ := 1) (d₂ := 1) rfl (hemb0_poly _) (hemb0_poly _)) (hemb0_poly _)
            · have h23 : s2 = s3 := hdist h13 h14
              have hred : (fun u => (emb0 u s1 && emb0 u s2) && (emb0 u s3 && emb0 u s4)) =
                  (fun u => (emb0 u s1 && emb0 u s2) && emb0 u s4) := by
                funext u; rw [h23]; cases emb0 u s1 <;> cases emb0 u s3 <;> cases emb0 u s4 <;> rfl
              rw [hred]
              exact isPoly_and (d₁ := 2) (d₂ := 1) rfl
                (isPoly_and (d₁ := 1) (d₂ := 1) rfl (hemb0_poly _) (hemb0_poly _)) (hemb0_poly _)
      · have hzero : (fun u => (emb0 u s1 && emb0 u s2) && (emb0 u s3 && emb0 u s4)) = fun _ => false := by
          funext u
          dsimp only [emb0]
          by_cases h1 : isActive k d s1.val
          · by_cases h2 : isActive k d s2.val
            · by_cases h3 : isActive k d s3.val
              · have h4 : ¬ isActive k d s4.val := fun h => hact ⟨h1, h2, h3, h⟩
                rw [fold_zero_outside hk hd u s4 h4]; simp
              · rw [fold_zero_outside hk hd u s3 h3]; simp
            · rw [fold_zero_outside hk hd u s2 h2]; simp
          · rw [fold_zero_outside hk hd u s1 h1]; simp
        rw [hzero]
        exact isPoly_mono (by omega) (isPoly_const false)
    have hre : (fun u => Q u (idx k hk (j.val + 1)) && Q u (idx k hk (j.val + 2))) =
        (fun u =>
          xor (xor (xor (P u (idx k hk ((idx k hk (j.val + 1)).val + 0)) && P u (idx k hk ((idx k hk (j.val + 2)).val + 0)))
                        (P u (idx k hk ((idx k hk (j.val + 1)).val + 0)) && P u (idx k hk ((idx k hk (j.val + 2)).val + d))))
                   (P u (idx k hk ((idx k hk (j.val + 1)).val + 0)) && P u (idx k hk ((idx k hk (j.val + 2)).val + (k - d)))))
          (xor (xor (xor (P u (idx k hk ((idx k hk (j.val + 1)).val + d)) && P u (idx k hk ((idx k hk (j.val + 2)).val + 0)))
                        (P u (idx k hk ((idx k hk (j.val + 1)).val + d)) && P u (idx k hk ((idx k hk (j.val + 2)).val + d))))
                   (P u (idx k hk ((idx k hk (j.val + 1)).val + d)) && P u (idx k hk ((idx k hk (j.val + 2)).val + (k - d)))))
               (xor (xor (P u (idx k hk ((idx k hk (j.val + 1)).val + (k - d))) && P u (idx k hk ((idx k hk (j.val + 2)).val + 0)))
                        (P u (idx k hk ((idx k hk (j.val + 1)).val + (k - d))) && P u (idx k hk ((idx k hk (j.val + 2)).val + d))))
                   (P u (idx k hk ((idx k hk (j.val + 1)).val + (k - d))) && P u (idx k hk ((idx k hk (j.val + 2)).val + (k - d))))))) := by
      funext u
      have h0_eq : ∀ r : Fin k, idx k hk (r.val + 0) = r := fun r =>
        Fin.ext (by simp [idx, Nat.mod_eq_of_lt r.isLt])
      have hsub_eq : ∀ r : Fin k, idx k hk (r.val + (k - d)) = idx k hk (r.val + k - d) := fun r =>
        Fin.ext (by simp only [idx]; congr 1; omega)
      simp only [Q, h0_eq, hsub_eq]
      cases P u (idx k hk (j.val + 1)) <;>
        cases P u (idx k hk ((idx k hk (j.val + 1)).val + d)) <;>
        cases P u (idx k hk ((idx k hk (j.val + 1)).val + k - d)) <;>
        cases P u (idx k hk (j.val + 2)) <;>
        cases P u (idx k hk ((idx k hk (j.val + 2)).val + d)) <;>
        cases P u (idx k hk ((idx k hk (j.val + 2)).val + k - d)) <;> rfl
    rw [hre]
    exact isPoly_xor
      (isPoly_xor (isPoly_xor (hterm 0 0 (Or.inl rfl) (Or.inl rfl))
        (hterm 0 d (Or.inl rfl) (Or.inr (Or.inl rfl))))
        (hterm 0 (k - d) (Or.inl rfl) (Or.inr (Or.inr rfl))))
      (isPoly_xor
        (isPoly_xor (isPoly_xor (hterm d 0 (Or.inr (Or.inl rfl)) (Or.inl rfl))
          (hterm d d (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))))
          (hterm d (k - d) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))))
        (isPoly_xor (isPoly_xor (hterm (k - d) 0 (Or.inr (Or.inr rfl)) (Or.inl rfl))
          (hterm (k - d) d (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))))
          (hterm (k - d) (k - d) (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)))))
  have hQ_prod_block : ∀ (b : Fin blocks),
      IsPoly 3 (fun u => xor (Q u (idx k hk ((blockJ b).val + 1)) && Q u (idx k hk ((blockJ b).val + 2)))
        ((List.ofFn (u b)).all id)) := by
    intro b
    set j := blockJ b
    let j0 : Fin k := idx k hk (j.val + k - shift % k)
    have hj0_eq : j0 = idx k hk (b.val * (4 * d + 5) + k + d - 2) := by
      apply Fin.ext
      dsimp only [j0, j, blockJ, idx]
      have hs := Nat.mod_lt shift hk
      have hle : shift % k ≤ shift := Nat.mod_le shift k
      have hsub1 : (shift + b.val * (4 * d + 5) + k + d - 2) % k + k - shift % k =
          (shift + b.val * (4 * d + 5) + k + d - 2) % k + (k - shift % k) := by omega
      have hsub2 : shift + b.val * (4 * d + 5) + k + d - 2 + (k - shift % k) =
          (shift - shift % k) + k + (b.val * (4 * d + 5) + k + d - 2) := by
        generalize b.val * (4 * d + 5) = Bv
        omega
      rw [hsub1, Nat.mod_add_mod, hsub2]
      have hdiv : shift - shift % k = k * (shift / k) := by
        have := Nat.div_add_mod shift k; omega
      rw [hdiv, show k * (shift / k) + k + (b.val * (4 * d + 5) + k + d - 2) =
        k * (shift / k + 1) + (b.val * (4 * d + 5) + k + d - 2) by ring,
        Nat.mul_add_mod]
    have hshift_back : ∀ m : ℕ, idx k hk ((idx k hk (j.val + m)).val + k - shift % k) =
        idx k hk (j0.val + m) := by
      intro m
      apply Fin.ext
      dsimp only [j0, idx]
      have hs := Nat.mod_lt shift hk
      rw [show (j.val + m) % k + k - shift % k = (j.val + m) % k + (k - shift % k) by omega,
        Nat.mod_add_mod, Nat.mod_add_mod]
      congr 1; omega
    have hterm_other : ∀ d1 d2 : ℕ, (d1 = 0 ∨ d1 = d ∨ d1 = k - d) → (d2 = 0 ∨ d2 = d ∨ d2 = k - d) →
        ¬ (d1 = k - d ∧ d2 = d) →
        IsPoly 3 (fun u => P u (idx k hk ((idx k hk (j.val + 1)).val + d1)) &&
          P u (idx k hk ((idx k hk (j.val + 2)).val + d2))) := by
      intro d1 d2 hd1 hd2 hne_pair
      set s1 := idx k hk (j0.val + 2 + d1)
      set s2 := idx k hk (j0.val + 3 + d1)
      set s3 := idx k hk (j0.val + 3 + d2)
      set s4 := idx k hk (j0.val + 4 + d2)
      have heq_fn : (fun u => P u (idx k hk ((idx k hk (j.val + 1)).val + d1)) &&
          P u (idx k hk ((idx k hk (j.val + 2)).val + d2))) =
          (fun u => (emb0 u s1 && emb0 u s2) && (emb0 u s3 && emb0 u s4)) := by
        funext u
        simp only [P, emb, rotW]
        have hf : ∀ (a b' c : ℕ),
            idx k hk ((idx k hk ((idx k hk ((idx k hk (j.val + a)).val + b')).val + c)).val + k - shift % k) =
            idx k hk (j0.val + (a + c) + b') := by
          intro a b' c
          have h1 : idx k hk ((idx k hk ((idx k hk (j.val + a)).val + b')).val + c) =
              idx k hk (j.val + (a + b' + c)) := by
            apply Fin.ext; dsimp only [idx]
            rw [Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod]; congr 1; omega
          rw [h1, hshift_back (a + b' + c)]
          apply Fin.ext; dsimp only [idx]; congr 1; omega
        rw [hf 1 d1 1, hf 1 d1 2, hf 2 d2 1, hf 2 d2 2]
      rw [heq_fn]
      have hemb0_poly : ∀ r : Fin k, IsPoly 1 (fun u => emb0 u r) := fun r =>
        isPoly_linear (fun u => emb0 u r) (fun u₁ u₂ => congrFun (hemb0_lin u₁ u₂) r)
      by_cases hact : isActive k d s1.val ∧ isActive k d s2.val ∧ isActive k d s3.val ∧ isActive k d s4.val
      · by_cases hdist : s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3
        · exfalso
          obtain ⟨hd1', hd2', _, _, _, _, _, _⟩ := quartic_hit_unique k d hk hd hbig j0 d1 d2 hd1 hd2
            s1 s2 s3 s4 rfl rfl rfl rfl hdist.1 hdist.2.1 hdist.2.2 hact.1 hact.2.1 hact.2.2.1 hact.2.2.2
          exact hne_pair ⟨hd1', hd2'⟩
        · push_neg at hdist
          by_cases h13 : s1 = s3
          · have hred : (fun u => (emb0 u s1 && emb0 u s2) && (emb0 u s3 && emb0 u s4)) =
                (fun u => (emb0 u s1 && emb0 u s2) && emb0 u s4) := by
              funext u; rw [h13]; cases emb0 u s3 <;> cases emb0 u s2 <;> cases emb0 u s4 <;> rfl
            rw [hred]
            exact isPoly_and (d₁ := 2) (d₂ := 1) rfl
              (isPoly_and (d₁ := 1) (d₂ := 1) rfl (hemb0_poly _) (hemb0_poly _)) (hemb0_poly _)
          · by_cases h14 : s1 = s4
            · have hred : (fun u => (emb0 u s1 && emb0 u s2) && (emb0 u s3 && emb0 u s4)) =
                  (fun u => (emb0 u s1 && emb0 u s2) && emb0 u s3) := by
                funext u; rw [h14]; cases emb0 u s4 <;> cases emb0 u s2 <;> cases emb0 u s3 <;> rfl
              rw [hred]
              exact isPoly_and (d₁ := 2) (d₂ := 1) rfl
                (isPoly_and (d₁ := 1) (d₂ := 1) rfl (hemb0_poly _) (hemb0_poly _)) (hemb0_poly _)
            · have h23 : s2 = s3 := hdist h13 h14
              have hred : (fun u => (emb0 u s1 && emb0 u s2) && (emb0 u s3 && emb0 u s4)) =
                  (fun u => (emb0 u s1 && emb0 u s2) && emb0 u s4) := by
                funext u; rw [h23]; cases emb0 u s1 <;> cases emb0 u s3 <;> cases emb0 u s4 <;> rfl
              rw [hred]
              exact isPoly_and (d₁ := 2) (d₂ := 1) rfl
                (isPoly_and (d₁ := 1) (d₂ := 1) rfl (hemb0_poly _) (hemb0_poly _)) (hemb0_poly _)
      · have hzero : (fun u => (emb0 u s1 && emb0 u s2) && (emb0 u s3 && emb0 u s4)) = fun _ => false := by
          funext u
          dsimp only [emb0]
          by_cases h1 : isActive k d s1.val
          · by_cases h2 : isActive k d s2.val
            · by_cases h3 : isActive k d s3.val
              · have h4 : ¬ isActive k d s4.val := fun h => hact ⟨h1, h2, h3, h⟩
                rw [fold_zero_outside hk hd u s4 h4]; simp
              · rw [fold_zero_outside hk hd u s3 h3]; simp
            · rw [fold_zero_outside hk hd u s2 h2]; simp
          · rw [fold_zero_outside hk hd u s1 h1]; simp
        rw [hzero]
        exact isPoly_mono (by omega) (isPoly_const false)
    have hmain_eq : (fun u => P u (idx k hk ((idx k hk (j.val + 1)).val + (k - d))) &&
        P u (idx k hk ((idx k hk (j.val + 2)).val + d))) =
        (fun u => (List.ofFn (u b)).all id) := by
      funext u
      simp only [P, emb, rotW]
      have hf : ∀ (a b' c : ℕ),
          idx k hk ((idx k hk ((idx k hk ((idx k hk (j.val + a)).val + b')).val + c)).val + k - shift % k) =
          idx k hk (j0.val + (a + c) + b') := by
        intro a b' c
        have h1 : idx k hk ((idx k hk ((idx k hk (j.val + a)).val + b')).val + c) =
            idx k hk (j.val + (a + b' + c)) := by
          apply Fin.ext; dsimp only [idx]
          rw [Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod]; congr 1; omega
        rw [h1, hshift_back (a + b' + c)]
        apply Fin.ext; dsimp only [idx]; congr 1; omega
      rw [hf 1 (k - d) 1, hf 1 (k - d) 2, hf 2 d 1, hf 2 d 2]
      have hp0 : idx k hk (j0.val + (1 + 1) + (k - d)) = primarySite k d hk b 0 := by
        apply Fin.ext; rw [hj0_eq]; dsimp only [idx, primarySite]; rw [primaryOff_0]
        rw [Nat.add_assoc, Nat.mod_add_mod,
          show b.val * (4 * d + 5) + k + d - 2 + (1 + 1 + (k - d)) =
            b.val * (4 * d + 5) + k * 2 by omega, Nat.add_mul_mod_self_left]
        simp only [Nat.add_zero]
      have hp1 : idx k hk (j0.val + (1 + 2) + (k - d)) = primarySite k d hk b 1 := by
        apply Fin.ext; rw [hj0_eq]; dsimp only [idx, primarySite]; rw [primaryOff_1]
        rw [Nat.add_assoc, Nat.mod_add_mod,
          show b.val * (4 * d + 5) + k + d - 2 + (1 + 2 + (k - d)) =
            (b.val * (4 * d + 5) + 1) + k * 2 by omega, Nat.add_mul_mod_self_left]
      have hp2 : idx k hk (j0.val + (2 + 1) + d) = primarySite k d hk b 2 := by
        apply Fin.ext; rw [hj0_eq]; dsimp only [idx, primarySite]; rw [primaryOff_2]
        rw [Nat.add_assoc, Nat.mod_add_mod,
          show b.val * (4 * d + 5) + k + d - 2 + (2 + 1 + d) =
            (b.val * (4 * d + 5) + (2 * d + 1)) + k by omega, Nat.add_mod_right]
      have hp3 : idx k hk (j0.val + (2 + 2) + d) = primarySite k d hk b 3 := by
        apply Fin.ext; rw [hj0_eq]; dsimp only [idx, primarySite]; rw [primaryOff_3]
        rw [Nat.add_assoc, Nat.mod_add_mod,
          show b.val * (4 * d + 5) + k + d - 2 + (2 + 2 + d) =
            (b.val * (4 * d + 5) + (2 * d + 2)) + k by omega, Nat.add_mod_right]
      dsimp only [emb0]
      rw [hp0, hp1, hp2, hp3,
        fold_at_primary hk hd hbig u b 0, fold_at_primary hk hd hbig u b 1,
        fold_at_primary hk hd hbig u b 2, fold_at_primary hk hd hbig u b 3]
      simp only [List.ofFn_succ, List.ofFn_zero, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      change (u b 0 && u b 1 && (u b 2 && u b 3)) = (u b 0 && (u b 1 && (u b 2 && u b 3)))
      cases u b 0 <;> cases u b 1 <;> cases u b 2 <;> cases u b 3 <;> rfl
    have hre : (fun u => xor (Q u (idx k hk (j.val + 1)) && Q u (idx k hk (j.val + 2)))
          ((List.ofFn (u b)).all id)) =
        (fun u =>
          xor (xor (xor (P u (idx k hk ((idx k hk (j.val + 1)).val + 0)) && P u (idx k hk ((idx k hk (j.val + 2)).val + 0)))
                        (P u (idx k hk ((idx k hk (j.val + 1)).val + 0)) && P u (idx k hk ((idx k hk (j.val + 2)).val + d))))
                   (P u (idx k hk ((idx k hk (j.val + 1)).val + 0)) && P u (idx k hk ((idx k hk (j.val + 2)).val + (k - d)))))
          (xor (xor (xor (P u (idx k hk ((idx k hk (j.val + 1)).val + d)) && P u (idx k hk ((idx k hk (j.val + 2)).val + 0)))
                        (P u (idx k hk ((idx k hk (j.val + 1)).val + d)) && P u (idx k hk ((idx k hk (j.val + 2)).val + d))))
                   (P u (idx k hk ((idx k hk (j.val + 1)).val + d)) && P u (idx k hk ((idx k hk (j.val + 2)).val + (k - d)))))
               (xor (P u (idx k hk ((idx k hk (j.val + 1)).val + (k - d))) && P u (idx k hk ((idx k hk (j.val + 2)).val + 0)))
                   (P u (idx k hk ((idx k hk (j.val + 1)).val + (k - d))) && P u (idx k hk ((idx k hk (j.val + 2)).val + (k - d))))))) := by
      funext u
      rw [← congrFun hmain_eq u]
      have h0_eq : ∀ r : Fin k, idx k hk (r.val + 0) = r := fun r =>
        Fin.ext (by simp [idx, Nat.mod_eq_of_lt r.isLt])
      have hsub_eq : ∀ r : Fin k, idx k hk (r.val + (k - d)) = idx k hk (r.val + k - d) := fun r =>
        Fin.ext (by simp only [idx]; congr 1; omega)
      simp only [Q, h0_eq, hsub_eq]
      cases P u (idx k hk (j.val + 1)) <;>
        cases P u (idx k hk ((idx k hk (j.val + 1)).val + d)) <;>
        cases P u (idx k hk ((idx k hk (j.val + 1)).val + k - d)) <;>
        cases P u (idx k hk (j.val + 2)) <;>
        cases P u (idx k hk ((idx k hk (j.val + 2)).val + d)) <;>
        cases P u (idx k hk ((idx k hk (j.val + 2)).val + k - d)) <;> rfl
    rw [hre]
    exact isPoly_xor
      (isPoly_xor (isPoly_xor (hterm_other 0 0 (Or.inl rfl) (Or.inl rfl) (by omega))
        (hterm_other 0 d (Or.inl rfl) (Or.inr (Or.inl rfl)) (by omega)))
        (hterm_other 0 (k - d) (Or.inl rfl) (Or.inr (Or.inr rfl)) (by omega)))
      (isPoly_xor
        (isPoly_xor (isPoly_xor (hterm_other d 0 (Or.inr (Or.inl rfl)) (Or.inl rfl) (by omega))
          (hterm_other d d (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) (by omega)))
          (hterm_other d (k - d) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (by omega)))
        (isPoly_xor (hterm_other (k - d) 0 (Or.inr (Or.inr rfl)) (Or.inl rfl) (by omega))
          (hterm_other (k - d) (k - d) (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) (by omega))))
  classical
  let targBit : B → Fin k → Bool := fun u j =>
    if h : ∃ b : Fin blocks, blockJ b = j then
      (List.ofFn (u (Classical.choose h))).all id
    else false
  have htarg_eq : ∀ u : B,
      (List.ofFn (fun j : Fin k => mask j && targBit u j)).foldl xor false = target u := by
    intro u
    have h0 := xor_foldl_ofFn_eq_of_inj
      (fun j : Fin k => mask j && targBit u j)
      (fun b : Fin blocks => mask (blockJ b) && (List.ofFn (u b)).all id)
      blockJ hblockJ_inj
      (fun j hnot => by
        have : ¬ ∃ b : Fin blocks, blockJ b = j := fun ⟨b, hb⟩ => hnot b hb
        simp [targBit, this])
      (fun b => by
        have hex : ∃ b' : Fin blocks, blockJ b' = blockJ b := ⟨b, rfl⟩
        have hch : Classical.choose hex = b := hblockJ_inj (Classical.choose_spec hex)
        simp only [targBit, dif_pos hex, hch])
    cases hA : (List.ofFn (fun j : Fin k => mask j && targBit u j)).foldl xor false <;>
      cases hB : target u <;> simp_all [target, blockJ]
  have hres_eq : residual = fun u =>
      (List.ofFn (fun j : Fin k => mask j && xor (outU u j) (targBit u j))).foldl xor false := by
    funext u
    simp only [residual, observed]
    have hobs : (List.ofFn (fun bit : Fin k => mask bit &&
        addW (stepW hk (mixW hk d (addW (stepW hk (mixW hk d (addW (rotW hk s (addW base (lift u))) name)))
          (addW (rotW hk t (addW base (lift u))) c₁))))
          (addW (rotW hk h (addW base (lift u))) c₂) bit)).foldl xor false =
        (List.ofFn (fun j : Fin k => mask j && outU u j)).foldl xor false := by
      congr 2; funext j; dsimp only [outU, mid]; rw [hinit u]
    rw [hobs, ← htarg_eq u, xor_foldl_ofFn_add]
    congr 2
    funext j
    cases mask j <;> cases outU u j <;> cases targBit u j <;> rfl
  rw [hres_eq]
  have hmap : (fun u => (List.ofFn (fun j : Fin k => mask j && xor (outU u j) (targBit u j))).foldl xor false) =
      (fun u => ((List.finRange k).map (fun j => mask j && xor (outU u j) (targBit u j))).foldl xor false) := by
    funext u
    rw [List.ofFn_eq_map]
  rw [hmap]
  apply isPoly_foldl_xor
  intro j _
  apply isPoly_const_and
  by_cases hex : ∃ b : Fin blocks, blockJ b = j
  · obtain ⟨b, rfl⟩ := hex
    have ht_eq : (fun u => targBit u (blockJ b)) = (fun u => (List.ofFn (u b)).all id) := by
      funext u
      have h1 : ∃ b' : Fin blocks, blockJ b' = blockJ b := ⟨b, rfl⟩
      have hch : Classical.choose h1 = b := hblockJ_inj (Classical.choose_spec h1)
      simp only [targBit, dif_pos h1, hch]
    have hsplit : (fun u => xor (outU u (blockJ b)) (targBit u (blockJ b))) =
        (fun u => xor (xor (outU u (blockJ b)) (Q u (idx k hk ((blockJ b).val + 1)) && Q u (idx k hk ((blockJ b).val + 2))))
          (xor (Q u (idx k hk ((blockJ b).val + 1)) && Q u (idx k hk ((blockJ b).val + 2))) ((List.ofFn (u b)).all id))) := by
      funext u
      rw [congrFun ht_eq u]
      cases outU u (blockJ b) <;>
        cases Q u (idx k hk ((blockJ b).val + 1)) <;>
        cases Q u (idx k hk ((blockJ b).val + 2)) <;>
        cases (List.ofFn (u b)).all id <;> rfl
    rw [hsplit]
    exact isPoly_xor (hout_decomp (blockJ b)) (hQ_prod_block b)
  · have ht_eq : (fun u => targBit u j) = fun _ => false := by
      funext u; simp [targBit, hex]
    have hsplit : (fun u => xor (outU u j) (targBit u j)) =
        (fun u => xor (xor (outU u j) (Q u (idx k hk (j.val + 1)) && Q u (idx k hk (j.val + 2))))
          (Q u (idx k hk (j.val + 1)) && Q u (idx k hk (j.val + 2)))) := by
      funext u
      rw [congrFun ht_eq u]
      cases outU u j <;>
        cases Q u (idx k hk (j.val + 1)) <;>
        cases Q u (idx k hk (j.val + 2)) <;> rfl
    rw [hsplit]
    exact isPoly_xor (hout_decomp j) (hQ_prod j (fun b hb => hex ⟨b, hb⟩))

end PEqualNP.Outside.L_meta_25622_aux

theorem PEqualNP.Outside.L_meta_25622 : (∀ (k d : ℕ) (hk : 0 < k), (d = 1 ∨ d = 2) → 4 * d + 4 < k →
  let W := Fin k → Bool
  let idx := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (i : Fin k) => xor (x i) (y i)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (idx (i.val + k - s % k))
  let mix := fun (x : W) (i : Fin k) =>
    xor (xor (x i) (x (idx (i.val + d)))) (x (idx (i.val + k - d)))
  let step := fun (x : W) (i : Fin k) =>
    xor (x i) (!(x (idx (i.val + 1))) && x (idx (i.val + 2)))
  let stride := 4 * d + 5
  let blocks := k / stride
  let B := Fin blocks → Fin 4 → Bool
  let plus := fun (u v : B) (block : Fin blocks) (lane : Fin 4) => xor (u block lane) (v block lane)
  let diff := fun (f : B → Bool) (v x : B) => xor (f x) (f (plus x v))
  ∀ (s shift : ℕ), ∃ lift : B → W, Function.Injective lift ∧
    (∀ x y, lift (plus x y) = add (lift x) (lift y)) ∧
    ∀ (t h : ℕ) (name c₁ c₂ mask base : W),
      let observed := fun (key : W) =>
        let initial := mix (add (rot s key) name)
        let middle := add (step initial) (add (rot t key) c₁)
        let out := add (step (mix middle)) (add (rot h key) c₂)
        (List.ofFn (fun bit : Fin k => mask bit && out bit)).foldl xor false
      let target := fun (input : B) =>
        (List.ofFn (fun b : Fin blocks =>
          mask (idx (shift + b.val * stride + k + d - 2)) &&
          (List.ofFn (input b)).all id)).foldl xor false
      let residual := fun (input : B) => xor (observed (add base (lift input))) (target input)
      ∀ (v : Fin 4 → B) (x : B), (List.ofFn v).foldl diff residual x = false) := by
  intro k d hk hd hbig
  dsimp only
  intro s shift
  exact PEqualNP.Outside.L_meta_25622_aux.main_theorem_core k d hk hd hbig s shift
