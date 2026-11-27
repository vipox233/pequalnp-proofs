import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25623_aux.Grid

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

theorem xor_foldl_ofFn_eq_of_inj {n m : ℕ} (g : Fin n → Bool) (h : Fin m → Bool)
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

theorem main_theorem_core (k d : ℕ) (hk : 0 < k) (hd : d = 1 ∨ d = 2)
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

end PEqualNP.Outside.L_meta_25623_aux.Grid

namespace PEqualNP.Outside.L_meta_25623_aux

namespace RawGrid
abbrev W (k : Nat) := Fin k → Bool
abbrev R (q : Nat) := Fin q → Fin 4 → Bool
def wa {k} (x y : W k) : W k := fun i => xor (x i) (y i)
def ra {q} (x y : R q) : R q := fun i j => xor (x i j) (y i j)
def fd {X : Type*} (a : X→X→X) (f : X→Bool) (v x : X) := xor (f x) (f (a x v))
def target {q} (x : R q) := (List.ofFn (fun i => (List.ofFn (x i)).all id)).foldl xor false
def point {k} (hk : 0<k) (d L : Nat) (r : Fin k) (b : Nat) : Fin k :=
  ⟨(r.val + b*L + k + d - 2)%k,Nat.mod_lt _ hk⟩

theorem shiftGrid {k : Nat} (hk : 0<k) (d L : Nat) (h : 2≤k+d) (mask : W k) :
    let q := k/L
    let w := (Finset.univ.filter (fun i : Fin k => mask i=true)).card
    let p := (q*w+k-1)/k
    ∃ r : Fin k, ∃ (e : Fin p ↪ Fin q), ∀ i, mask (point hk d L r (e i).val)=true := by
  classical
  intro q w p
  let : NeZero k := ⟨hk.ne'⟩
  let I (i : Fin k) := if mask i=true then 1 else 0
  let active (r : Fin k) := Finset.univ.filter (fun j : Fin q => mask (point hk d L r j.val)=true)
  have col (j : Fin q) : (∑ r : Fin k, I (point hk d L r j.val)) = w := by
    let a : Fin k := ⟨(j.val*L+k+d-2)%k,Nat.mod_lt _ hk⟩
    have eqp (r : Fin k) : point hk d L r j.val = r+a := by
      apply Fin.ext
      change (r.val + j.val*L + k + d - 2)%k = (r.val+((j.val*L+k+d-2)%k))%k
      rw [Nat.add_mod_mod]
      congr 1
      omega
    calc
      _ = ∑ r : Fin k, I (r+a) := Finset.sum_congr rfl (fun r _ => congrArg I (eqp r))
      _ = _ := (Equiv.sum_comp (Equiv.addRight a) I).trans (Finset.card_filter _ _).symm
  have total : q*w = ∑ r : Fin k, (active r).card := by
    calc
      _ = ∑ j : Fin q, ∑ r : Fin k, I (point hk d L r j.val) := by simp [col]
      _ = ∑ r : Fin k, ∑ j : Fin q, I (point hk d L r j.val) := Finset.sum_comm
      _ = _ := by simp only [active,Finset.card_filter,I]
  let r0 : Fin k := ⟨0,hk⟩
  obtain ⟨r,_,hr⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k)) (fun a => (active a).card) ⟨r0,by simp⟩
  have le : q*w ≤ k*(active r).card := calc
    _ = _ := total
    _ ≤ ∑ _i : Fin k, (active r).card := Finset.sum_le_sum hr
    _ = _ := by simp
  have enough : p ≤ (active r).card := by
    apply Nat.le_of_lt_succ
    change (q*w+k-1)/k < (active r).card+1
    apply (Nat.div_lt_iff_lt_mul hk).mpr
    rw [Nat.succ_mul,Nat.mul_comm (active r).card k]
    omega
  let e := (active r).orderEmbOfFin rfl
  refine ⟨r,⟨fun i => e (Fin.castLE enough i),?_,⟩,?_⟩
  · intro i j h
    exact Fin.ext (congrArg (fun u : Fin (active r).card => u.val) (e.injective h))
  · intro i
    exact (Finset.mem_filter.mp ((active r).orderEmbOfFin_mem rfl _)).2

noncomputable def pad {p q} (e : Fin p ↪ Fin q) (x : R p) (i : Fin q) : Fin 4→Bool :=
  if h : ∃ j, e j = i then x h.choose else fun _=>false

theorem pad_add {p q} (e : Fin p ↪ Fin q) (x y : R p) :
    pad e (ra x y) = ra (pad e x) (pad e y) := by
  funext i j
  by_cases h : ∃ a, e a=i <;> simp [pad,ra,h]

theorem pad_on {p q} (e : Fin p ↪ Fin q) (x : R p) (i : Fin p) : pad e x (e i) = x i := by
  have h : ∃ j, e j=e i := ⟨i,rfl⟩
  simp only [pad,dite_eq_left h,e.injective h.choose_spec]

theorem target_pad {p q} (e : Fin p ↪ Fin q) (m : Fin q→Bool) (h : ∀ i, m (e i)=true) (x : R p) :
    (List.ofFn fun b => m b && (List.ofFn (pad e x b)).all id).foldl xor false = target x := by
  have he := Grid.xor_foldl_ofFn_eq_of_inj
    (fun b => m b && (List.ofFn (pad e x b)).all id) (fun i => (List.ofFn (x i)).all id)
    e e.injective (by
      intro j hj
      have ne : ¬ ∃ a, e a=j := by rintro ⟨a,ha⟩; exact hj a ha
      simp [pad,ne,List.ofFn_succ]) (by intro i; simp [pad_on,h])
  change xor _ _ = false at he
  exact (show ∀ a b : Bool, xor a b = false → a=b by decide) _ _ he

theorem pull {p q} (e : Fin p ↪ Fin q) (f : R q→Bool) (g : R p→Bool)
    (he : ∀ x, g x = f (pad e x)) (l : List (R p)) (x : R p) :
    l.foldl (fd ra) g x = (l.map (pad e)).foldl (fd ra) f (pad e x) := by
  induction l generalizing f g with
  | nil => exact he x
  | cons a l ih =>
    simp only [List.foldl_cons,List.map_cons]
    apply ih
    intro y
    simp only [fd,he,pad_add]

def idx {k} (hk : 0<k) (n : Nat) : Fin k := ⟨n%k,Nat.mod_lt _ hk⟩
def obs {k} (hk : 0<k) (d s t h : Nat) (name c1 c2 mask key : W k) : Bool :=
  let rot := fun (r : Nat) (x : W k) (i : Fin k) => x (idx hk (i.val+k-r%k))
  let mix := fun (x : W k) (i : Fin k) => xor (xor (x i) (x (idx hk (i.val+d)))) (x (idx hk (i.val+k-d)))
  let step := fun (x : W k) (i : Fin k) => xor (x i) (!(x (idx hk (i.val+1))) && x (idx hk (i.val+2)))
  let initial := mix (wa (rot s key) name)
  let middle := wa (step initial) (wa (rot t key) c1)
  let out := wa (step (mix middle)) (wa (rot h key) c2)
  (List.ofFn (fun bit : Fin k => mask bit && out bit)).foldl xor false

theorem embeddedCube (k d : Nat) (hk : 0<k) (hd : d=1 ∨ d=2) (hw : 4*d+4<k)
    (s t h : Nat) (name c1 c2 mask : W k) :
    let L := 4*d+5
    let w := (Finset.univ.filter (fun i : Fin k => mask i=true)).card
    let p := ((k/L)*w+k-1)/k
    ∃ E : R p → W k, (∀ x y, E (ra x y) = wa (E x) (E y)) ∧
      ∀ base (v : Fin 4 → R p) x, (List.ofFn v).foldl (fd ra)
        (fun u => xor (obs hk d s t h name c1 c2 mask (wa base (E u))) (target u)) x = false := by
  classical
  intro L w p
  obtain ⟨r,e,he⟩ := shiftGrid hk d L (by omega) mask
  obtain ⟨lift,_,hadd,hr⟩ := Grid.main_theorem_core k d hk hd hw s r.val
  refine ⟨fun x => lift (pad e x),?_,?_⟩
  · intro x y; change lift (pad e (ra x y)) = _; rw [pad_add]; exact hadd _ _
  · intro base v x
    let m := fun b : Fin (k/L) => mask (point hk d L r b.val)
    let fullTarget := fun y : R (k/L) => (List.ofFn (fun b=>m b && (List.ofFn (y b)).all id)).foldl xor false
    let run := obs hk d s t h name c1 c2 mask
    let f := fun u => xor (run (wa base (lift u))) (fullTarget u)
    let g := fun u => xor (run (wa base (lift (pad e u)))) (target u)
    have match_ (u) : g u = f (pad e u) :=
      congrArg (xor (run (wa base (lift (pad e u))))) (target_pad e m he u).symm
    have tp := pull e f g match_ (List.ofFn v) x
    rw [List.map_ofFn] at tp
    exact tp.trans (hr t h name c1 c2 mask base (pad e ∘ v) (pad e x))

end RawGrid
end PEqualNP.Outside.L_meta_25623_aux

namespace PEqualNP.Outside.L_meta_25623_aux.BlockBound

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma zmod2_pow_two (k : ℕ) : (2 : ZMod 2) ^ k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero, ite_false]
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_pow (Nat.succ_ne_zero k)]

lemma b2z_foldl_xor {α : Type*} (l : List α) (f : α → Bool) (init : Bool) :
    b2z ((l.map f).foldl xor init) = b2z init + (l.map (fun a => b2z (f a))).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.foldl_cons, List.sum_cons, ih, b2z_xor]
    ring

lemma b2z_foldl_xor_ofFn {m : ℕ} (f : Fin m → Bool) :
    b2z ((List.ofFn f).foldl xor false) = ∑ i : Fin m, b2z (f i) := by
  have h1 : List.ofFn f = (List.finRange m).map f := List.ofFn_eq_map
  rw [h1, b2z_foldl_xor]
  simp only [b2z, Bool.false_eq_true, ite_false, zero_add]
  have h2 : ((List.finRange m).map (fun a => b2z (f a))).sum = ∑ i : Fin m, b2z (f i) := by
    rw [← Fin.sum_univ_def]
  exact h2

lemma b2z_all_id {α : Type*} (l : List α) (f : α → Bool) :
    b2z ((l.map f).all id) = (l.map (fun a => b2z (f a))).prod := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, id_eq, List.prod_cons, b2z_and, ih]

lemma b2z_all_id_ofFn {m : ℕ} (f : Fin m → Bool) :
    b2z ((List.ofFn f).all id) = ∏ i : Fin m, b2z (f i) := by
  have h1 : List.ofFn f = (List.finRange m).map f := List.ofFn_eq_map
  rw [h1, b2z_all_id]
  have h2 : ((List.finRange m).map (fun a => b2z (f a))).prod = ∏ i : Fin m, b2z (f i) := by
    rw [← Fin.prod_univ_def]
  exact h2

def diffZ {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (d x : α) : ZMod 2 :=
  f x + f (x + d)

def foldDiffZ {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (l : List α) : α → ZMod 2 :=
  l.foldl diffZ f

lemma foldDiffZ_nil {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (x : α) :
    foldDiffZ f [] x = f x := rfl

lemma foldDiffZ_cons {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (d : α) (l : List α) (x : α) :
    foldDiffZ f (d :: l) x = foldDiffZ (diffZ f d) l x := rfl

lemma foldDiffZ_add {α : Type*} [AddCommMonoid α] (f g : α → ZMod 2) (l : List α) (x : α) :
    foldDiffZ (fun y => f y + g y) l x = foldDiffZ f l x + foldDiffZ g l x := by
  induction l generalizing f g x with
  | nil => rfl
  | cons d t ih =>
    simp only [foldDiffZ_cons]
    have hfg : diffZ (fun y => f y + g y) d = fun y => diffZ f d y + diffZ g d y := by
      ext y; simp only [diffZ]; ring
    rw [hfg, ih]

lemma foldDiffZ_zero {α : Type*} [AddCommMonoid α] (l : List α) (x : α) :
    foldDiffZ (fun _ => (0 : ZMod 2)) l x = 0 := by
  induction l generalizing x with
  | nil => rfl
  | cons d t ih =>
    simp only [foldDiffZ_cons]
    have h0 : diffZ (fun _ : α => (0 : ZMod 2)) d = fun _ => 0 := by
      ext y; simp only [diffZ, add_zero]
    rw [h0, ih]

lemma foldDiffZ_const_mul {α : Type*} [AddCommMonoid α] (c : ZMod 2) (f : α → ZMod 2)
    (l : List α) (x : α) :
    foldDiffZ (fun y => c * f y) l x = c * foldDiffZ f l x := by
  induction l generalizing f x with
  | nil => rfl
  | cons d t ih =>
    simp only [foldDiffZ_cons]
    have hcf : diffZ (fun y => c * f y) d = fun y => c * diffZ f d y := by
      ext y; simp only [diffZ]; ring
    rw [hcf, ih]

lemma foldDiffZ_sum {α β : Type*} [AddCommMonoid α] (s : Finset β) (f : β → α → ZMod 2)
    (l : List α) (x : α) :
    foldDiffZ (fun y => ∑ b ∈ s, f b y) l x = ∑ b ∈ s, foldDiffZ (f b) l x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact foldDiffZ_zero l x
  | insert a s ha ih =>
    have h1 : (fun y => ∑ b ∈ insert a s, f b y) = fun y => f a y + ∑ b ∈ s, f b y := by
      ext y; exact Finset.sum_insert ha
    rw [h1, foldDiffZ_add, ih, Finset.sum_insert ha]

lemma foldDiffZ_translate {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (a : α)
    (l : List α) (x : α) :
    foldDiffZ (fun y => f (y + a)) l x = foldDiffZ f l (x + a) := by
  induction l generalizing f x with
  | nil => rfl
  | cons d t ih =>
    simp only [foldDiffZ_cons]
    have ht : diffZ (fun y => f (y + a)) d = fun y => diffZ f d (y + a) := by
      ext y; simp only [diffZ, add_right_comm]
    rw [ht, ih]

lemma foldDiffZ_cons_split {α : Type*} [AddCommMonoid α] (f : α → ZMod 2) (d : α)
    (l : List α) (x : α) :
    foldDiffZ f (d :: l) x = foldDiffZ f l x + foldDiffZ f l (x + d) := by
  rw [foldDiffZ_cons]
  have h : diffZ f d = fun y => f y + f (y + d) := rfl
  rw [h, foldDiffZ_add, foldDiffZ_translate]

lemma foldDiffZ_ofFn_eq_sum {α : Type*} [AddCommMonoid α] {m : ℕ} (f : α → ZMod 2)
    (v : Fin m → α) (x : α) :
    foldDiffZ f (List.ofFn v) x = ∑ S : Finset (Fin m), f (x + ∑ i ∈ S, v i) := by
  induction m generalizing x with
  | zero =>
    simp only [List.ofFn_zero, foldDiffZ_nil]
    have hsub : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by
      ext S; simp [Finset.eq_empty_of_isEmpty]
    rw [hsub, Finset.sum_singleton, Finset.sum_empty, add_zero]
  | succ m ih =>
    rw [List.ofFn_succ, foldDiffZ_cons_split, ih, ih]
    have hpart : (Finset.univ : Finset (Finset (Fin (m + 1)))) =
        Finset.univ.image (fun S : Finset (Fin m) => S.map ⟨Fin.succ, Fin.succ_injective m⟩) ∪
        Finset.univ.image (fun S : Finset (Fin m) => insert 0 (S.map ⟨Fin.succ, Fin.succ_injective m⟩)) := by
      ext T
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, true_iff]
      let S : Finset (Fin m) := Finset.univ.filter (fun i => i.succ ∈ T)
      have hmap : S.map ⟨Fin.succ, Fin.succ_injective m⟩ = T.erase 0 := by
        ext j
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk, Finset.mem_erase, S]
        refine Fin.cases ?_ ?_ j
        · simp
        · intro i
          constructor
          · rintro ⟨i', hi', hEq⟩
            have : i' = i := Fin.succ_injective m hEq
            subst this
            exact ⟨Fin.succ_ne_zero _, hi'⟩
          · rintro ⟨_, hi⟩
            exact ⟨i, hi, rfl⟩
      by_cases h0 : (0 : Fin (m + 1)) ∈ T
      · right; refine ⟨S, ?_⟩
        rw [hmap, Finset.insert_erase h0]
      · left; refine ⟨S, ?_⟩
        rw [hmap, Finset.erase_eq_of_notMem h0]
    have hdisj : Disjoint
        (Finset.univ.image (fun S : Finset (Fin m) => S.map ⟨Fin.succ, Fin.succ_injective m⟩))
        (Finset.univ.image (fun S : Finset (Fin m) => insert 0 (S.map ⟨Fin.succ, Fin.succ_injective m⟩))) := by
      rw [Finset.disjoint_left]
      intro T h1 h2
      rcases Finset.mem_image.mp h1 with ⟨S1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨S2, _, hEq⟩
      have h0in : (0 : Fin (m + 1)) ∈ S1.map ⟨Fin.succ, Fin.succ_injective m⟩ := by
        rw [← hEq]; exact Finset.mem_insert_self 0 _
      rcases Finset.mem_map.mp h0in with ⟨i, _, hi⟩
      exact Fin.succ_ne_zero i hi
    rw [hpart, Finset.sum_union hdisj]
    have hinj1 : Function.Injective (fun S : Finset (Fin m) => S.map ⟨Fin.succ, Fin.succ_injective m⟩) := by
      intro S1 S2 h
      ext i
      have hi := Finset.ext_iff.mp h i.succ
      simpa using hi
    have hinj2 : Function.Injective (fun S : Finset (Fin m) => insert 0 (S.map ⟨Fin.succ, Fin.succ_injective m⟩)) := by
      intro S1 S2 h
      ext i
      have hi := Finset.ext_iff.mp h i.succ
      simpa [Fin.succ_ne_zero] using hi
    rw [Finset.sum_image (fun a _ b _ h => hinj1 h), Finset.sum_image (fun a _ b _ h => hinj2 h)]
    congr 1
    · apply Finset.sum_congr rfl; intro S _
      rw [Finset.sum_map]; rfl
    · apply Finset.sum_congr rfl; intro S _
      have h0not : (0 : Fin (m + 1)) ∉ S.map ⟨Fin.succ, Fin.succ_injective m⟩ := by
        simp [Fin.succ_ne_zero]
      rw [Finset.sum_insert h0not, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk]
      rw [← add_assoc]

lemma foldDiffZ_comp_addHom {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    (φ : α → β) (hφ : ∀ a b, φ (a + b) = φ a + φ b) (f : β → ZMod 2)
    (l : List α) (x : α) :
    foldDiffZ (fun a => f (φ a)) l x = foldDiffZ f (l.map φ) (φ x) := by
  induction l generalizing f x with
  | nil => rfl
  | cons d t ih =>
    simp only [List.map_cons, foldDiffZ_cons]
    have hd : diffZ (fun a => f (φ a)) d = fun a => diffZ f (φ d) (φ a) := by
      ext a; simp only [diffZ, hφ]
    rw [hd, ih]

lemma foldDiffZ_comp_affine {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
    (x0 : β) (φ : α → β) (hφ : ∀ a b, φ (a + b) = φ a + φ b) (f : β → ZMod 2)
    (l : List α) (x : α) :
    foldDiffZ (fun a => f (x0 + φ a)) l x = foldDiffZ f (l.map φ) (x0 + φ x) := by
  have h1 := foldDiffZ_comp_addHom φ hφ (fun b => f (x0 + b)) l x
  have h2 : (fun b => f (x0 + b)) = (fun b => f (b + x0)) := by ext b; rw [add_comm]
  rw [h1, h2, foldDiffZ_translate, add_comm]

def monom {ι : Type*} (S : Finset ι) (x : ι → ZMod 2) : ZMod 2 :=
  ∏ i ∈ S, x i

def ind {ι : Type*} [DecidableEq ι] (T : Finset ι) : ι → ZMod 2 :=
  fun i => if i ∈ T then 1 else 0

lemma eq_ind_supp {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ZMod 2) :
    x = ind (Finset.univ.filter (fun i => x i = 1)) := by
  ext i
  simp only [ind, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases zmod2_cases (x i) with h | h <;> simp [h]

lemma monom_ind {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    monom S (ind T) = if S ⊆ T then 1 else 0 := by
  by_cases hST : S ⊆ T
  · simp only [hST, ite_true, monom, ind]
    apply Finset.prod_eq_one
    intro i hi
    simp only [hST hi, ite_true]
  · simp only [hST, ite_false, monom, ind]
    rw [Finset.not_subset] at hST
    rcases hST with ⟨i, hiS, hiT⟩
    exact Finset.prod_eq_zero hiS (by simp [hiT])

def anf {ι : Type*} [DecidableEq ι] (f : (ι → ZMod 2) → ZMod 2) (S : Finset ι) : ZMod 2 :=
  ∑ T ∈ S.powerset, f (ind T)

lemma anf_add {ι : Type*} [DecidableEq ι] (f g : (ι → ZMod 2) → ZMod 2) (S : Finset ι) :
    anf (fun x => f x + g x) S = anf f S + anf g S := by
  unfold anf
  exact Finset.sum_add_distrib

lemma sum_powerset_between {ι : Type*} [DecidableEq ι] (U X : Finset ι) (hUX : U ⊆ X) :
    (∑ _S ∈ X.powerset.filter (fun S => U ⊆ S), (1 : ZMod 2)) = if U = X then 1 else 0 := by
  have hbij : (X.powerset.filter (fun S => U ⊆ S)).card = (X \ U).powerset.card := by
    refine Finset.card_bij (fun S _ => S \ U) ?_ ?_ ?_
    · intro S hS
      rcases Finset.mem_filter.mp hS with ⟨hSX, _⟩
      exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff (Finset.mem_powerset.mp hSX) le_rfl)
    · intro S1 hS1 S2 hS2 hEq
      have hU1 := (Finset.mem_filter.mp hS1).2
      have hU2 := (Finset.mem_filter.mp hS2).2
      rw [← Finset.sdiff_union_of_subset hU1, ← Finset.sdiff_union_of_subset hU2, hEq]
    · intro R hR
      have hRXU : R ⊆ X \ U := Finset.mem_powerset.mp hR
      refine ⟨R ∪ U, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.subset_union_right⟩, ?_⟩
      · exact Finset.union_subset (hRXU.trans Finset.sdiff_subset) hUX
      · rw [Finset.union_sdiff_cancel_right]
        exact Finset.disjoint_of_subset_left hRXU disjoint_sdiff_self_left
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hbij, Finset.card_powerset]
  have h2 : ((2 ^ (X \ U).card : ℕ) : ZMod 2) = (2 : ZMod 2) ^ (X \ U).card := by push_cast; rfl
  rw [h2, zmod2_pow_two]
  have heq : (X \ U).card = 0 ↔ U = X := by
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h => Finset.Subset.antisymm hUX h, fun h => h ▸ le_rfl⟩
  by_cases h : U = X
  · simp [h]
  · have hne : (X \ U).card ≠ 0 := mt heq.mp h
    simp [h, hne]

lemma anf_eval {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ZMod 2) → ZMod 2)
    (x : ι → ZMod 2) :
    f x = ∑ S : Finset ι, anf f S * monom S x := by
  let X := Finset.univ.filter (fun i => x i = 1)
  have hx : x = ind X := eq_ind_supp x
  rw [hx]
  have h1 : (∑ S : Finset ι, anf f S * monom S (ind X)) = ∑ S ∈ X.powerset, anf f S := by
    simp only [monom_ind, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    congr 1; ext S; simp [Finset.mem_powerset]
  rw [h1]
  unfold anf
  have hswap : (∑ S ∈ X.powerset, ∑ T ∈ S.powerset, f (ind T)) =
      ∑ T ∈ X.powerset, f (ind T) * ∑ S ∈ X.powerset.filter (fun S => T ⊆ S), (1 : ZMod 2) := by
    calc ∑ S ∈ X.powerset, ∑ T ∈ S.powerset, f (ind T)
        = ∑ S ∈ X.powerset, ∑ T ∈ X.powerset, (if T ⊆ S then f (ind T) else 0) := by
          apply Finset.sum_congr rfl; intro S hS
          rw [← Finset.sum_filter]
          congr 1; ext T
          simp only [Finset.mem_powerset, Finset.mem_filter]
          exact ⟨fun hTS => ⟨hTS.trans (Finset.mem_powerset.mp hS), hTS⟩, fun h => h.2⟩
      _ = ∑ T ∈ X.powerset, ∑ S ∈ X.powerset, (if T ⊆ S then f (ind T) else 0) := Finset.sum_comm
      _ = ∑ T ∈ X.powerset, f (ind T) * ∑ S ∈ X.powerset.filter (fun S => T ⊆ S), (1 : ZMod 2) := by
          apply Finset.sum_congr rfl; intro T _
          rw [← Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro S _; ring
  rw [hswap]
  have hcollapse : (∑ T ∈ X.powerset, f (ind T) * ∑ S ∈ X.powerset.filter (fun S => T ⊆ S), (1 : ZMod 2)) =
      ∑ T ∈ X.powerset, if T = X then f (ind T) else 0 := by
    apply Finset.sum_congr rfl; intro T hT
    rw [sum_powerset_between T X (Finset.mem_powerset.mp hT)]
    by_cases hTX : T = X <;> simp [hTX]
  rw [hcollapse, Finset.sum_ite_eq']
  simp

lemma anf_unique {ι : Type*} [Fintype ι] [DecidableEq ι] (c : Finset ι → ZMod 2) (S : Finset ι) :
    anf (fun x => ∑ U : Finset ι, c U * monom U x) S = c S := by
  unfold anf
  have h1 : (∑ T ∈ S.powerset, ∑ U : Finset ι, c U * monom U (ind T)) =
      ∑ T ∈ S.powerset, ∑ U ∈ T.powerset, c U := by
    apply Finset.sum_congr rfl; intro T _
    simp only [monom_ind, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    congr 1; ext U; simp [Finset.mem_powerset]
  rw [h1]
  have hswap : (∑ T ∈ S.powerset, ∑ U ∈ T.powerset, c U) =
      ∑ U ∈ S.powerset, c U * ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (1 : ZMod 2) := by
    calc ∑ T ∈ S.powerset, ∑ U ∈ T.powerset, c U
        = ∑ T ∈ S.powerset, ∑ U ∈ S.powerset, (if U ⊆ T then c U else 0) := by
          apply Finset.sum_congr rfl; intro T hT
          rw [← Finset.sum_filter]
          congr 1; ext U
          simp only [Finset.mem_powerset, Finset.mem_filter]
          exact ⟨fun hUT => ⟨hUT.trans (Finset.mem_powerset.mp hT), hUT⟩, fun h => h.2⟩
      _ = ∑ U ∈ S.powerset, ∑ T ∈ S.powerset, (if U ⊆ T then c U else 0) := Finset.sum_comm
      _ = ∑ U ∈ S.powerset, c U * ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (1 : ZMod 2) := by
          apply Finset.sum_congr rfl; intro U _
          rw [← Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro T _; ring
  rw [hswap]
  have hcollapse : (∑ U ∈ S.powerset, c U * ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), (1 : ZMod 2)) =
      ∑ U ∈ S.powerset, if U = S then c U else 0 := by
    apply Finset.sum_congr rfl; intro U hU
    rw [sum_powerset_between U S (Finset.mem_powerset.mp hU)]
    by_cases hUS : U = S <;> simp [hUS]
  rw [hcollapse, Finset.sum_ite_eq']
  simp

lemma anf_eq_zero_of_foldDiffZ_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (f : (ι → ZMod 2) → ZMod 2)
    (hf : ∀ (v : Fin r → (ι → ZMod 2)) (x : ι → ZMod 2), foldDiffZ f (List.ofFn v) x = 0) :
    ∀ T : Finset ι, r ≤ T.card → anf f T = 0 := by
  intro T hTr
  induction hn : T.card using Nat.strong_induction_on generalizing T with
  | ind n ih =>
    subst hn
    rcases Finset.exists_subset_card_eq hTr with ⟨A, hAT, hAcard⟩
    let eA : Fin r ≃ A := (Finset.equivFinOfCardEq hAcard).symm
    let s : Fin r → ι := fun t => (eA t).1
    have hs_inj : Function.Injective s := fun t1 t2 h => eA.injective (Subtype.ext h)
    let v : Fin r → (ι → ZMod 2) := fun t => ind {s t}
    have hv_zero := hf v (ind (T \ A))
    rw [foldDiffZ_ofFn_eq_sum] at hv_zero
    have hsum_vec : ∀ U : Finset (Fin r),
        ind (T \ A) + ∑ t ∈ U, v t = ind ((T \ A) ∪ U.image s) := by
      intro U
      ext i
      simp only [Pi.add_apply, Finset.sum_apply, ind, v, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_image, Finset.mem_singleton]
      have hUsum : (∑ t ∈ U, (if i = s t then (1 : ZMod 2) else 0)) =
          if ∃ t ∈ U, s t = i then 1 else 0 := by
        by_cases h : ∃ t ∈ U, s t = i
        · simp only [h, ite_true]
          rcases h with ⟨t0, ht0U, ht0Eq⟩
          rw [Finset.sum_eq_single t0]
          · simp [ht0Eq]
          · intro t _ hne
            have : i ≠ s t := fun heq => hne (hs_inj (heq.symm.trans ht0Eq.symm))
            simp [this]
          · intro hnot; exact absurd ht0U hnot
        · simp only [h, ite_false]
          apply Finset.sum_eq_zero; intro t ht
          have : i ≠ s t := fun heq => h ⟨t, ht, heq.symm⟩
          simp [this]
      rw [hUsum]
      by_cases hiTA : i ∈ T ∧ i ∉ A
      · have hnotU : ¬ ∃ t ∈ U, s t = i := by
          rintro ⟨t, _, rfl⟩
          exact hiTA.2 (eA t).2
        simp [hiTA, hnotU]
      · by_cases hU : ∃ t ∈ U, s t = i
        · simp [hiTA, hU]
        · simp [hiTA, hU]
    have hbij : (∑ U : Finset (Fin r), f (ind (T \ A) + ∑ t ∈ U, v t)) =
        ∑ Y ∈ T.powerset.filter (fun Y => T \ A ⊆ Y), f (ind Y) := by
      simp_rw [hsum_vec]
      refine Finset.sum_bij (fun U _ => (T \ A) ∪ U.image s) ?_ ?_ ?_ ?_
      · intro U _
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.subset_union_left⟩
        refine Finset.union_subset Finset.sdiff_subset ?_
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨t, _, rfl⟩
        exact hAT (eA t).2
      · intro U1 _ U2 _ hEq
        ext t
        have hm := Finset.ext_iff.mp hEq (s t)
        have hnotTA : s t ∉ T \ A := by
          simp only [Finset.mem_sdiff, not_and, not_not]
          intro _; exact (eA t).2
        simp only [Finset.mem_union, hnotTA, false_or, Finset.mem_image] at hm
        constructor
        · intro ht
          rcases hm.mp ⟨t, ht, rfl⟩ with ⟨t', ht', heq⟩
          exact hs_inj heq ▸ ht'
        · intro ht
          rcases hm.mpr ⟨t, ht, rfl⟩ with ⟨t', ht', heq⟩
          exact hs_inj heq ▸ ht'
      · intro Y hY
        rcases Finset.mem_filter.mp hY with ⟨hYT, hTAY⟩
        have hYT' : Y ⊆ T := Finset.mem_powerset.mp hYT
        refine ⟨Finset.univ.filter (fun t => s t ∈ Y), Finset.mem_univ _, ?_⟩
        ext i
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · rintro (⟨hiT, hiA⟩ | ⟨t, htY, rfl⟩)
          · exact hTAY (Finset.mem_sdiff.mpr ⟨hiT, hiA⟩)
          · exact htY
        · intro hiY
          by_cases hiA : i ∈ A
          · right
            refine ⟨eA.symm ⟨i, hiA⟩, ?_, ?_⟩
            · have : s (eA.symm ⟨i, hiA⟩) = i := by simp [s]
              rw [this]; exact hiY
            · simp [s]
          · left; exact ⟨hYT' hiY, hiA⟩
      · intro U _; rfl
    rw [hbij] at hv_zero
    have hexpand : (∑ Y ∈ T.powerset.filter (fun Y => T \ A ⊆ Y), f (ind Y)) =
        ∑ M ∈ T.powerset.filter (fun M => A ⊆ M), anf f M := by
      have h1 : ∀ Y ∈ T.powerset.filter (fun Y => T \ A ⊆ Y),
          f (ind Y) = ∑ M ∈ T.powerset, if M ⊆ Y then anf f M else 0 := by
        intro Y hY
        have hYT : Y ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hY).1
        rw [anf_eval f (ind Y)]
        simp only [monom_ind, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
        congr 1; ext M
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
        exact ⟨fun hMY => ⟨hMY.trans hYT, hMY⟩, fun h => h.2⟩
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      have h2 : ∀ M ∈ T.powerset,
          (∑ Y ∈ T.powerset.filter (fun Y => T \ A ⊆ Y), if M ⊆ Y then anf f M else 0) =
          if A ⊆ M then anf f M else 0 := by
        intro M hM
        have hMT : M ⊆ T := Finset.mem_powerset.mp hM
        have hfilt : (T.powerset.filter (fun Y => T \ A ⊆ Y)).filter (fun Y => M ⊆ Y) =
            T.powerset.filter (fun Y => (T \ A) ∪ M ⊆ Y) := by
          ext Y; simp only [Finset.mem_filter, Finset.union_subset_iff]; tauto
        rw [← Finset.sum_filter, hfilt]
        have hpull : (∑ Y ∈ T.powerset.filter (fun Y => (T \ A) ∪ M ⊆ Y), anf f M) =
            anf f M * ∑ Y ∈ T.powerset.filter (fun Y => (T \ A) ∪ M ⊆ Y), (1 : ZMod 2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
        rw [hpull, sum_powerset_between ((T \ A) ∪ M) T (Finset.union_subset Finset.sdiff_subset hMT)]
        have heq : (T \ A) ∪ M = T ↔ A ⊆ M := by
          constructor
          · intro h i hiA
            have hiT : i ∈ T := hAT hiA
            rw [← h] at hiT
            rcases Finset.mem_union.mp hiT with h1 | h2
            · exact absurd hiA (Finset.mem_sdiff.mp h1).2
            · exact h2
          · intro hAM
            ext i
            simp only [Finset.mem_union, Finset.mem_sdiff]
            constructor
            · rintro (⟨hiT, _⟩ | hiM)
              · exact hiT
              · exact hMT hiM
            · intro hiT
              by_cases hiA : i ∈ A
              · right; exact hAM hiA
              · left; exact ⟨hiT, hiA⟩
        by_cases hAM : A ⊆ M
        · simp [hAM, heq.mpr hAM]
        · have hne : (T \ A) ∪ M ≠ T := mt heq.mp hAM
          simp [hAM, hne]
      rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]
    rw [hexpand] at hv_zero
    have hTmem : T ∈ T.powerset.filter (fun M => A ⊆ M) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr le_rfl, hAT⟩
    rw [← Finset.add_sum_erase _ _ hTmem] at hv_zero
    have hrest : ∑ M ∈ (T.powerset.filter (fun M => A ⊆ M)).erase T, anf f M = 0 := by
      apply Finset.sum_eq_zero; intro M hM
      have hne : M ≠ T := (Finset.mem_erase.mp hM).1
      rcases Finset.mem_filter.mp (Finset.mem_erase.mp hM).2 with ⟨hMT, hAM⟩
      have hMsub : M ⊂ T := ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hMT, hne⟩
      have hMlt : M.card < T.card := Finset.card_lt_card hMsub
      have hMr : r ≤ M.card := hAcard ▸ Finset.card_le_card hAM
      exact ih M.card hMlt M hMr rfl
    rw [hrest, add_zero] at hv_zero
    exact hv_zero

lemma diffZ_monom {ι : Type*} [DecidableEq ι] (S : Finset ι) (d x : ι → ZMod 2) :
    diffZ (monom S) d x =
      ∑ T ∈ S.powerset.erase S, (∏ i ∈ S \ T, d i) * monom T x := by
  unfold diffZ monom
  simp only [Pi.add_apply]
  have hprod : (∏ i ∈ S, (x i + d i)) =
      ∑ T ∈ S.powerset, (∏ i ∈ T, x i) * (∏ i ∈ S \ T, d i) := by
    rw [Finset.prod_add]
  rw [hprod, ← Finset.add_sum_erase _ _ (Finset.mem_powerset.mpr le_rfl)]
  have hself : (∏ i ∈ S, x i) * (∏ i ∈ S \ S, d i) = ∏ i ∈ S, x i := by simp
  rw [hself]
  have hcancel : (∏ i ∈ S, x i) + ((∏ i ∈ S, x i) +
      ∑ T ∈ S.powerset.erase S, (∏ i ∈ T, x i) * (∏ i ∈ S \ T, d i)) =
      ∑ T ∈ S.powerset.erase S, (∏ i ∈ T, x i) * (∏ i ∈ S \ T, d i) := by
    have h2 : (∏ i ∈ S, x i) + (∏ i ∈ S, x i) = (2 : ZMod 2) * (∏ i ∈ S, x i) := by ring
    have hz : (2 : ZMod 2) = 0 := by decide
    rw [← add_assoc, h2, hz, zero_mul, zero_add]
  rw [hcancel]
  apply Finset.sum_congr rfl; intro T _; ring

lemma foldDiffZ_monom_eq_zero {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (l : List (ι → ZMod 2)) (hcard : S.card < l.length) (x : ι → ZMod 2) :
    foldDiffZ (monom S) l x = 0 := by
  induction l generalizing S x with
  | nil => simp at hcard
  | cons d t ih =>
    rw [foldDiffZ_cons]
    have hdiff : diffZ (monom S) d = fun y => ∑ T ∈ S.powerset.erase S, (∏ i ∈ S \ T, d i) * monom T y := by
      ext y; exact diffZ_monom S d y
    rw [hdiff, foldDiffZ_sum]
    apply Finset.sum_eq_zero; intro T hT
    rw [foldDiffZ_const_mul]
    have hTsub : T ⊂ S := ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp hT).2, (Finset.mem_erase.mp hT).1⟩
    have hTlt : T.card < t.length := by
      have h1 := Finset.card_lt_card hTsub
      simp only [List.length_cons] at hcard
      omega
    rw [ih T hTlt x, mul_zero]

lemma foldDiffZ_monom_const {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (l : List (ι → ZMod 2)) (hcard : S.card = l.length) (x y : ι → ZMod 2) :
    foldDiffZ (monom S) l x = foldDiffZ (monom S) l y := by
  induction l generalizing S x y with
  | nil =>
    simp only [List.length_nil, Finset.card_eq_zero] at hcard
    subst hcard
    rfl
  | cons d t ih =>
    rw [foldDiffZ_cons, foldDiffZ_cons]
    have hdiff : diffZ (monom S) d = fun z => ∑ T ∈ S.powerset.erase S, (∏ i ∈ S \ T, d i) * monom T z := by
      ext z; exact diffZ_monom S d z
    rw [hdiff, foldDiffZ_sum, foldDiffZ_sum]
    apply Finset.sum_congr rfl; intro T hT
    rw [foldDiffZ_const_mul, foldDiffZ_const_mul]
    have hTsub : T ⊂ S := ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp hT).2, (Finset.mem_erase.mp hT).1⟩
    have hTle : T.card ≤ t.length := by
      have h1 := Finset.card_lt_card hTsub
      simp only [List.length_cons] at hcard
      omega
    rcases lt_or_eq_of_le hTle with hlt | heq
    · rw [foldDiffZ_monom_eq_zero T t hlt x, foldDiffZ_monom_eq_zero T t hlt y]
    · rw [ih T heq x y]

def zSign (a : ZMod 2) : ℤ := if a = 1 then -1 else 1

lemma zSign_add (a b : ZMod 2) : zSign (a + b) = zSign a * zSign b := by
  fin_cases a <;> fin_cases b <;> decide

lemma zSign_sum {α : Type*} (s : Finset α) (g : α → ZMod 2) :
    zSign (∑ a ∈ s, g a) = ∏ a ∈ s, zSign (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zSign]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, zSign_add, ih]

lemma card_filter_ones {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Finset ι) :
    ((Finset.univ : Finset (ι → ZMod 2)).filter (fun x => ∀ i ∈ U, x i = 1)).card =
      2 ^ (Fintype.card ι - U.card) := by
  let e : {x : ι → ZMod 2 // ∀ i ∈ U, x i = 1} ≃ ({i : ι // i ∉ U} → ZMod 2) :=
    { toFun := fun x i => x.1 i.1
      invFun := fun y => ⟨fun i => if h : i ∈ U then 1 else y ⟨i, h⟩, fun i hi => by simp [hi]⟩
      left_inv := fun x => by
        ext i
        by_cases h : i ∈ U
        · simp [h, x.2 i h]
        · simp [h]
      right_inv := fun y => by
        ext i
        simp [i.2] }
  have h1 : ((Finset.univ : Finset (ι → ZMod 2)).filter (fun x => ∀ i ∈ U, x i = 1)).card =
      Fintype.card {x : ι → ZMod 2 // ∀ i ∈ U, x i = 1} := by
    rw [Fintype.card_subtype]
  rw [h1, Fintype.card_congr e, Fintype.card_fun, ZMod.card]
  have hcompl : Fintype.card {i : ι // i ∉ U} = Fintype.card ι - U.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hcompl]

lemma signed_sum_anf {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ZMod 2) → ZMod 2) :
    let supp := Finset.univ.filter (fun S : Finset ι => anf f S = 1)
    (∑ x : ι → ZMod 2, zSign (f x)) =
      ∑ A ∈ supp.powerset, (-2 : ℤ) ^ A.card * (2 : ℤ) ^ (Fintype.card ι - (A.biUnion id).card) := by
  intro supp
  have hfx : ∀ x : ι → ZMod 2, f x = ∑ S ∈ supp, monom S x := by
    intro x
    rw [anf_eval f x]
    have h0 : ∀ S : Finset ι, anf f S * monom S x = if anf f S = 1 then monom S x else 0 := by
      intro S
      rcases zmod2_cases (anf f S) with h | h <;> simp [h]
    simp_rw [h0, ← Finset.sum_filter]
    rfl
  have hterm : ∀ x : ι → ZMod 2, zSign (f x) =
      ∑ A ∈ supp.powerset, (-2 : ℤ) ^ A.card *
        (if ∀ i ∈ A.biUnion id, x i = 1 then (1 : ℤ) else 0) := by
    intro x
    rw [hfx x, zSign_sum]
    have hfactor : ∀ S ∈ supp, zSign (monom S x) =
        (if monom S x = 1 then (-2 : ℤ) else 0) + 1 := by
      intro S _
      unfold zSign
      by_cases h : monom S x = 1 <;> simp [h]
    rw [Finset.prod_congr rfl hfactor, Finset.prod_add]
    apply Finset.sum_congr rfl; intro A _
    simp only [Finset.prod_const_one, mul_one]
    have hprod_eq : (∏ S ∈ A, if monom S x = 1 then (-2 : ℤ) else 0) =
        (-2 : ℤ) ^ A.card * (if ∀ i ∈ A.biUnion id, x i = 1 then (1 : ℤ) else 0) := by
      have hall : (∀ S ∈ A, monom S x = 1) ↔ (∀ i ∈ A.biUnion id, x i = 1) := by
        constructor
        · intro h i hi
          rcases Finset.mem_biUnion.mp hi with ⟨S, hSA, hiS⟩
          have hm := h S hSA
          rcases zmod2_cases (x i) with h0 | h1
          · exfalso
            have : monom S x = 0 := Finset.prod_eq_zero hiS h0
            rw [this] at hm
            exact absurd hm (by decide)
          · exact h1
        · intro h S hSA
          unfold monom
          apply Finset.prod_eq_one; intro i hiS
          exact h i (Finset.mem_biUnion.mpr ⟨S, hSA, hiS⟩)
      by_cases hA : ∀ S ∈ A, monom S x = 1
      · have hU := hall.mp hA
        have hite : (if ∀ i ∈ A.biUnion id, x i = 1 then (1 : ℤ) else 0) = 1 := by
          split_ifs
          rfl
        rw [hite, mul_one]
        calc ∏ S ∈ A, (if monom S x = 1 then (-2 : ℤ) else 0)
            = ∏ _S ∈ A, (-2 : ℤ) := Finset.prod_congr rfl (fun S hS => by simp [hA S hS])
          _ = (-2 : ℤ) ^ A.card := Finset.prod_const (-2 : ℤ)
      · have hU : ¬ ∀ i ∈ A.biUnion id, x i = 1 := mt hall.mpr hA
        have hite : (if ∀ i ∈ A.biUnion id, x i = 1 then (1 : ℤ) else 0) = 0 := by
          split_ifs
          rfl
        rw [hite, mul_zero]
        push Not at hA
        rcases hA with ⟨S, hSA, hSne⟩
        exact Finset.prod_eq_zero hSA (by simp [hSne])
    exact hprod_eq
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro A _
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_filter_ones]
  push_cast; rfl

lemma pow_two_dvd_term (p a b : ℕ) (h : p + 1 ≤ a + b) :
    (2 : ℤ) ^ (p + 1) ∣ (-2 : ℤ) ^ a * (2 : ℤ) ^ b := by
  have heq : (-2 : ℤ) ^ a * (2 : ℤ) ^ b = (-1 : ℤ) ^ a * (2 : ℤ) ^ (a + b) := by
    have : (-2 : ℤ) = (-1 : ℤ) * 2 := by ring
    rw [this, mul_pow, mul_assoc, ← pow_add]
  rw [heq]
  have hdvd : (2 : ℤ) ^ (p + 1) ∣ (2 : ℤ) ^ (a + b) := pow_dvd_pow (2 : ℤ) h
  exact dvd_mul_of_dvd_right hdvd _

lemma signed_sum_dvd_of_deg_lt {ι : Type*} [Fintype ι] [DecidableEq ι] (p r : ℕ)
    (hr : 2 ≤ r) (f : (ι → ZMod 2) → ZMod 2)
    (hdeg : ∀ S : Finset ι, r ≤ S.card → anf f S = 0)
    (hdim : p * (r - 1) < Fintype.card ι) :
    (2 : ℤ) ^ (p + 1) ∣ ∑ x : ι → ZMod 2, zSign (f x) := by
  rw [signed_sum_anf f]
  apply Finset.dvd_sum
  intro A hA
  apply pow_two_dvd_term
  have hsub : ∀ S ∈ A, S.card ≤ r - 1 := by
    intro S hSA
    have hSsupp := Finset.mem_powerset.mp hA hSA
    have h1 : anf f S = 1 := (Finset.mem_filter.mp hSsupp).2
    by_contra hge
    push Not at hge
    have hSr : r ≤ S.card := by omega
    rw [hdeg S hSr] at h1
    exact absurd h1 (by decide)
  have hu_le_n : (A.biUnion id).card ≤ Fintype.card ι := Finset.card_le_univ _
  have hu_le_tr : (A.biUnion id).card ≤ A.card * (r - 1) := by
    calc (A.biUnion id).card
        ≤ ∑ S ∈ A, S.card := Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ A, (r - 1) := Finset.sum_le_sum hsub
      _ = A.card * (r - 1) := by simp
  by_cases htp : p + 1 ≤ A.card
  · omega
  · have hle : A.card ≤ p := by omega
    have hmul : A.card * (r - 2) ≤ p * (r - 2) := Nat.mul_le_mul_right (r - 2) hle
    have h1 : A.card * (r - 1) = A.card + A.card * (r - 2) := by
      have : r - 1 = 1 + (r - 2) := by omega
      rw [this, mul_add, mul_one]
    have h2 : p * (r - 1) = p + p * (r - 2) := by
      have : r - 1 = 1 + (r - 2) := by omega
      rw [this, mul_add, mul_one]
    omega

theorem blockQueryLowerBound :
    ∀ (p r : ℕ), 0 < p → 2 ≤ r →
      let W := Fin p → Fin r → Bool
      let add := fun (x y : W) (row : Fin p) (col : Fin r) => xor (x row col) (y row col)
      let diff := fun (f : W → Bool) (direction point : W) =>
        xor (f point) (f (add point direction))
      let top := fun (f : W → Bool) (v : Fin r → W) => (List.ofFn v).foldl diff f
      let blocks := fun (word : W) =>
        (List.ofFn (fun block : Fin p => (List.ofFn (word block)).all id)).foldl xor false
      ∀ (lower : W → Bool), (∀ v x, top lower v x = false) →
        let observed := fun (input : W) => xor (blocks input) (lower input)
        let linear := fun (n : ℕ) (q : W → Fin n → Bool) =>
          ∀ x y i, q (add x y) i = xor (q x i) (q y i)
        let drops := fun (n : ℕ) (q : W → Fin n → Bool) (base : W) =>
          ∀ (v : Fin r → W) (x : W), q x = q base →
            (∀ t i, q (v t) i = false) → top observed v x = false
        ∀ c query, linear c query → ∀ base, drops c query base → p ≤ c := by
  intro p r hp hr W add diff top blocks lower hlower observed linear drops
  let signed := Finset.univ.sum (fun sample : W => if observed sample then (-1 : ℤ) else 1)
  let ι := Fin p × Fin r
  let V := ι → ZMod 2
  let eW : W ≃ V :=
    { toFun := fun x ⟨b, c⟩ => b2z (x b c)
      invFun := fun v b c => decide (v (b, c) = 1)
      left_inv := fun x => by
        ext b c
        cases h : x b c <;> simp [h, b2z]
      right_inv := fun v => by
        ext ⟨b, c⟩
        rcases zmod2_cases (v (b, c)) with h | h <;>
          simp [h, b2z] }
  have heW_add : ∀ x y : W, eW (add x y) = eW x + eW y := by
    intro x y; ext ⟨b, c⟩
    exact b2z_xor (x b c) (y b c)
  have heW_foldl : ∀ (f : W → Bool) (l : List W) (x : W),
      b2z (l.foldl diff f x) =
        foldDiffZ
          (fun v => b2z (f (eW.symm v)))
          (l.map eW) (eW x) := by
    intro f l
    induction l generalizing f with
    | nil =>
      intro x; simp [foldDiffZ_nil]
    | cons d t ih =>
      intro x
      simp only [List.foldl_cons, List.map_cons, foldDiffZ_cons]
      rw [ih (diff f d) x]
      congr 1
      ext v
      simp only [diff, diffZ,
        b2z_xor]
      congr 3
      apply eW.injective
      rw [heW_add, eW.apply_symm_apply, eW.apply_symm_apply]
  let rowSet : Fin p → Finset ι := fun b => Finset.univ.image (fun c : Fin r => (b, c))
  have hrow_card : ∀ b : Fin p, (rowSet b).card = r := by
    intro b
    rw [Finset.card_image_of_injective _ (fun c1 c2 h => (Prod.mk.inj h).2)]
    simp
  have hrow_inj : Function.Injective rowSet := by
    intro b1 b2 h
    have hmem : (b1, (⟨0, by omega⟩ : Fin r)) ∈ rowSet b2 := by
      rw [← h]; exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
    rcases Finset.mem_image.mp hmem with ⟨c, _, hc⟩
    exact (Prod.mk.inj hc).1.symm
  let blocksZ : V → ZMod 2 := fun v => ∑ b : Fin p, monom (rowSet b) v
  have hblocksZ : ∀ x : W, b2z (blocks x) = blocksZ (eW x) := by
    intro x
    dsimp only [blocks, blocksZ]
    rw [b2z_foldl_xor_ofFn]
    apply Finset.sum_congr rfl; intro b _
    rw [b2z_all_id_ofFn]
    unfold monom
    rw [Finset.prod_image (fun c1 _ c2 _ h => (Prod.mk.inj h).2)]
    rfl
  let lowerZ : V → ZMod 2 := fun v => b2z (lower (eW.symm v))
  let obsZ : V → ZMod 2 := fun v => blocksZ v + lowerZ v
  have hobsZ : ∀ x : W, b2z (observed x) = obsZ (eW x) := by
    intro x
    dsimp only [observed, obsZ, lowerZ]
    rw [b2z_xor, hblocksZ, eW.symm_apply_apply]
  have hlower_diff : ∀ (v : Fin r → V) (x : V),
      foldDiffZ lowerZ (List.ofFn v) x = 0 := by
    intro v x
    have hl := hlower (fun t => eW.symm (v t)) (eW.symm x)
    have hbz : b2z (top lower (fun t => eW.symm (v t)) (eW.symm x)) = 0 := by
      rw [hl]; rfl
    rw [heW_foldl] at hbz
    have hmap : (List.ofFn (fun t => eW.symm (v t))).map eW = List.ofFn v := by
      rw [List.map_ofFn]
      congr 1; funext t; exact eW.apply_symm_apply (v t)
    rw [hmap, eW.apply_symm_apply] at hbz
    exact hbz
  have hlower_anf : ∀ S : Finset ι, r ≤ S.card →
      anf lowerZ S = 0 :=
    anf_eq_zero_of_foldDiffZ_zero r lowerZ hlower_diff
  have hblocks_anf : ∀ S : Finset ι,
      anf blocksZ S = if ∃ b : Fin p, S = rowSet b then 1 else 0 := by
    intro S
    have hrew : blocksZ = fun v => ∑ U : Finset ι,
        (if ∃ b : Fin p, U = rowSet b then (1 : ZMod 2) else 0) *
          monom U v := by
      ext v
      dsimp only [blocksZ]
      simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
      refine Finset.sum_bij (fun b _ => rowSet b) ?_ ?_ ?_ ?_
      · intro b _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b, rfl⟩⟩
      · intro b1 _ b2 _ h; exact hrow_inj h
      · intro U hU
        rcases (Finset.mem_filter.mp hU).2 with ⟨b, rfl⟩
        exact ⟨b, Finset.mem_univ _, rfl⟩
      · intro b _; rfl
    rw [hrew, anf_unique]
  have hobs_anf : ∀ S : Finset ι,
      anf obsZ S =
        (if ∃ b : Fin p, S = rowSet b then 1 else 0) +
          anf lowerZ S := by
    intro S
    rw [anf_add, hblocks_anf]
  have hsigned_eq : signed = ∑ v : V, zSign (obsZ v) := by
    dsimp only [signed]
    have hterm : ∀ x : W, (if observed x then (-1 : ℤ) else 1) =
        zSign (obsZ (eW x)) := by
      intro x
      rw [← hobsZ x]
      unfold zSign
      cases observed x <;> decide
    simp_rw [hterm]
    exact Fintype.sum_equiv eW _ _ (fun _ => rfl)
  have hgoal1 : Int.ModEq ((2 : ℤ) ^ (p + 1)) signed ((2 : ℤ) ^ p) := by
    rw [hsigned_eq, signed_sum_anf obsZ]
    set supp := Finset.univ.filter (fun S : Finset ι => anf obsZ S = 1)
    let A0 : Finset (Finset ι) := Finset.univ.image rowSet
    have hA0_mem : A0 ∈ supp.powerset := by
      rw [Finset.mem_powerset]
      intro S hS
      rcases Finset.mem_image.mp hS with ⟨b, _, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hobs_anf, hlower_anf (rowSet b) (by rw [hrow_card])]
      simp
    have hA0_card : A0.card = p := by
      rw [Finset.card_image_of_injective _ hrow_inj]; simp
    have hA0_union : A0.biUnion id = Finset.univ := by
      ext ⟨b, c⟩
      simp only [Finset.mem_biUnion, id_eq, Finset.mem_image, Finset.mem_univ, true_and, iff_true, A0]
      exact ⟨rowSet b, ⟨b, rfl⟩, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
    have hcard_ι : Fintype.card ι = p * r := by simp [ι]
    rw [← Finset.add_sum_erase _ _ hA0_mem]
    have hterm0 : (-2 : ℤ) ^ A0.card * (2 : ℤ) ^ (Fintype.card ι - (A0.biUnion id).card) = (-2 : ℤ) ^ p := by
      rw [hA0_card, hA0_union, Finset.card_univ, Nat.sub_self, pow_zero, mul_one]
    rw [hterm0]
    have hrest_dvd : (2 : ℤ) ^ (p + 1) ∣
        ∑ A ∈ supp.powerset.erase A0,
          (-2 : ℤ) ^ A.card * (2 : ℤ) ^ (Fintype.card ι - (A.biUnion id).card) := by
      apply Finset.dvd_sum
      intro A hA
      have hAne : A ≠ A0 := (Finset.mem_erase.mp hA).1
      have hAsupp : A ⊆ supp := Finset.mem_powerset.mp (Finset.mem_erase.mp hA).2
      apply pow_two_dvd_term
      have hSle : ∀ S ∈ A, S.card ≤ r := by
        intro S hSA
        have h1 : anf obsZ S = 1 :=
          (Finset.mem_filter.mp (hAsupp hSA)).2
        by_contra hgt
        push Not at hgt
        have hnotrow : ¬ ∃ b : Fin p, S = rowSet b := by
          rintro ⟨b, rfl⟩; rw [hrow_card] at hgt; omega
        rw [hobs_anf, hlower_anf S (by omega)] at h1
        simp [hnotrow] at h1
      have hu_le : (A.biUnion id).card ≤ Fintype.card ι := Finset.card_le_univ _
      have hu_le_sum : (A.biUnion id).card ≤ ∑ S ∈ A, S.card := Finset.card_biUnion_le
      have hsum_le : ∑ S ∈ A, S.card ≤ A.card * r := by
        calc ∑ S ∈ A, S.card ≤ ∑ _S ∈ A, r := Finset.sum_le_sum hSle
          _ = A.card * r := by simp
      rw [hcard_ι] at hu_le ⊢
      by_cases hgt : p + 1 ≤ A.card
      · omega
      · by_cases hlt : A.card < p
        · have hmul : (p - A.card) * 2 ≤ (p - A.card) * r := Nat.mul_le_mul_left _ hr
          have hsub : p * r - A.card * r = (p - A.card) * r := (Nat.sub_mul p A.card r).symm
          omega
        · have heq : A.card = p := by omega
          by_contra hnot
          have hu_eq : (A.biUnion id).card = p * r := by omega
          have hsum_eq : ∑ S ∈ A, S.card = ∑ _S ∈ A, r := by
            have h1 : ∑ _S ∈ A, r = p * r := by simp [heq]
            have h2 : A.card * r = p * r := by rw [heq]
            omega
          have hall_r : ∀ S ∈ A, S.card = r := by
            intro S hSA
            by_contra hne_r
            have hltS : S.card < r := lt_of_le_of_ne (hSle S hSA) hne_r
            have hltSum : ∑ T ∈ A, T.card < ∑ _T ∈ A, r :=
              Finset.sum_lt_sum hSle ⟨S, hSA, hltS⟩
            omega
          have hsubA0 : A ⊆ A0 := by
            intro S hSA
            have hSr := hall_r S hSA
            have h1 : anf obsZ S = 1 :=
              (Finset.mem_filter.mp (hAsupp hSA)).2
            rw [hobs_anf, hlower_anf S (by omega)] at h1
            simp only [add_zero] at h1
            by_cases hrow : ∃ b : Fin p, S = rowSet b
            · rcases hrow with ⟨b, rfl⟩
              exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
            · simp [hrow] at h1
          have hEqA : A = A0 := Finset.eq_of_subset_of_card_le hsubA0 (by rw [heq, hA0_card])
          exact hAne hEqA
    rw [Int.modEq_iff_dvd]
    have hdiff_pow : (2 : ℤ) ^ (p + 1) ∣ (2 : ℤ) ^ p - (-2 : ℤ) ^ p := by
      have hfac : (2 : ℤ) ^ p - (-2 : ℤ) ^ p = (1 - (-1 : ℤ) ^ p) * (2 : ℤ) ^ p := by
        have : (-2 : ℤ) = (-1 : ℤ) * 2 := by ring
        rw [this, mul_pow]; ring
      rw [hfac, pow_succ]
      rcases Nat.even_or_odd p with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have h1 : (-1 : ℤ) ^ (k + k) = 1 := by
          rw [show k + k = 2 * k by omega, pow_mul]; norm_num
        rw [h1]; simp
      · have h1 : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
          rw [pow_succ, pow_mul]; norm_num
        rw [h1]
        refine ⟨1, ?_⟩; ring
    have hcomb : (2 : ℤ) ^ p - ((-2 : ℤ) ^ p +
        ∑ A ∈ supp.powerset.erase A0,
          (-2 : ℤ) ^ A.card * (2 : ℤ) ^ (Fintype.card ι - (A.biUnion id).card)) =
        ((2 : ℤ) ^ p - (-2 : ℤ) ^ p) -
        ∑ A ∈ supp.powerset.erase A0,
          (-2 : ℤ) ^ A.card * (2 : ℤ) ^ (Fintype.card ι - (A.biUnion id).card) := by ring
    rw [hcomb]
    exact dvd_sub hdiff_pow hrest_dvd
  intro c query hlin base hdrops
  by_contra hlt
  push Not at hlt
  let Q : V →ₗ[ZMod 2] (Fin c → ZMod 2) :=
    { toFun := fun v i => b2z (query (eW.symm v) i)
      map_add' := fun v1 v2 => by
        ext i
        have hsum : eW.symm (v1 + v2) = add (eW.symm v1) (eW.symm v2) := by
          apply eW.injective
          rw [heW_add, eW.apply_symm_apply, eW.apply_symm_apply, eW.apply_symm_apply]
        rw [hsum, hlin, b2z_xor]
        rfl
      map_smul' := fun a v => by
        ext i
        rcases zmod2_cases a with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply, Pi.zero_apply]
          have hz : eW.symm (0 : V) = add (eW.symm (0 : V)) (eW.symm (0 : V)) := by
            apply eW.injective
            rw [heW_add, eW.apply_symm_apply, add_zero]
          have hq0 := congrArg (fun w => b2z (query w i)) hz
          rw [hlin, b2z_xor] at hq0
          rcases zmod2_cases
            (b2z (query (eW.symm 0) i)) with h | h
          · exact h
          · rw [h] at hq0; exact absurd hq0 (by decide)
        · simp }
  let K : Submodule (ZMod 2) V := LinearMap.ker Q
  let n : ℕ := Module.finrank (ZMod 2) K
  have hdim_n : p * (r - 1) < n := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Q
    have hV : Module.finrank (ZMod 2) V = p * r := by
      simp [V, ι]
    have hrange : Module.finrank (ZMod 2) (LinearMap.range Q) ≤ c := by
      calc Module.finrank (ZMod 2) (LinearMap.range Q)
          ≤ Module.finrank (ZMod 2) (Fin c → ZMod 2) := Submodule.finrank_le _
        _ = c := by simp
    have hmul : p * (r - 1) + p = p * r := by
      have : r = (r - 1) + 1 := by omega
      conv_rhs => rw [this, mul_add, mul_one]
    dsimp only [n, K]
    omega
  have hobs_diff_ker : ∀ (v : Fin r → V) (x : V), (∀ t, v t ∈ K) →
      foldDiffZ obsZ (List.ofFn v) x = 0 := by
    intro v x hvK
    have hobs_split : ∀ y : V, foldDiffZ obsZ (List.ofFn v) y =
        foldDiffZ blocksZ (List.ofFn v) y := by
      intro y
      dsimp only [obsZ]
      rw [foldDiffZ_add, hlower_diff, add_zero]
    have hblocks_const : foldDiffZ blocksZ (List.ofFn v) x =
        foldDiffZ blocksZ (List.ofFn v) (eW base) := by
      dsimp only [blocksZ]
      rw [foldDiffZ_sum,
        foldDiffZ_sum]
      apply Finset.sum_congr rfl; intro b _
      apply foldDiffZ_monom_const
      rw [hrow_card, List.length_ofFn]
    rw [hobs_split x, hblocks_const, ← hobs_split (eW base)]
    have hvq : ∀ t i, query (eW.symm (v t)) i = false := by
      intro t i
      have hQt : Q (v t) = 0 := LinearMap.mem_ker.mp (hvK t)
      have hti := congrFun hQt i
      exact b2z_inj hti
    have hd := hdrops (fun t => eW.symm (v t)) base rfl hvq
    have hbz : b2z
        (top observed (fun t => eW.symm (v t)) base) = 0 := by
      rw [hd]; rfl
    rw [heW_foldl] at hbz
    have hmap : (List.ofFn (fun t => eW.symm (v t))).map eW = List.ofFn v := by
      rw [List.map_ofFn]; congr 1; funext t; exact eW.apply_symm_apply (v t)
    have hobs_fn : (fun u => b2z (observed (eW.symm u))) = obsZ := by
      ext u; rw [hobsZ, eW.apply_symm_apply]
    rw [hmap, hobs_fn] at hbz
    exact hbz
  have hpart : (∑ v : V, zSign (obsZ v)) =
      ∑ y : Fin c → ZMod 2, ∑ v ∈ Finset.univ.filter (fun v : V => Q v = y),
        zSign (obsZ v) := by
    rw [Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _)]
  have hdvd_signed : (2 : ℤ) ^ (p + 1) ∣ signed := by
    rw [hsigned_eq, hpart]
    apply Finset.dvd_sum
    intro y _
    by_cases hne : (Finset.univ.filter (fun v : V => Q v = y)).Nonempty
    · rcases hne with ⟨x0, hx0⟩
      have hQx0 : Q x0 = y := (Finset.mem_filter.mp hx0).2
      let B : Module.Basis (Fin n) (ZMod 2) K := Module.finBasis (ZMod 2) K
      let φ : (Fin n → ZMod 2) → V := fun z => ∑ i : Fin n, z i • (B i : V)
      have hφ_add : ∀ z1 z2, φ (z1 + z2) = φ z1 + φ z2 := by
        intro z1 z2; dsimp only [φ]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        simp only [Pi.add_apply, add_smul]
      have hφ_mem : ∀ z, φ z ∈ K := fun z =>
        Submodule.sum_mem K (fun i _ => Submodule.smul_mem K (z i) (B i).2)
      have hφ_inj : Function.Injective φ := by
        intro z1 z2 hEq
        have hK : (∑ i : Fin n, z1 i • B i) = ∑ i : Fin n, z2 i • B i := by
          apply Subtype.ext
          simpa [φ] using hEq
        have hlin_eq := B.equivFun.symm.injective (by
          simpa [Module.Basis.equivFun_symm_apply] using hK)
        exact hlin_eq
      have hφ_surj : ∀ v ∈ K, ∃ z, φ z = v := by
        intro v hvK
        refine ⟨B.equivFun ⟨v, hvK⟩, ?_⟩
        have hsum : (∑ i : Fin n, (B.equivFun ⟨v, hvK⟩) i • B i) = ⟨v, hvK⟩ := by
          simp [Module.Basis.equivFun_apply]
        have hcoe : (↑(∑ i : Fin n, (B.equivFun ⟨v, hvK⟩) i • B i) : V) = φ (B.equivFun ⟨v, hvK⟩) := by
          simp only [φ, Submodule.coe_sum, SetLike.val_smul]
        rw [← hcoe, hsum]
      have hfib : (∑ v ∈ Finset.univ.filter (fun v : V => Q v = y),
          zSign (obsZ v)) =
          ∑ z : Fin n → ZMod 2, zSign (obsZ (x0 + φ z)) := by
        symm
        refine Finset.sum_bij (fun z _ => x0 + φ z) ?_ ?_ ?_ ?_
        · intro z _
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [map_add, hQx0, LinearMap.mem_ker.mp (hφ_mem z), add_zero]
        · intro z1 _ z2 _ hEq
          exact hφ_inj (add_left_cancel hEq)
        · intro v hv
          have hQv : Q v = y := (Finset.mem_filter.mp hv).2
          have hvx0 : v - x0 ∈ K := by
            rw [LinearMap.mem_ker, map_sub, hQv, hQx0, sub_self]
          rcases hφ_surj (v - x0) hvx0 with ⟨z, hz⟩
          exact ⟨z, Finset.mem_univ _, by rw [hz]; abel⟩
        · intro z _; rfl
      rw [hfib]
      apply signed_sum_dvd_of_deg_lt p r hr
        (fun z => obsZ (x0 + φ z)) _ (by simpa using hdim_n)
      apply anf_eq_zero_of_foldDiffZ_zero
      intro u z
      rw [foldDiffZ_comp_affine x0 φ hφ_add obsZ (List.ofFn u) z,
        List.map_ofFn]
      exact hobs_diff_ker (fun t => φ (u t)) (x0 + φ z) (fun t => hφ_mem (u t))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      exact dvd_zero _
  rw [Int.modEq_iff_dvd] at hgoal1
  have hdvd_pow : (2 : ℤ) ^ (p + 1) ∣ (2 : ℤ) ^ p := by
    have : (2 : ℤ) ^ p = ((2 : ℤ) ^ p - signed) + signed := by ring
    rw [this]
    exact dvd_add hgoal1 hdvd_signed
  have hle : (2 : ℤ) ^ (p + 1) ≤ (2 : ℤ) ^ p := Int.le_of_dvd (by positivity) hdvd_pow
  have hlt_pow : (2 : ℤ) ^ p < (2 : ℤ) ^ (p + 1) := by
    rw [pow_succ]; linarith [show (0 : ℤ) < (2 : ℤ) ^ p by positivity]
  omega

end PEqualNP.Outside.L_meta_25623_aux.BlockBound

namespace PEqualNP.Outside.L_meta_25623_aux.Leaves

abbrev W (k : ℕ) := Fin k → Bool
def plus {k} (x y : W k) : W k := fun i => xor (x i) (y i)

private def enc : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv b := by cases b <;> rfl
  right_inv z := by fin_cases z <;> rfl

private def ew (k : ℕ) : W k ≃ (Fin k → ZMod 2) := Equiv.piCongrRight fun _ => enc

private lemma encode_sum {k} (x y : W k) : ew k (plus x y) = ew k x + ew k y := by
  funext i
  change enc (xor (x i) (y i)) = enc (x i) + enc (y i)
  cases x i <;> cases y i <;> rfl

private lemma decode_sum {k} (x y : Fin k → ZMod 2) : (ew k).symm (x+y) = plus ((ew k).symm x) ((ew k).symm y) := by
  apply (ew k).injective
  simp only [Equiv.apply_symm_apply, encode_sum]

private def lin {a b} (q : W a → W b) (hq : ∀ x y, q (plus x y) = plus (q x) (q y)) :
    (Fin a → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2) := by
  let f (z : Fin a → ZMod 2) := ew b (q ((ew a).symm z))
  have hf (u v) : f (u+v) = f u + f v := by unfold f; rw [decode_sum,hq,encode_sum]
  have hf0 : f 0 = 0 := by have h := hf 0 0; simpa using h
  exact {
    toFun := f
    map_add' := hf
    map_smul' := fun s v => by
      have hs : s = 0 ∨ s = 1 := by fin_cases s; exact Or.inl rfl; exact Or.inr rfl
      rcases hs with rfl | rfl <;> simp [hf0] }

theorem compress {k t} (q : W k → W t) (hq : ∀ x y, q (plus x y) = plus (q x) (q y)) :
    ∃ r, ∃ q' : W k → W r, (∀ x y, q' (plus x y) = plus (q' x) (q' y)) ∧
      (∀ x y, q' x = q' y ↔ q x = q y) ∧
      ∀ x, 2^r * (Finset.univ.filter (fun u => q u = q x)).card = 2^k := by
  classical
  let Q := lin q hq
  let R := LinearMap.range Q
  let K := LinearMap.ker Q
  let r := Module.finrank (ZMod 2) R
  let e := (Module.finBasis (ZMod 2) R).equivFun
  let Q' := e.toLinearMap.comp Q.rangeRestrict
  let q' (x : W k) := (ew r).symm (Q' (ew k x))
  have apps (x : W k) : Q (ew k x) = ew t (q x) := by change ew t (q ((ew k).symm (ew k x))) = _; rw [Equiv.symm_apply_apply]
  refine ⟨r,q',?_,?_,?_⟩
  · intro x y; simp only [q',encode_sum,map_add,decode_sum]
  · intro x y
    simp only [q', (ew r).symm.injective.eq_iff, e.injective.eq_iff, Q', LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    change Q.rangeRestrict (ew k x) = Q.rangeRestrict (ew k y) ↔ q x = q y
    rw [←Subtype.coe_inj]; change Q (ew k x) = Q (ew k y) ↔ _
    rw [apps,apps, (ew t).injective.eq_iff]
  · intro x
    let D := Finset.univ.filter fun u => q u = q x
    let F : D ≃ K := {
      toFun := fun v => ⟨ew k v.val - ew k x, by
        change Q _ = 0
        rw [map_sub,apps,apps, Finset.mem_filter.mp v.property |>.2, sub_self]⟩
      invFun := fun z => ⟨(ew k).symm (z.val + ew k x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        apply (ew t).injective
        rw [←apps,Equiv.apply_symm_apply,map_add,show Q z.val = 0 from z.property, zero_add,apps]⟩⟩
      left_inv := fun v => by apply Subtype.ext; simp
      right_inv := fun z => by apply Subtype.ext; simp }
    have hc : D.card = 2 ^ Module.finrank (ZMod 2) K := by
      calc D.card = Fintype.card K := by simpa only [Fintype.card_coe] using Fintype.card_congr F
           _ = _ := by rw [Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card]
    change 2 ^ r * D.card = 2 ^ k
    rw [hc, ←pow_add]
    congr 1
    have hr := Q.finrank_range_add_finrank_ker
    simpa [r,R,K] using hr

theorem count_leaves {k p n : ℕ} (leaf : W k → Fin n) (query : Fin n → W k → W k)
    (answer : Fin n → W k) (hlin : ∀ b x y, query b (plus x y) = plus (query b x) (query b y))
    (hleaf : ∀ b x, leaf x = b ↔ query b x = answer b)
    (need : ∀ (b : Fin n) (base : W k), leaf base = b → ∀ (r : ℕ) (q : W k → W r),
      (∀ x y, q (plus x y) = plus (q x) (q y)) → (∀ x y, q x = q y ↔ query b x = query b y) → p ≤ r) :
    2 ^ p ≤ n := by
  classical
  let D (b : Fin n) := Finset.univ.filter fun x => leaf x = b
  have bound (b : Fin n) : 2 ^ p * (D b).card ≤ 2 ^ k := by
    by_cases h : (D b).Nonempty
    · obtain ⟨x,hx⟩ := h
      have hx' := (Finset.mem_filter.mp hx).2
      obtain ⟨r,q,hq,he,hs⟩ := compress (query b) (hlin b)
      have hr := need b x hx' r q hq he
      have hd : D b = Finset.univ.filter (fun u => query b u = query b x) := by
        ext u; simp only [D,Finset.mem_filter,Finset.mem_univ,true_and,hleaf,(hleaf b x).mp hx']
      rw [hd,←hs x]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hr)
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]; simp
  have hsum : (∑ b : Fin n, (D b).card) = 2 ^ k := by
    have eq := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (W k)) (Finset.univ : Finset (Fin n)) leaf
    simpa [D, W] using eq
  have h := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => bound b
  rw [←Finset.mul_sum,hsum] at h
  simp at h
  exact h

abbrev BlockW (p : ℕ) := Fin p → Fin 4 → Bool
def plusB {p} (x y : BlockW p) : BlockW p := fun i j => xor (x i j) (y i j)
def diffOn {X : Type*} (plus : X → X → X) (f : X → Bool) (u x : X) := xor (f x) (f (plus x u))
def blockProduct {p} (x : BlockW p) : Bool :=
  (List.ofFn fun i : Fin p => (List.ofFn (x i)).all id).foldl xor false

theorem zeroOfAdd {p n} (q : BlockW p → Fin n → Bool)
    (hl : ∀ x y i, q (plusB x y) i = xor (q x i) (q y i)) :
    q (fun _ _ => false) = fun _ => false := by
  funext i
  have h := hl (fun _ _ => false) (fun _ _ => false) i
  change q (fun _ _ => false) i = xor (q (fun _ _ => false) i) (q (fun _ _ => false) i) at h
  simpa only [Bool.xor_self] using h

theorem diff_pull_branch {A B : Type*} (pa : A → A → A) (pb : B → B → B)
    (P : A → Prop) (closed : ∀ x u, P x → P u → P (pa x u))
    (point dir : A → B) (aff : ∀ x u, point (pa x u) = pb (point x) (dir u))
    (f : A → Bool) (g : B → Bool) (he : ∀ x, P x → f x = g (point x)) :
    ∀ (l : List A), (∀ u ∈ l, P u) → ∀ x, P x →
      l.foldl (diffOn pa) f x = (l.map dir).foldl (diffOn pb) g (point x) := by
  intro l
  induction l generalizing f g with
  | nil => exact fun _ x hx => he x hx
  | cons a l ih =>
    intro h x hx
    simp only [List.foldl_cons, List.map_cons]
    apply ih _ _ _
    · exact fun u hu => h u (List.mem_cons_of_mem _ hu)
    · exact hx
    · intro y hy
      simp only [diffOn, he y hy, he (pa y a) (closed y a hy (h a (by simp))), aff]

theorem exact_from_cube {k p n : ℕ} (E : BlockW p → W k)
    (hE : ∀ x y, E (plusB x y) = plus (E x) (E y))
    (f : W k → Bool) (low : ∀ base (v : Fin 4 → BlockW p) x,
      (List.ofFn v).foldl (diffOn plusB) (fun u => xor (f (plus base (E u))) (blockProduct u)) x = false)
    (leaf : W k → Fin n) (query : Fin n → W k → W k) (answer : Fin n → W k)
    (model : Fin n → W k → Bool) (hlin : ∀ b x y, query b (plus x y) = plus (query b x) (query b y))
    (hleaf : ∀ b x, leaf x = b ↔ query b x = answer b)
    (hcubic : ∀ b (v : Fin 4 → W k) x, (List.ofFn v).foldl (diffOn plus) (model b) x = false)
    (exactAll : ∀ x, f x = model (leaf x) x) : 2 ^ p ≤ n := by
  classical
  by_cases hp : p = 0
  · have pos := (leaf (fun _=>false)).isLt; simp [hp]; omega
  apply count_leaves leaf query answer hlin hleaf
  intro b base hbase r q hq he
  let qB (x : BlockW p) := q (E x)
  have linB (x y : BlockW p) (i) : qB (plusB x y) i = xor (qB x i) (qB y i) := by
    change q (E (plusB x y)) i = _
    rw [hE,hq]; rfl
  let res := fun u => xor (f (plus base (E u))) (blockProduct u)
  have cut := PEqualNP.Outside.L_meta_25623_aux.BlockBound.blockQueryLowerBound p 4 (by omega) (by decide) res (low base)
  apply cut r qB linB (fun _ _ => false)
  intro v x hx hv
  let P := fun w : BlockW p => qB w = fun _ => false
  have px : P x := hx.trans (zeroOfAdd qB linB)
  have pv (j : Fin 4) : P (v j) := funext (hv j)
  have closed (a u : BlockW p) (ha : P a) (hu : P u) : P (plusB a u) := by
    funext i
    rw [linB,congrFun ha i, congrFun hu i]; rfl
  have aff (a u : BlockW p) : plus base (E (plusB a u)) = plus (plus base (E a)) (E u) := by
    rw [hE]; funext i; exact (Bool.xor_assoc ..).symm
  have matchOn (z : BlockW p) (hz : P z) : xor (blockProduct z) (res z) = model b (plus base (E z)) := by
    have hfib : q (plus base (E z)) = q base := by
      rw [hq]; funext i
      change xor (q base i) (qB z i) = q base i
      simp [congrFun hz i]
    have lb : leaf (plus base (E z)) = b := (hleaf b _).mpr (((he _ _).mp hfib).trans ((hleaf b _).mp hbase))
    rw [← lb, ←exactAll]; unfold res
    cases blockProduct z <;> cases f (plus base (E z)) <;> rfl
  have tr := diff_pull_branch plusB plus P closed (fun y=>plus base (E y)) E aff
    (fun z => xor (blockProduct z) (res z)) (model b) matchOn (List.ofFn v)
    (fun u hu => by obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hu; exact pv j) x px
  rw [List.map_ofFn] at tr
  exact tr.trans (hcubic b (E ∘ v) _)

end PEqualNP.Outside.L_meta_25623_aux.Leaves

namespace PEqualNP.Outside.L_meta_25623_aux

def signedTwist {X : Type*} (v : X → Bool) (F : X → ℤ) (x : X) : ℤ :=
  if v x then -F x else F x

def character {X : Type*} (add : X → X → X) (l : X → Bool) : Prop :=
  ∀ x y, l (add x y) = xor (l x) (l y)

private theorem chooseSign (E T R : ℤ) (h : 2*E=T+R ∨ 2*E=T-R) :
    E.natAbs ≤ T.natAbs ∨ E.natAbs ≤ R.natAbs := by
  have h' : (2*E).natAbs ≤ T.natAbs+R.natAbs := by
    rcases h with h|h
    · rw [h]; exact Int.natAbs_add_le ..
    · rw [h,sub_eq_add_neg]; simpa using Int.natAbs_add_le T (-R)
  rw [Int.natAbs_mul] at h'
  change 2*E.natAbs≤_ at h'
  omega

theorem leafCharacter {X I : Type*} [Fintype X] [DecidableEq I] (add : X→X→X)
    (q : I→X→Bool) (ans : I→Bool) (hq : ∀ i, character add (q i))
    (s : Finset I) (F : X → ℤ) :
    ∃ l, character add l ∧
      (∑ x, if ∀ i ∈ s, q i x=ans i then F x else 0).natAbs ≤ (∑ x, signedTwist l F x).natAbs := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty => exact ⟨fun _=>false, fun _ _=>rfl, by simp [signedTwist]⟩
  | @insert i s hi ih =>
    let E := ∑ x, if ∀ j ∈ insert i s, q j x=ans j then F x else 0
    let T := ∑ x, if ∀ j ∈ s, q j x=ans j then F x else 0
    let R := ∑ x, if ∀ j ∈ s, q j x=ans j then signedTwist (q i) F x else 0
    have h : 2*E=T+R ∨ 2*E=T-R := by
      cases ha : ans i with
      | false =>
        left
        simp only [E,T,R,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        cases he : q i x <;> simp [ha,he,signedTwist,two_mul] <;> split_ifs <;> ring
      | true =>
        right
        simp only [E,T,R,Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        cases he : q i x <;> simp [ha,he,signedTwist,two_mul] <;> split_ifs <;> ring
    rcases chooseSign E T R h with hc|hc
    · obtain ⟨l,hl,hh⟩ := ih F
      exact ⟨l,hl,hc.trans hh⟩
    · obtain ⟨l,hl,hh⟩ := ih (signedTwist (q i) F)
      let l' := fun x => xor (q i x) (l x)
      refine ⟨l',?_,?_⟩
      · intro x y
        simp only [l', hq i x y, hl x y, Bool.xor_left_comm, Bool.xor_comm]
      · have e : ∀ x, signedTwist l (signedTwist (q i) F) x = signedTwist l' F x := by
          intro x
          cases hq' : q i x <;> cases hl' : l x <;> simp [signedTwist,l',hq',hl']
        simp_rw [e] at hh
        exact hc.trans hh

end PEqualNP.Outside.L_meta_25623_aux

namespace PEqualNP.Outside.L_meta_25623_aux

private theorem absSum {X : Type*} (s : Finset X) (f : X → ℤ) :
    (∑ x ∈ s, f x).natAbs ≤ ∑ x ∈ s, (f x).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (Int.natAbs_add_le ..).trans (Nat.add_le_add_left ih _)

theorem leafFourthBound {X : Type*} [Fintype X] [Nonempty X] {n k A B C : ℕ}
    (add : X → X → X) (leaf : X → Fin n) (query : Fin n → X → Fin k → Bool)
    (answer : Fin n → Fin k → Bool) (score : Fin n → X → ℤ)
    (hlin : ∀ b i, character add (fun x=>query b x i))
    (hleaf : ∀ b x, leaf x=b ↔ query b x=answer b)
    (hglobal : ∀ b l, character add l → A*(∑ x, signedTwist l (score b) x).natAbs^4 ≤ B*C^4) :
    A*(∑ x, score (leaf x) x).natAbs^4 ≤ B*(n*C)^4 := by
  classical
  let fiber := fun b : Fin n => ∑ x, if leaf x=b then score b x else 0
  have fiberBound (b : Fin n) : A*(fiber b).natAbs^4 ≤ B*C^4 := by
    obtain ⟨l,hl,h⟩ := leafCharacter add (fun i x=>query b x i) (answer b) (hlin b) Finset.univ (score b)
    have hh : (fiber b).natAbs ≤ (∑ x, signedTwist l (score b) x).natAbs := by
      simpa only [fiber,Finset.mem_univ,forall_const,← funext_iff,← hleaf] using h
    exact (Nat.mul_le_mul_left A (Nat.pow_le_pow_left hh 4)).trans (hglobal b l hl)
  have hn : (Finset.univ : Finset (Fin n)).Nonempty := ⟨leaf (Classical.choice ‹Nonempty X›),Finset.mem_univ _⟩
  obtain ⟨b,_,hb⟩ := Finset.exists_max_image Finset.univ (fun b => (fiber b).natAbs) hn
  have hs : (∑ x, score (leaf x) x) = ∑ b, fiber b := by
    simp only [fiber]; rw [Finset.sum_comm]; simp
  have hl : (∑ x, score (leaf x) x).natAbs ≤ n*(fiber b).natAbs := by
    rw [hs]
    exact (absSum _ _).trans (calc
      _ ≤ ∑ _ : Fin n, (fiber b).natAbs := Finset.sum_le_sum hb
      _ = n*(fiber b).natAbs := by simp)
  calc
    _ ≤ A*(n*(fiber b).natAbs)^4 := Nat.mul_le_mul_left A (Nat.pow_le_pow_left hl 4)
    _ = n^4*(A*(fiber b).natAbs^4) := by ring
    _ ≤ n^4*(B*C^4) := Nat.mul_le_mul_left (n^4) (fiberBound b)
    _ = _ := by ring

end PEqualNP.Outside.L_meta_25623_aux

namespace PEqualNP.Outside.L_meta_25623_aux

def boolDiff {X : Type*} (add : X → X → X) (f : X → Bool) (u x : X) := xor (f x) (f (add x u))
def cubic {X : Type*} (add : X → X → X) (f : X → Bool) : Prop :=
    ∀ (v : Fin 4 → X) x, (List.ofFn v).foldl (boolDiff add) f x = false
def agreementSign (a b : Bool) : ℤ := if a=b then 1 else -1

private theorem xorDiffList {X : Type*} (add : X→X→X) (l : List X) (f g : X→Bool) (x : X) :
    l.foldl (boolDiff add) (fun y=>xor (f y) (g y)) x =
      xor (l.foldl (boolDiff add) f x) (l.foldl (boolDiff add) g x) := by
  induction l generalizing f g with
  | nil => rfl
  | cons u l ih =>
    simp only [List.foldl_cons]
    have h : boolDiff add (fun y=>xor (f y) (g y)) u = fun y=>xor (boolDiff add f u y) (boolDiff add g u y) := by
      funext y
      simp only [boolDiff,Bool.xor_left_comm,Bool.xor_comm]
    rw [h,ih]

theorem cubicTwist {X : Type*} (add : X→X→X) {f l : X→Bool} (hf : cubic add f) (hl : character add l) :
    cubic add (fun x=>xor (f x) (l x)) := by
  intro v x
  rw [xorDiffList, hf, Bool.false_xor]
  have h₁ (u) : boolDiff add l u = fun _=>l u := by
    funext y
    simp [boolDiff,hl y u]
  have h₂ (b : Bool) (u : X) : boolDiff add (fun _=>b) u = fun _=>false := by
    funext y; exact Bool.xor_self _
  simp [List.ofFn_succ,h₁,h₂]

theorem affineCubicLeaves {X : Type*} [Fintype X] [Nonempty X] {n k A B C : ℕ}
    (add : X → X → X) (observed : X→Bool) (leaf : X → Fin n) (query : Fin n → X → Fin k → Bool)
    (answer : Fin n → Fin k → Bool) (model : Fin n → X → Bool)
    (hlin : ∀ b x y i, query b (add x y) i=xor (query b x i) (query b y i))
    (hleaf : ∀ b x, leaf x=b ↔ query b x=answer b) (hm : ∀ b, cubic add (model b))
    (hglobal : ∀ f, cubic add f → A*(∑ x, agreementSign (observed x) (f x)).natAbs^4 ≤ B*C^4) :
    A*(∑ x, agreementSign (observed x) (model (leaf x) x)).natAbs^4 ≤ B*(n*C)^4 := by
  apply leafFourthBound add leaf query answer (fun b x=>agreementSign (observed x) (model b x))
    (fun b i x y=> hlin b x y i) hleaf
  intro b l hl
  have H := hglobal (fun x=>xor (model b x) (l x)) (cubicTwist add (hm b) hl)
  convert H using 1
  congr 3
  apply Finset.sum_congr rfl
  intro x _
  cases ho : observed x <;> cases hm' : model b x <;> cases hl' : l x <;> simp [agreementSign,signedTwist,ho,hm',hl']

end PEqualNP.Outside.L_meta_25623_aux

namespace PEqualNP.Outside.L_meta_25623_aux

theorem averageFromBlocks {X I : Type*} [Fintype X] [Nonempty X] [Fintype I] [Nonempty I]
    {A B : ℕ} (point : X → I → X) (F : X → ℤ)
    (hperm : ∀ i, Function.Bijective (fun x=>point x i))
    (hbound : ∀ base, A*(∑ i, F (point base i)).natAbs^4 ≤ B*(Fintype.card I)^4) :
    A*(∑ x, F x).natAbs^4 ≤ B*(Fintype.card X)^4 := by
  classical
  let S := ∑ x, F x
  let R := fun x => ∑ i, F (point x i)
  have he : (Fintype.card I : ℤ)*S = ∑ x, R x := by
    unfold R
    rw [Finset.sum_comm]
    have h (i : I) : (∑ x, F (point x i))=S :=
      (Equiv.ofBijective (fun x=>point x i) (hperm i)).sum_comp F
    simp only [h,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  obtain ⟨base,_,hm⟩ := Finset.exists_max_image Finset.univ (fun x => (R x).natAbs) Finset.univ_nonempty
  have h : Fintype.card I*S.natAbs ≤ Fintype.card X*(R base).natAbs := by
    calc
      _ = ((Fintype.card I : ℤ)*S).natAbs := by rw [Int.natAbs_mul,Int.natAbs_natCast]
      _ = (∑ x, R x).natAbs := congrArg Int.natAbs he
      _ ≤ ∑ x, (R x).natAbs := absSum _ _
      _ ≤ ∑ _ : X, (R base).natAbs := Finset.sum_le_sum hm
      _ = _ := by simp
  have h' : (Fintype.card I)^4*(A*S.natAbs^4) ≤ (Fintype.card I)^4*(B*(Fintype.card X)^4) := calc
    _ = A*(Fintype.card I*S.natAbs)^4 := by ring
    _ ≤ A*(Fintype.card X*(R base).natAbs)^4 := Nat.mul_le_mul_left A (Nat.pow_le_pow_left h 4)
    _ = (Fintype.card X)^4*(A*(R base).natAbs^4) := by ring
    _ ≤ (Fintype.card X)^4*(B*(Fintype.card I)^4) := Nat.mul_le_mul_left _ (hbound base)
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h' (pow_pos Fintype.card_pos 4)

theorem xorShiftBijective {k : ℕ} (w : Fin k → Bool) :
    Function.Bijective (fun x : Fin k → Bool => fun i => xor (x i) (w i)) := by
  apply Function.Involutive.bijective
  intro x
  funext i
  simp

end PEqualNP.Outside.L_meta_25623_aux

namespace PEqualNP.Outside.L_meta_25623_aux
open scoped BigOperators

abbrev PKWord23 (k : ℕ) := Fin k → Bool
abbrev PKBlock23 (p : ℕ) := Fin p → Fin 4 → Bool
def pkWordAdd {k : ℕ} (x y : PKWord23 k) : PKWord23 k := fun i => xor (x i) (y i)
def pkBlockAdd {p : ℕ} (x y : PKBlock23 p) : PKBlock23 p := fun i j => xor (x i j) (y i j)
def pkBlockTarget {p : ℕ} (x : PKBlock23 p) : Bool :=
  (List.ofFn (fun i : Fin p => (List.ofFn (x i)).all id)).foldl xor false

theorem cubicXor23 {A : Type*} (add : A→A→A) {f g : A→Bool} (hf : cubic add f) (hg : cubic add g) :
    cubic add (fun x=>xor (f x) (g x)) := by
  intro v x
  have H : ∀ (l : List A) (u w : A → Bool), l.foldl (boolDiff add) (fun y=>xor (u y) (w y)) x =
      xor (l.foldl (boolDiff add) u x) (l.foldl (boolDiff add) w x) := by
    intro l
    induction l with
    | nil => exact fun _ _ => rfl
    | cons a l ih =>
      intro u w
      simp only [List.foldl_cons]
      have h : boolDiff add (fun y=>xor (u y) (w y)) a = fun y=>xor (boolDiff add u a y) (boolDiff add w a y) := by
        funext y; simp only [boolDiff,Bool.xor_left_comm,Bool.xor_comm]
      rw [h,ih]
  rw [H, hf v x, hg v x]; rfl

theorem cubicAffine23 {A B : Type*} (pa : A→A→A) (pb : B→B→B) (point dir : A→B)
    (h : ∀ x y, point (pa x y)=pb (point x) (dir y)) (f : B→Bool) (hf : cubic pb f) :
    cubic pa (fun x=>f (point x)) := by
  intro v x
  have H : ∀ (l : List A) (g : B→Bool), l.foldl (boolDiff pa) (fun y=>g (point y)) x =
      (l.map dir).foldl (boolDiff pb) g (point x) := by
    intro l
    induction l with
    | nil => exact fun _ => rfl
    | cons a l ih =>
      intro g
      simp only [List.foldl_cons,List.map_cons]
      have hm : boolDiff pa (fun y=>g (point y)) a = fun y=> boolDiff pb g (dir a) (point y) := by
        funext y; simp only [boolDiff,h]
      rw [hm,ih]
  rw [H,List.map_ofFn]
  exact hf _ _

theorem fourthFromMean23 {X : Type*} [Fintype X] [Nonempty X] {A B : ℕ} (F : X→ℤ)
    (h : (A:ℝ)*(𝔼 x, (F x:ℝ))^4 ≤ B) :
    A*(∑ x, F x).natAbs^4 ≤ B*(Fintype.card X)^4 := by
  rw [Fintype.expect_eq_sum_div_card,div_pow,mul_div_assoc'] at h
  have h' := (div_le_iff₀ (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) 4)).mp h
  have h'' : (A:ℤ)*(∑ x, F x)^4 ≤ B*(Fintype.card X:ℤ)^4 := by exact_mod_cast h'
  have hAbs (z : ℤ) : (z.natAbs:ℤ)^4=z^4 := by
    rw [Int.natCast_natAbs,Even.pow_abs (by decide : Even 4)]
  exact_mod_cast (show (A:ℤ)*((∑ x, F x).natAbs:ℤ)^4 ≤ B*(Fintype.card X:ℤ)^4 by rw [hAbs]; exact h'')

theorem globalBound {k p n : ℕ} (E : PKBlock23 p → PKWord23 k)
    (hE : ∀ x y, E (pkBlockAdd x y)=pkWordAdd (E x) (E y))
    (obs : PKWord23 k→Bool) (low : ∀ base, cubic pkBlockAdd (fun z=>xor (obs (pkWordAdd base (E z))) (pkBlockTarget z)))
    (leaf : PKWord23 k → Fin n) (query : Fin n → PKWord23 k → PKWord23 k) (answer : Fin n → PKWord23 k)
    (model : Fin n → PKWord23 k → Bool) (hlin : ∀ b x y, query b (pkWordAdd x y)=pkWordAdd (query b x) (query b y))
    (hleaf : ∀ b x, leaf x=b ↔ query b x=answer b) (hm : ∀ b, cubic pkWordAdd (model b))
    (localBound : ∀ (f : PKBlock23 p → Bool), cubic pkBlockAdd (fun z=>xor (f z) (pkBlockTarget z)) →
      8^p*(∑ z, agreementSign false (f z)).natAbs^4 ≤ 7^p*(Fintype.card (PKBlock23 p))^4) :
    8^p*(∑ x, agreementSign (obs x) (model (leaf x) x)).natAbs^4 ≤ 7^p*(n*2^k)^4 := by
  apply affineCubicLeaves pkWordAdd obs leaf query answer model (fun b x y i=>congrFun (hlin b x y) i) hleaf hm
  intro f hf
  have h := averageFromBlocks (A:=8^p) (B:=7^p) (fun base z => pkWordAdd base (E z))
    (fun x=>agreementSign (obs x) (f x)) (fun z => xorShiftBijective (E z))
  have cardX : Fintype.card (PKWord23 k)=2^k := by simp [PKWord23]
  rw [← cardX]
  apply h
  intro base
  let point := fun z=>pkWordAdd base (E z)
  have ha (x y : PKBlock23 p) : point (pkBlockAdd x y)=pkWordAdd (point x) (E y) := by
    dsimp only [point]; rw [hE]; funext i; exact (Bool.xor_assoc ..).symm
  have H := cubicXor23 pkBlockAdd (low base) (cubicAffine23 pkBlockAdd pkWordAdd point E ha f hf)
  let g := fun z=>xor (obs (point z)) (f (point z))
  have HG : cubic pkBlockAdd (fun z=>xor (g z) (pkBlockTarget z)) := by
    convert H using 1
    funext z
    simp only [g,point,Bool.xor_comm,Bool.xor_left_comm]
  have score (z) : agreementSign (obs (point z)) (f (point z))=agreementSign false (g z) := by
    cases ho : obs (point z) <;> cases hq : f (point z) <;> simp [agreementSign,g,ho,hq]
  change 8^p*(∑ z, agreementSign (obs (point z)) (f (point z))).natAbs^4 ≤ _
  simp_rw [score]
  exact localBound g HG

end PEqualNP.Outside.L_meta_25623_aux

namespace PEqualNP.Outside.L_meta_25623_aux
open scoped BigOperators
noncomputable section
variable {X : Type*} [Fintype X] [Nonempty X]

theorem sqMean23 (f : X→ℝ) : (𝔼 x, f x)^2 ≤ 𝔼 x, (f x)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : X=>(1:ℝ)) f
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  simp only [Fintype.expect_eq_sum_div_card,div_pow]
  have hp : (0:ℝ)<Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
  nlinarith [mul_le_mul_of_nonneg_right h hp.le]

theorem powMean23 (n : Nat) (f : X→ℝ) : (𝔼 x, f x)^(2^n) ≤ 𝔼 x, (f x)^(2^n) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ (2:Nat) n, Nat.mul_comm (2^n) 2, pow_mul]
    exact (pow_le_pow_left₀ (sq_nonneg _) (sqMean23 f) _).trans (ih (fun x=>(f x)^2))

def delta23 (plus : X→X→X) (f : X→ℝ) (h x : X) := f x * f (plus x h)

def cube23 (plus : X→X→X) : Nat → (X→ℝ) → ℝ
  | 0,f=>𝔼 x, f x
  | n+1,f=>𝔼 h,cube23 plus n (delta23 plus f h)

theorem sqMean_delta23 (plus : X→X→X) (bij : ∀x,Function.Bijective (plus x)) (f : X→ℝ) :
    (𝔼 x, f x)^2 = 𝔼 h, 𝔼 x, delta23 plus f h x := by
  rw [sq,Fintype.expect_mul_expect]
  conv_rhs => rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  rw [←Finset.mul_expect]
  unfold delta23
  rw [←Finset.mul_expect]
  congr 1
  exact (Fintype.expect_bijective (plus x) (bij x) (fun i=>f (plus x i)) f (fun _=>rfl)).symm

theorem cube_bound23 (plus : X→X→X) (bij : ∀x,Function.Bijective (plus x)) (n : Nat) (f : X→ℝ) :
    (𝔼 x, f x)^(2^n) ≤ cube23 plus n f := by
  induction n generalizing f with
  | zero => simp [cube23]
  | succ n ih =>
    rw [pow_succ (2:Nat),Nat.mul_comm,pow_mul,sqMean_delta23 plus bij]
    apply (powMean23 n _).trans
    apply Finset.expect_le_expect
    intro h _
    exact ih (delta23 plus f h)

end
end PEqualNP.Outside.L_meta_25623_aux

namespace PEqualNP.Outside.L_meta_25623_aux
open scoped BigOperators
noncomputable section
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Nonempty X]

theorem mean_prod23 (f : I→X→ℝ) :
    (𝔼 x : I→X, ∏ i, f i (x i)) = ∏ i, 𝔼 y, f i y := by
  classical
  simp only [Fintype.expect_eq_sum_div_card,←Fintype.prod_sum,Finset.prod_div_distrib,
    Fintype.card_fun,Nat.cast_pow,Finset.prod_const,Finset.card_univ]

theorem cube_prod23 (plus : X→X→X) (f : I→X→ℝ) (n : Nat) :
    cube23 (fun (x y : I→X) i=>plus (x i) (y i)) n (fun x=>∏ i, f i (x i)) =
    ∏ i, cube23 plus n (f i) := by
  classical
  induction n generalizing f with
  | zero => exact mean_prod23 f
  | succ n ih =>
    simp only [cube23]
    have h (a : I→X) :
        delta23 (fun (x y : I→X) i=>plus (x i) (y i)) (fun x=>∏ i, f i (x i)) a =
        fun x=> ∏ i, delta23 plus (f i) (a i) (x i) := by
      funext x
      simp only [delta23,Finset.prod_mul_distrib]
    simp only [h,ih]
    exact mean_prod23 (fun i y=>cube23 plus n (delta23 plus (f i) y))

theorem cube_one23 (plus : X→X→X) (n : Nat) : cube23 plus n (fun _=>1)=1 := by
  induction n with
  | zero => exact Fintype.expect_one
  | succ n ih =>
    have h (a : X) : delta23 plus (fun _=>1) a=fun _=>1 := by funext x; simp [delta23]
    simp only [cube23,h,ih,Fintype.expect_one]

def sign23 (b : Bool) : ℝ := if b then -1 else 1

def bd23 (plus : X→X→X) (f : X→Bool) (v x : X) := xor (f x) (f (plus x v))

theorem delta_sign23 (plus : X→X→X) (f : X→Bool) (h : X) :
    delta23 plus (fun x=>sign23 (f x)) h = fun x=>sign23 (bd23 plus f h x) := by
  funext x
  simp only [delta23,bd23]
  cases f x <;> cases f (plus x h) <;> norm_num [sign23]

theorem same_cube23 (plus : X→X→X) (f g : X→Bool)
    (hh : ∀ (v : Fin 4→X) x, (List.ofFn v).foldl (bd23 plus) f x = (List.ofFn v).foldl (bd23 plus) g x) :
    cube23 plus 4 (fun x=>sign23 (f x))=cube23 plus 4 (fun x=>sign23 (g x)) := by
  simp only [cube23,delta_sign23]
  repeat' apply Finset.expect_congr rfl <;> intro _ _
  rename_i a _ b _ c _ d _ x _
  exact congrArg sign23 (hh ![a,b,c,d] x)

end
end PEqualNP.Outside.L_meta_25623_aux

namespace PEqualNP.Outside.L_meta_25623_aux
open scoped BigOperators
noncomputable section

def plusRow23 (x y : Fin 4→Bool) (j : Fin 4) := xor (x j) (y j)
def plusBlock23 {p : Nat} (x y : Fin p→Fin 4→Bool) (i : Fin p) := plusRow23 (x i) (y i)
def mono23 (x : Fin 4→Bool) := (List.ofFn x).all id
def target23 {p : Nat} (m : Fin p→Bool) (x : Fin p→Fin 4→Bool) :=
  (List.ofFn (fun i => m i && mono23 (x i))).foldl xor false

theorem sgn_xor23 (a b : Bool) : sign23 (xor a b)=sign23 a * sign23 b := by
  cases a <;> cases b <;> norm_num [sign23]

private theorem sign_fold23 (l : List Bool) (b : Bool) :
    sign23 (l.foldl xor b)=sign23 b * (l.map sign23).prod := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons,ih,sgn_xor23];simp [mul_assoc]

theorem sign_target23 {p : Nat} (m : Fin p→Bool) :
    (fun x=>sign23 (target23 m x)) =
    fun x=> ∏ i, (if m i then sign23 (mono23 (x i)) else 1) := by
  funext x
  rw [target23,sign_fold23,List.map_ofFn,List.prod_ofFn]
  simp only [show sign23 false=1 from rfl,one_mul,Function.comp_apply]
  apply Finset.prod_congr rfl
  intro i _
  cases m i <;> rfl

theorem bd_xor23 {A : Type*} (plus : A→A→A) (f g : A→Bool) (l : List A) :
    l.foldl (bd23 plus) (fun x=>xor (f x) (g x)) =
    fun x=>xor (l.foldl (bd23 plus) f x) (l.foldl (bd23 plus) g x) := by
  induction l generalizing f g with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    have hd : bd23 plus (fun x=>xor (f x) (g x)) a = fun x=>xor (bd23 plus f a x) (bd23 plus g a x) := by
      funext x
      simp [bd23,Bool.xor_comm,Bool.xor_assoc,Bool.xor_left_comm]
    rw [hd,ih]

theorem cubicBias23 {p : Nat} (m : Fin p→Bool) (f : (Fin p→Fin 4→Bool)→Bool)
    (hc : ∀ (v : Fin 4→(Fin p→Fin 4→Bool)) x,
      (List.ofFn v).foldl (bd23 plusBlock23) (fun y=>xor (f y) (target23 m y)) x=false)
    (hblock : cube23 plusRow23 4 (fun x=>sign23 (mono23 x)) = 197/512) :
    let q := (Finset.univ.filter (fun i=>m i=true)).card
    (8:ℝ)^q * (𝔼 x, sign23 (f x))^4 ≤ 7^q := by
  classical
  intro q
  have bij (x : Fin p→Fin 4→Bool) : Function.Bijective (plusBlock23 x) := by
    apply Function.Involutive.bijective
    intro a
    funext i j
    simp [plusBlock23,plusRow23]
  have same := same_cube23 plusBlock23 f (target23 m) (fun v x=>by
    have h := hc v x
    rw [bd_xor23] at h
    cases u : (List.ofFn v).foldl (bd23 plusBlock23) f x <;>
      cases w : (List.ofFn v).foldl (bd23 plusBlock23) (target23 m) x <;> simp_all)
  have hb := cube_bound23 plusBlock23 bij 4 (fun x=>sign23 (f x))
  have hecube : cube23 plusBlock23 4 (fun y=>sign23 (target23 m y)) = (197/512 : ℝ)^q := by
    rw [sign_target23]
    let F := fun (i:Fin p) (x:Fin 4→Bool)=> if m i then sign23 (mono23 x) else 1
    change cube23 (fun (x y : Fin p→Fin 4→Bool) i=>plusRow23 (x i) (y i)) 4 (fun x=>∏ i,F i (x i))=_
    rw [cube_prod23]
    have he (i : Fin p) : cube23 plusRow23 4 (F i)= if m i=true then (197/512:ℝ) else 1 := by
      cases hh : m i <;> simp [F,hh,cube_one23,hblock]
    simp only [he]
    rw [←Finset.prod_filter]
    simp [q,div_pow]
  rw [same,hecube] at hb
  have hratio : (197/512:ℝ)^q ≤ ((7/8:ℝ)^4)^q := by
    apply pow_le_pow_left₀ <;> norm_num
  have hpow : ((𝔼 x, sign23 (f x))^4)^4 ≤ ((7/8:ℝ)^q)^4 := by
    rw [←pow_mul,←pow_mul, Nat.mul_comm q 4]
    exact hb.trans (by simpa [pow_mul] using hratio)
  have h4 : (𝔼 x, sign23 (f x))^4 ≤ (7/8:ℝ)^q := by
    by_contra! h
    have hlt := pow_lt_pow_left₀ h (by positivity : (0:ℝ)≤(7/8:ℝ)^q) (by decide : 4≠0)
    linarith
  rw [div_pow] at h4
  rw [mul_comm]
  exact (le_div_iff₀ (by positivity)).mp h4

end
end PEqualNP.Outside.L_meta_25623_aux

namespace PEqualNP.Outside.L_meta_25623_aux
open scoped BigOperators
noncomputable section

private def code23 (x : Fin 4→Bool) : Fin 16 :=
  Fin.ofNat 16 ((x 0).toNat + 2*(x 1).toNat + 4*(x 2).toNat + 8*(x 3).toNat)
private def read23 (x : Fin 16) (j : Fin 4) := x.val.testBit j.val
private def codeEquiv23 : (Fin 4→Bool) ≃ Fin 16 where
  toFun := code23
  invFun := read23
  left_inv := by decide
  right_inv := by decide

private def mask23 (m : Nat) (x : Fin 4→Bool) := m.testBit (code23 x).val

private def rowCube23 (n m : Nat) := cube23 plusRow23 n (fun x=>sign23 (mask23 m x))

private theorem rowStep23 (n m : Nat) (T : Fin 16→Nat) (V : Fin 16→ℤ) (s : ℤ)
    (hs : ∀ a x, bd23 plusRow23 (mask23 m) (read23 a) x = mask23 (T a) x)
    (hc : ∀ a, rowCube23 n (T a) = (V a:ℝ) / 16^n)
    (ht : ∑ i, V i = s) : rowCube23 (n+1) m=(s:ℝ)/16^(n+1) := by
  unfold rowCube23
  rw [cube23]
  have ht' : (∑ a, (V a:ℝ))=(s:ℝ) := by exact_mod_cast ht
  calc
    _ = 𝔼 a : Fin 16, cube23 plusRow23 n (delta23 plusRow23 (fun x=>sign23 (mask23 m x)) (read23 a)) := by
      exact Fintype.expect_equiv codeEquiv23 _ _ (fun i=>by
        have h := codeEquiv23.left_inv i
        change read23 (code23 i)=i at h
        change _=cube23 _ n (delta23 _ _ (read23 (code23 i)))
        rw [h])
    _ = 𝔼 a : Fin 16, (V a:ℝ)/16^n := by
      apply Finset.expect_congr rfl
      intro a _
      rw [delta_sign23, show (fun x=>sign23 (bd23 plusRow23 (mask23 m) (read23 a) x))=
          (fun x=>sign23 (mask23 (T a) x)) by funext x;rw [hs]]
      exact hc a
    _ = _ := by rw [Fintype.expect_eq_sum_div_card, ←Finset.sum_div,ht'];simp [pow_succ,div_div]

private theorem rowZero23 (m : Nat) (b : Bool) (hm : ∀ x, mask23 m x = b) :
    rowCube23 0 m = sign23 b := by
  simp only [rowCube23,cube23,hm,Fintype.expect_const]

private theorem rc23_0_0 : rowCube23 0 0 = (1:ℝ)/16^0 := by
  rw [rowZero23 0 false (by decide)]; norm_num [sign23]

private theorem rc23_0_65535 : rowCube23 0 65535 = ((-1:ℤ):ℝ)/16^0 := by
  rw [rowZero23 65535 true (by decide)]; norm_num [sign23]

private theorem rc23_1_0 : rowCube23 1 0 = (16:ℝ)/16^1 := by
  apply rowStep23 0 0 ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] 16 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0

private theorem rc23_1_38505 : rowCube23 1 38505 = (0:ℝ)/16^1 := by
  apply rowStep23 0 38505 ![0,65535,65535,0,65535,0,0,65535,65535,0,0,65535,0,65535,65535,0] ![1,(-1),(-1),1,(-1),1,1,(-1),(-1),1,1,(-1),1,(-1),(-1),1] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0

private theorem rc23_1_38550 : rowCube23 1 38550 = (0:ℝ)/16^1 := by
  apply rowStep23 0 38550 ![0,65535,65535,0,65535,0,0,65535,0,65535,65535,0,65535,0,0,65535] ![1,(-1),(-1),1,(-1),1,1,(-1),1,(-1),(-1),1,(-1),1,1,(-1)] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535

private theorem rc23_1_39270 : rowCube23 1 39270 = (0:ℝ)/16^1 := by
  apply rowStep23 0 39270 ![0,65535,65535,0,0,65535,65535,0,65535,0,0,65535,65535,0,0,65535] ![1,(-1),(-1),1,1,(-1),(-1),1,(-1),1,1,(-1),(-1),1,1,(-1)] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535

private theorem rc23_1_39321 : rowCube23 1 39321 = (0:ℝ)/16^1 := by
  apply rowStep23 0 39321 ![0,65535,65535,0,0,65535,65535,0,0,65535,65535,0,0,65535,65535,0] ![1,(-1),(-1),1,1,(-1),(-1),1,1,(-1),(-1),1,1,(-1),(-1),1] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0

private theorem rc23_1_42330 : rowCube23 1 42330 = (0:ℝ)/16^1 := by
  apply rowStep23 0 42330 ![0,65535,0,65535,65535,0,65535,0,65535,0,65535,0,0,65535,0,65535] ![1,(-1),1,(-1),(-1),1,(-1),1,(-1),1,(-1),1,1,(-1),1,(-1)] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535

private theorem rc23_1_42405 : rowCube23 1 42405 = (0:ℝ)/16^1 := by
  apply rowStep23 0 42405 ![0,65535,0,65535,65535,0,65535,0,0,65535,0,65535,65535,0,65535,0] ![1,(-1),1,(-1),(-1),1,(-1),1,1,(-1),1,(-1),(-1),1,(-1),1] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0

private theorem rc23_1_43605 : rowCube23 1 43605 = (0:ℝ)/16^1 := by
  apply rowStep23 0 43605 ![0,65535,0,65535,0,65535,0,65535,65535,0,65535,0,65535,0,65535,0] ![1,(-1),1,(-1),1,(-1),1,(-1),(-1),1,(-1),1,(-1),1,(-1),1] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0

private theorem rc23_1_43690 : rowCube23 1 43690 = (0:ℝ)/16^1 := by
  apply rowStep23 0 43690 ![0,65535,0,65535,0,65535,0,65535,0,65535,0,65535,0,65535,0,65535] ![1,(-1),1,(-1),1,(-1),1,(-1),1,(-1),1,(-1),1,(-1),1,(-1)] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_65535

private theorem rc23_1_49980 : rowCube23 1 49980 = (0:ℝ)/16^1 := by
  apply rowStep23 0 49980 ![0,0,65535,65535,65535,65535,0,0,65535,65535,0,0,0,0,65535,65535] ![1,1,(-1),(-1),(-1),(-1),1,1,(-1),(-1),1,1,1,1,(-1),(-1)] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535

private theorem rc23_1_50115 : rowCube23 1 50115 = (0:ℝ)/16^1 := by
  apply rowStep23 0 50115 ![0,0,65535,65535,65535,65535,0,0,0,0,65535,65535,65535,65535,0,0] ![1,1,(-1),(-1),(-1),(-1),1,1,1,1,(-1),(-1),(-1),(-1),1,1] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0

private theorem rc23_1_52275 : rowCube23 1 52275 = (0:ℝ)/16^1 := by
  apply rowStep23 0 52275 ![0,0,65535,65535,0,0,65535,65535,65535,65535,0,0,65535,65535,0,0] ![1,1,(-1),(-1),1,1,(-1),(-1),(-1),(-1),1,1,(-1),(-1),1,1] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0

private theorem rc23_1_52428 : rowCube23 1 52428 = (0:ℝ)/16^1 := by
  apply rowStep23 0 52428 ![0,0,65535,65535,0,0,65535,65535,0,0,65535,65535,0,0,65535,65535] ![1,1,(-1),(-1),1,1,(-1),(-1),1,1,(-1),(-1),1,1,(-1),(-1)] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535

private theorem rc23_1_61455 : rowCube23 1 61455 = (0:ℝ)/16^1 := by
  apply rowStep23 0 61455 ![0,0,0,0,65535,65535,65535,65535,65535,65535,65535,65535,0,0,0,0] ![1,1,1,1,(-1),(-1),(-1),(-1),(-1),(-1),(-1),(-1),1,1,1,1] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0

private theorem rc23_1_61680 : rowCube23 1 61680 = (0:ℝ)/16^1 := by
  apply rowStep23 0 61680 ![0,0,0,0,65535,65535,65535,65535,0,0,0,0,65535,65535,65535,65535] ![1,1,1,1,(-1),(-1),(-1),(-1),1,1,1,1,(-1),(-1),(-1),(-1)] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535

private theorem rc23_1_65280 : rowCube23 1 65280 = (0:ℝ)/16^1 := by
  apply rowStep23 0 65280 ![0,0,0,0,0,0,0,0,65535,65535,65535,65535,65535,65535,65535,65535] ![1,1,1,1,1,1,1,1,(-1),(-1),(-1),(-1),(-1),(-1),(-1),(-1)] 0 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_0
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535
  · exact rc23_0_65535

private theorem rc23_2_0 : rowCube23 2 0 = (256:ℝ)/16^2 := by
  apply rowStep23 1 0 ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] ![16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16] 256 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0

private theorem rc23_2_33048 : rowCube23 2 33048 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33048 ![0,49980,42330,39321,39321,42330,49980,0,39321,42330,49980,0,0,49980,42330,39321] ![16,0,0,0,0,0,0,16,0,0,0,16,16,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_42330
  · exact rc23_1_39321
  · exact rc23_1_39321
  · exact rc23_1_42330
  · exact rc23_1_49980
  · exact rc23_1_0
  · exact rc23_1_39321
  · exact rc23_1_42330
  · exact rc23_1_49980
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_42330
  · exact rc23_1_39321

private theorem rc23_2_33060 : rowCube23 2 33060 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33060 ![0,49980,42405,39270,39270,42405,49980,0,42405,39270,0,49980,49980,0,39270,42405] ![16,0,0,0,0,0,0,16,0,0,16,0,0,16,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_42405
  · exact rc23_1_39270
  · exact rc23_1_39270
  · exact rc23_1_42405
  · exact rc23_1_49980
  · exact rc23_1_0
  · exact rc23_1_42405
  · exact rc23_1_39270
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_49980
  · exact rc23_1_0
  · exact rc23_1_39270
  · exact rc23_1_42405

private theorem rc23_2_33090 : rowCube23 2 33090 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33090 ![0,50115,42330,39270,39270,42330,50115,0,50115,0,39270,42330,42330,39270,0,50115] ![16,0,0,0,0,0,0,16,0,16,0,0,0,0,16,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_50115
  · exact rc23_1_42330
  · exact rc23_1_39270
  · exact rc23_1_39270
  · exact rc23_1_42330
  · exact rc23_1_50115
  · exact rc23_1_0
  · exact rc23_1_50115
  · exact rc23_1_0
  · exact rc23_1_39270
  · exact rc23_1_42330
  · exact rc23_1_42330
  · exact rc23_1_39270
  · exact rc23_1_0
  · exact rc23_1_50115

private theorem rc23_2_33153 : rowCube23 2 33153 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33153 ![0,50115,42405,39321,39321,42405,50115,0,0,50115,42405,39321,39321,42405,50115,0] ![16,0,0,0,0,0,0,16,16,0,0,0,0,0,0,16] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_50115
  · exact rc23_1_42405
  · exact rc23_1_39321
  · exact rc23_1_39321
  · exact rc23_1_42405
  · exact rc23_1_50115
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_50115
  · exact rc23_1_42405
  · exact rc23_1_39321
  · exact rc23_1_39321
  · exact rc23_1_42405
  · exact rc23_1_50115
  · exact rc23_1_0

private theorem rc23_2_33300 : rowCube23 2 33300 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33300 ![0,49980,43605,38550,43605,38550,0,49980,38550,43605,49980,0,49980,0,38550,43605] ![16,0,0,0,0,0,16,0,0,0,0,16,0,16,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_43605
  · exact rc23_1_38550
  · exact rc23_1_43605
  · exact rc23_1_38550
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_38550
  · exact rc23_1_43605
  · exact rc23_1_49980
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_0
  · exact rc23_1_38550
  · exact rc23_1_43605

private theorem rc23_2_33320 : rowCube23 2 33320 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33320 ![0,49980,43690,38505,43690,38505,0,49980,43690,38505,0,49980,0,49980,43690,38505] ![16,0,0,0,0,0,16,0,0,0,16,0,16,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_43690
  · exact rc23_1_38505
  · exact rc23_1_43690
  · exact rc23_1_38505
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_43690
  · exact rc23_1_38505
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_43690
  · exact rc23_1_38505

private theorem rc23_2_33345 : rowCube23 2 33345 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33345 ![0,50115,43605,38505,43605,38505,0,50115,50115,0,38505,43605,38505,43605,50115,0] ![16,0,0,0,0,0,16,0,0,16,0,0,0,0,0,16] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_50115
  · exact rc23_1_43605
  · exact rc23_1_38505
  · exact rc23_1_43605
  · exact rc23_1_38505
  · exact rc23_1_0
  · exact rc23_1_50115
  · exact rc23_1_50115
  · exact rc23_1_0
  · exact rc23_1_38505
  · exact rc23_1_43605
  · exact rc23_1_38505
  · exact rc23_1_43605
  · exact rc23_1_50115
  · exact rc23_1_0

private theorem rc23_2_33410 : rowCube23 2 33410 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33410 ![0,50115,43690,38550,43690,38550,0,50115,0,50115,43690,38550,43690,38550,0,50115] ![16,0,0,0,0,0,16,0,16,0,0,0,0,0,16,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_50115
  · exact rc23_1_43690
  · exact rc23_1_38550
  · exact rc23_1_43690
  · exact rc23_1_38550
  · exact rc23_1_0
  · exact rc23_1_50115
  · exact rc23_1_0
  · exact rc23_1_50115
  · exact rc23_1_43690
  · exact rc23_1_38550
  · exact rc23_1_43690
  · exact rc23_1_38550
  · exact rc23_1_0
  · exact rc23_1_50115

private theorem rc23_2_33810 : rowCube23 2 33810 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33810 ![0,52275,42330,38550,52275,0,38550,42330,38550,42330,52275,0,42330,38550,0,52275] ![16,0,0,0,0,16,0,0,0,0,0,16,0,0,16,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_52275
  · exact rc23_1_42330
  · exact rc23_1_38550
  · exact rc23_1_52275
  · exact rc23_1_0
  · exact rc23_1_38550
  · exact rc23_1_42330
  · exact rc23_1_38550
  · exact rc23_1_42330
  · exact rc23_1_52275
  · exact rc23_1_0
  · exact rc23_1_42330
  · exact rc23_1_38550
  · exact rc23_1_0
  · exact rc23_1_52275

private theorem rc23_2_33825 : rowCube23 2 33825 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33825 ![0,52275,42405,38505,52275,0,38505,42405,42405,38505,0,52275,38505,42405,52275,0] ![16,0,0,0,0,16,0,0,0,0,16,0,0,0,0,16] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_52275
  · exact rc23_1_42405
  · exact rc23_1_38505
  · exact rc23_1_52275
  · exact rc23_1_0
  · exact rc23_1_38505
  · exact rc23_1_42405
  · exact rc23_1_42405
  · exact rc23_1_38505
  · exact rc23_1_0
  · exact rc23_1_52275
  · exact rc23_1_38505
  · exact rc23_1_42405
  · exact rc23_1_52275
  · exact rc23_1_0

private theorem rc23_2_33864 : rowCube23 2 33864 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33864 ![0,52428,42330,38505,52428,0,38505,42330,52428,0,38505,42330,0,52428,42330,38505] ![16,0,0,0,0,16,0,0,0,16,0,0,16,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_52428
  · exact rc23_1_42330
  · exact rc23_1_38505
  · exact rc23_1_52428
  · exact rc23_1_0
  · exact rc23_1_38505
  · exact rc23_1_42330
  · exact rc23_1_52428
  · exact rc23_1_0
  · exact rc23_1_38505
  · exact rc23_1_42330
  · exact rc23_1_0
  · exact rc23_1_52428
  · exact rc23_1_42330
  · exact rc23_1_38505

private theorem rc23_2_33924 : rowCube23 2 33924 = (64:ℝ)/16^2 := by
  apply rowStep23 1 33924 ![0,52428,42405,38550,52428,0,38550,42405,0,52428,42405,38550,52428,0,38550,42405] ![16,0,0,0,0,16,0,0,16,0,0,0,0,16,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_52428
  · exact rc23_1_42405
  · exact rc23_1_38550
  · exact rc23_1_52428
  · exact rc23_1_0
  · exact rc23_1_38550
  · exact rc23_1_42405
  · exact rc23_1_0
  · exact rc23_1_52428
  · exact rc23_1_42405
  · exact rc23_1_38550
  · exact rc23_1_52428
  · exact rc23_1_0
  · exact rc23_1_38550
  · exact rc23_1_42405

private theorem rc23_2_34833 : rowCube23 2 34833 = (64:ℝ)/16^2 := by
  apply rowStep23 1 34833 ![0,52275,43605,39321,0,52275,43605,39321,39321,43605,52275,0,39321,43605,52275,0] ![16,0,0,0,16,0,0,0,0,0,0,16,0,0,0,16] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_52275
  · exact rc23_1_43605
  · exact rc23_1_39321
  · exact rc23_1_0
  · exact rc23_1_52275
  · exact rc23_1_43605
  · exact rc23_1_39321
  · exact rc23_1_39321
  · exact rc23_1_43605
  · exact rc23_1_52275
  · exact rc23_1_0
  · exact rc23_1_39321
  · exact rc23_1_43605
  · exact rc23_1_52275
  · exact rc23_1_0

private theorem rc23_2_34850 : rowCube23 2 34850 = (64:ℝ)/16^2 := by
  apply rowStep23 1 34850 ![0,52275,43690,39270,0,52275,43690,39270,43690,39270,0,52275,43690,39270,0,52275] ![16,0,0,0,16,0,0,0,0,0,16,0,0,0,16,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_52275
  · exact rc23_1_43690
  · exact rc23_1_39270
  · exact rc23_1_0
  · exact rc23_1_52275
  · exact rc23_1_43690
  · exact rc23_1_39270
  · exact rc23_1_43690
  · exact rc23_1_39270
  · exact rc23_1_0
  · exact rc23_1_52275
  · exact rc23_1_43690
  · exact rc23_1_39270
  · exact rc23_1_0
  · exact rc23_1_52275

private theorem rc23_2_34884 : rowCube23 2 34884 = (64:ℝ)/16^2 := by
  apply rowStep23 1 34884 ![0,52428,43605,39270,0,52428,43605,39270,52428,0,39270,43605,52428,0,39270,43605] ![16,0,0,0,16,0,0,0,0,16,0,0,0,16,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_52428
  · exact rc23_1_43605
  · exact rc23_1_39270
  · exact rc23_1_0
  · exact rc23_1_52428
  · exact rc23_1_43605
  · exact rc23_1_39270
  · exact rc23_1_52428
  · exact rc23_1_0
  · exact rc23_1_39270
  · exact rc23_1_43605
  · exact rc23_1_52428
  · exact rc23_1_0
  · exact rc23_1_39270
  · exact rc23_1_43605

private theorem rc23_2_34952 : rowCube23 2 34952 = (64:ℝ)/16^2 := by
  apply rowStep23 1 34952 ![0,52428,43690,39321,0,52428,43690,39321,0,52428,43690,39321,0,52428,43690,39321] ![16,0,0,0,16,0,0,0,16,0,0,0,16,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_52428
  · exact rc23_1_43690
  · exact rc23_1_39321
  · exact rc23_1_0
  · exact rc23_1_52428
  · exact rc23_1_43690
  · exact rc23_1_39321
  · exact rc23_1_0
  · exact rc23_1_52428
  · exact rc23_1_43690
  · exact rc23_1_39321
  · exact rc23_1_0
  · exact rc23_1_52428
  · exact rc23_1_43690
  · exact rc23_1_39321

private theorem rc23_2_36870 : rowCube23 2 36870 = (64:ℝ)/16^2 := by
  apply rowStep23 1 36870 ![0,61455,61455,0,39270,38550,38550,39270,38550,39270,39270,38550,61455,0,0,61455] ![16,0,0,16,0,0,0,0,0,0,0,0,0,16,16,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_61455
  · exact rc23_1_0
  · exact rc23_1_39270
  · exact rc23_1_38550
  · exact rc23_1_38550
  · exact rc23_1_39270
  · exact rc23_1_38550
  · exact rc23_1_39270
  · exact rc23_1_39270
  · exact rc23_1_38550
  · exact rc23_1_61455
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_61455

private theorem rc23_2_36873 : rowCube23 2 36873 = (64:ℝ)/16^2 := by
  apply rowStep23 1 36873 ![0,61455,61455,0,39321,38505,38505,39321,39321,38505,38505,39321,0,61455,61455,0] ![16,0,0,16,0,0,0,0,0,0,0,0,16,0,0,16] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_61455
  · exact rc23_1_0
  · exact rc23_1_39321
  · exact rc23_1_38505
  · exact rc23_1_38505
  · exact rc23_1_39321
  · exact rc23_1_39321
  · exact rc23_1_38505
  · exact rc23_1_38505
  · exact rc23_1_39321
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_61455
  · exact rc23_1_0

private theorem rc23_2_36960 : rowCube23 2 36960 = (64:ℝ)/16^2 := by
  apply rowStep23 1 36960 ![0,61680,61680,0,39270,38505,38505,39270,61680,0,0,61680,38505,39270,39270,38505] ![16,0,0,16,0,0,0,0,0,16,16,0,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_61680
  · exact rc23_1_0
  · exact rc23_1_39270
  · exact rc23_1_38505
  · exact rc23_1_38505
  · exact rc23_1_39270
  · exact rc23_1_61680
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_38505
  · exact rc23_1_39270
  · exact rc23_1_39270
  · exact rc23_1_38505

private theorem rc23_2_37008 : rowCube23 2 37008 = (64:ℝ)/16^2 := by
  apply rowStep23 1 37008 ![0,61680,61680,0,39321,38550,38550,39321,0,61680,61680,0,39321,38550,38550,39321] ![16,0,0,16,0,0,0,0,16,0,0,16,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_61680
  · exact rc23_1_0
  · exact rc23_1_39321
  · exact rc23_1_38550
  · exact rc23_1_38550
  · exact rc23_1_39321
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_61680
  · exact rc23_1_0
  · exact rc23_1_39321
  · exact rc23_1_38550
  · exact rc23_1_38550
  · exact rc23_1_39321

private theorem rc23_2_38400 : rowCube23 2 38400 = (64:ℝ)/16^2 := by
  apply rowStep23 1 38400 ![0,65280,65280,0,65280,0,0,65280,38550,38505,38505,38550,38505,38550,38550,38505] ![16,0,0,16,0,16,16,0,0,0,0,0,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_38550
  · exact rc23_1_38505
  · exact rc23_1_38505
  · exact rc23_1_38550
  · exact rc23_1_38505
  · exact rc23_1_38550
  · exact rc23_1_38550
  · exact rc23_1_38505

private theorem rc23_2_39168 : rowCube23 2 39168 = (64:ℝ)/16^2 := by
  apply rowStep23 1 39168 ![0,65280,65280,0,0,65280,65280,0,39321,39270,39270,39321,39321,39270,39270,39321] ![16,0,0,16,16,0,0,16,0,0,0,0,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_39321
  · exact rc23_1_39270
  · exact rc23_1_39270
  · exact rc23_1_39321
  · exact rc23_1_39321
  · exact rc23_1_39270
  · exact rc23_1_39270
  · exact rc23_1_39321

private theorem rc23_2_40965 : rowCube23 2 40965 = (64:ℝ)/16^2 := by
  apply rowStep23 1 40965 ![0,61455,0,61455,43605,42405,43605,42405,42405,43605,42405,43605,61455,0,61455,0] ![16,0,16,0,0,0,0,0,0,0,0,0,0,16,0,16] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_43605
  · exact rc23_1_42405
  · exact rc23_1_43605
  · exact rc23_1_42405
  · exact rc23_1_42405
  · exact rc23_1_43605
  · exact rc23_1_42405
  · exact rc23_1_43605
  · exact rc23_1_61455
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_0

private theorem rc23_2_40970 : rowCube23 2 40970 = (64:ℝ)/16^2 := by
  apply rowStep23 1 40970 ![0,61455,0,61455,43690,42330,43690,42330,43690,42330,43690,42330,0,61455,0,61455] ![16,0,16,0,0,0,0,0,0,0,0,0,16,0,16,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_43690
  · exact rc23_1_42330
  · exact rc23_1_43690
  · exact rc23_1_42330
  · exact rc23_1_43690
  · exact rc23_1_42330
  · exact rc23_1_43690
  · exact rc23_1_42330
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_0
  · exact rc23_1_61455

private theorem rc23_2_41040 : rowCube23 2 41040 = (64:ℝ)/16^2 := by
  apply rowStep23 1 41040 ![0,61680,0,61680,43605,42330,43605,42330,61680,0,61680,0,42330,43605,42330,43605] ![16,0,16,0,0,0,0,0,0,16,0,16,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_43605
  · exact rc23_1_42330
  · exact rc23_1_43605
  · exact rc23_1_42330
  · exact rc23_1_61680
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_0
  · exact rc23_1_42330
  · exact rc23_1_43605
  · exact rc23_1_42330
  · exact rc23_1_43605

private theorem rc23_2_41120 : rowCube23 2 41120 = (64:ℝ)/16^2 := by
  apply rowStep23 1 41120 ![0,61680,0,61680,43690,42405,43690,42405,0,61680,0,61680,43690,42405,43690,42405] ![16,0,16,0,0,0,0,0,16,0,16,0,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_43690
  · exact rc23_1_42405
  · exact rc23_1_43690
  · exact rc23_1_42405
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_43690
  · exact rc23_1_42405
  · exact rc23_1_43690
  · exact rc23_1_42405

private theorem rc23_2_42240 : rowCube23 2 42240 = (64:ℝ)/16^2 := by
  apply rowStep23 1 42240 ![0,65280,0,65280,65280,0,65280,0,42405,42330,42405,42330,42330,42405,42330,42405] ![16,0,16,0,0,16,0,16,0,0,0,0,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_42405
  · exact rc23_1_42330
  · exact rc23_1_42405
  · exact rc23_1_42330
  · exact rc23_1_42330
  · exact rc23_1_42405
  · exact rc23_1_42330
  · exact rc23_1_42405

private theorem rc23_2_43520 : rowCube23 2 43520 = (64:ℝ)/16^2 := by
  apply rowStep23 1 43520 ![0,65280,0,65280,0,65280,0,65280,43690,43605,43690,43605,43690,43605,43690,43605] ![16,0,16,0,16,0,16,0,0,0,0,0,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_43690
  · exact rc23_1_43605
  · exact rc23_1_43690
  · exact rc23_1_43605
  · exact rc23_1_43690
  · exact rc23_1_43605
  · exact rc23_1_43690
  · exact rc23_1_43605

private theorem rc23_2_49155 : rowCube23 2 49155 = (64:ℝ)/16^2 := by
  apply rowStep23 1 49155 ![0,0,61455,61455,52275,52275,50115,50115,50115,50115,52275,52275,61455,61455,0,0] ![16,16,0,0,0,0,0,0,0,0,0,0,0,0,16,16] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_61455
  · exact rc23_1_52275
  · exact rc23_1_52275
  · exact rc23_1_50115
  · exact rc23_1_50115
  · exact rc23_1_50115
  · exact rc23_1_50115
  · exact rc23_1_52275
  · exact rc23_1_52275
  · exact rc23_1_61455
  · exact rc23_1_61455
  · exact rc23_1_0
  · exact rc23_1_0

private theorem rc23_2_49164 : rowCube23 2 49164 = (64:ℝ)/16^2 := by
  apply rowStep23 1 49164 ![0,0,61455,61455,52428,52428,49980,49980,52428,52428,49980,49980,0,0,61455,61455] ![16,16,0,0,0,0,0,0,0,0,0,0,16,16,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_61455
  · exact rc23_1_52428
  · exact rc23_1_52428
  · exact rc23_1_49980
  · exact rc23_1_49980
  · exact rc23_1_52428
  · exact rc23_1_52428
  · exact rc23_1_49980
  · exact rc23_1_49980
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_61455
  · exact rc23_1_61455

private theorem rc23_2_49200 : rowCube23 2 49200 = (64:ℝ)/16^2 := by
  apply rowStep23 1 49200 ![0,0,61680,61680,52275,52275,49980,49980,61680,61680,0,0,49980,49980,52275,52275] ![16,16,0,0,0,0,0,0,0,0,16,16,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_61680
  · exact rc23_1_52275
  · exact rc23_1_52275
  · exact rc23_1_49980
  · exact rc23_1_49980
  · exact rc23_1_61680
  · exact rc23_1_61680
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_49980
  · exact rc23_1_49980
  · exact rc23_1_52275
  · exact rc23_1_52275

private theorem rc23_2_49344 : rowCube23 2 49344 = (64:ℝ)/16^2 := by
  apply rowStep23 1 49344 ![0,0,61680,61680,52428,52428,50115,50115,0,0,61680,61680,52428,52428,50115,50115] ![16,16,0,0,0,0,0,0,16,16,0,0,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_61680
  · exact rc23_1_52428
  · exact rc23_1_52428
  · exact rc23_1_50115
  · exact rc23_1_50115
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_61680
  · exact rc23_1_61680
  · exact rc23_1_52428
  · exact rc23_1_52428
  · exact rc23_1_50115
  · exact rc23_1_50115

private theorem rc23_2_49920 : rowCube23 2 49920 = (64:ℝ)/16^2 := by
  apply rowStep23 1 49920 ![0,0,65280,65280,65280,65280,0,0,50115,50115,49980,49980,49980,49980,50115,50115] ![16,16,0,0,0,0,16,16,0,0,0,0,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_50115
  · exact rc23_1_50115
  · exact rc23_1_49980
  · exact rc23_1_49980
  · exact rc23_1_49980
  · exact rc23_1_49980
  · exact rc23_1_50115
  · exact rc23_1_50115

private theorem rc23_2_52224 : rowCube23 2 52224 = (64:ℝ)/16^2 := by
  apply rowStep23 1 52224 ![0,0,65280,65280,0,0,65280,65280,52428,52428,52275,52275,52428,52428,52275,52275] ![16,16,0,0,16,16,0,0,0,0,0,0,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_52428
  · exact rc23_1_52428
  · exact rc23_1_52275
  · exact rc23_1_52275
  · exact rc23_1_52428
  · exact rc23_1_52428
  · exact rc23_1_52275
  · exact rc23_1_52275

private theorem rc23_2_61440 : rowCube23 2 61440 = (64:ℝ)/16^2 := by
  apply rowStep23 1 61440 ![0,0,0,0,65280,65280,65280,65280,61680,61680,61680,61680,61455,61455,61455,61455] ![16,16,16,16,0,0,0,0,0,0,0,0,0,0,0,0] 64 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_0
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_65280
  · exact rc23_1_61680
  · exact rc23_1_61680
  · exact rc23_1_61680
  · exact rc23_1_61680
  · exact rc23_1_61455
  · exact rc23_1_61455
  · exact rc23_1_61455
  · exact rc23_1_61455

private theorem rc23_3_0 : rowCube23 3 0 = (4096:ℝ)/16^3 := by
  apply rowStep23 2 0 ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] ![256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256] 4096 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_0

private theorem rc23_3_32769 : rowCube23 3 32769 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 32769 ![0,49155,40965,36873,34833,33825,33345,33153,33153,33345,33825,34833,36873,40965,49155,0] ![256,64,64,64,64,64,64,64,64,64,64,64,64,64,64,256] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_49155
  · exact rc23_2_40965
  · exact rc23_2_36873
  · exact rc23_2_34833
  · exact rc23_2_33825
  · exact rc23_2_33345
  · exact rc23_2_33153
  · exact rc23_2_33153
  · exact rc23_2_33345
  · exact rc23_2_33825
  · exact rc23_2_34833
  · exact rc23_2_36873
  · exact rc23_2_40965
  · exact rc23_2_49155
  · exact rc23_2_0

private theorem rc23_3_32770 : rowCube23 3 32770 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 32770 ![0,49155,40970,36870,34850,33810,33410,33090,33410,33090,34850,33810,40970,36870,0,49155] ![256,64,64,64,64,64,64,64,64,64,64,64,64,64,256,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_49155
  · exact rc23_2_40970
  · exact rc23_2_36870
  · exact rc23_2_34850
  · exact rc23_2_33810
  · exact rc23_2_33410
  · exact rc23_2_33090
  · exact rc23_2_33410
  · exact rc23_2_33090
  · exact rc23_2_34850
  · exact rc23_2_33810
  · exact rc23_2_40970
  · exact rc23_2_36870
  · exact rc23_2_0
  · exact rc23_2_49155

private theorem rc23_3_32772 : rowCube23 3 32772 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 32772 ![0,49164,40965,36870,34884,33924,33300,33060,33924,34884,33060,33300,49164,0,36870,40965] ![256,64,64,64,64,64,64,64,64,64,64,64,64,256,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_49164
  · exact rc23_2_40965
  · exact rc23_2_36870
  · exact rc23_2_34884
  · exact rc23_2_33924
  · exact rc23_2_33300
  · exact rc23_2_33060
  · exact rc23_2_33924
  · exact rc23_2_34884
  · exact rc23_2_33060
  · exact rc23_2_33300
  · exact rc23_2_49164
  · exact rc23_2_0
  · exact rc23_2_36870
  · exact rc23_2_40965

private theorem rc23_3_32776 : rowCube23 3 32776 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 32776 ![0,49164,40970,36873,34952,33864,33320,33048,34952,33864,33320,33048,0,49164,40970,36873] ![256,64,64,64,64,64,64,64,64,64,64,64,256,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_49164
  · exact rc23_2_40970
  · exact rc23_2_36873
  · exact rc23_2_34952
  · exact rc23_2_33864
  · exact rc23_2_33320
  · exact rc23_2_33048
  · exact rc23_2_34952
  · exact rc23_2_33864
  · exact rc23_2_33320
  · exact rc23_2_33048
  · exact rc23_2_0
  · exact rc23_2_49164
  · exact rc23_2_40970
  · exact rc23_2_36873

private theorem rc23_3_32784 : rowCube23 3 32784 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 32784 ![0,49200,41040,37008,34833,33810,33300,33048,37008,41040,49200,0,33048,33300,33810,34833] ![256,64,64,64,64,64,64,64,64,64,64,256,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_49200
  · exact rc23_2_41040
  · exact rc23_2_37008
  · exact rc23_2_34833
  · exact rc23_2_33810
  · exact rc23_2_33300
  · exact rc23_2_33048
  · exact rc23_2_37008
  · exact rc23_2_41040
  · exact rc23_2_49200
  · exact rc23_2_0
  · exact rc23_2_33048
  · exact rc23_2_33300
  · exact rc23_2_33810
  · exact rc23_2_34833

private theorem rc23_3_32800 : rowCube23 3 32800 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 32800 ![0,49200,41120,36960,34850,33825,33320,33060,41120,36960,0,49200,33320,33060,34850,33825] ![256,64,64,64,64,64,64,64,64,64,256,64,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_49200
  · exact rc23_2_41120
  · exact rc23_2_36960
  · exact rc23_2_34850
  · exact rc23_2_33825
  · exact rc23_2_33320
  · exact rc23_2_33060
  · exact rc23_2_41120
  · exact rc23_2_36960
  · exact rc23_2_0
  · exact rc23_2_49200
  · exact rc23_2_33320
  · exact rc23_2_33060
  · exact rc23_2_34850
  · exact rc23_2_33825

private theorem rc23_3_32832 : rowCube23 3 32832 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 32832 ![0,49344,41040,36960,34884,33864,33345,33090,49344,0,36960,41040,33864,34884,33090,33345] ![256,64,64,64,64,64,64,64,64,256,64,64,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_49344
  · exact rc23_2_41040
  · exact rc23_2_36960
  · exact rc23_2_34884
  · exact rc23_2_33864
  · exact rc23_2_33345
  · exact rc23_2_33090
  · exact rc23_2_49344
  · exact rc23_2_0
  · exact rc23_2_36960
  · exact rc23_2_41040
  · exact rc23_2_33864
  · exact rc23_2_34884
  · exact rc23_2_33090
  · exact rc23_2_33345

private theorem rc23_3_32896 : rowCube23 3 32896 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 32896 ![0,49344,41120,37008,34952,33924,33410,33153,0,49344,41120,37008,34952,33924,33410,33153] ![256,64,64,64,64,64,64,64,256,64,64,64,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_49344
  · exact rc23_2_41120
  · exact rc23_2_37008
  · exact rc23_2_34952
  · exact rc23_2_33924
  · exact rc23_2_33410
  · exact rc23_2_33153
  · exact rc23_2_0
  · exact rc23_2_49344
  · exact rc23_2_41120
  · exact rc23_2_37008
  · exact rc23_2_34952
  · exact rc23_2_33924
  · exact rc23_2_33410
  · exact rc23_2_33153

private theorem rc23_3_33024 : rowCube23 3 33024 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 33024 ![0,49920,42240,39168,39168,42240,49920,0,33153,33090,33060,33048,33048,33060,33090,33153] ![256,64,64,64,64,64,64,256,64,64,64,64,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_49920
  · exact rc23_2_42240
  · exact rc23_2_39168
  · exact rc23_2_39168
  · exact rc23_2_42240
  · exact rc23_2_49920
  · exact rc23_2_0
  · exact rc23_2_33153
  · exact rc23_2_33090
  · exact rc23_2_33060
  · exact rc23_2_33048
  · exact rc23_2_33048
  · exact rc23_2_33060
  · exact rc23_2_33090
  · exact rc23_2_33153

private theorem rc23_3_33280 : rowCube23 3 33280 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 33280 ![0,49920,43520,38400,43520,38400,0,49920,33410,33345,33320,33300,33320,33300,33410,33345] ![256,64,64,64,64,64,256,64,64,64,64,64,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_49920
  · exact rc23_2_43520
  · exact rc23_2_38400
  · exact rc23_2_43520
  · exact rc23_2_38400
  · exact rc23_2_0
  · exact rc23_2_49920
  · exact rc23_2_33410
  · exact rc23_2_33345
  · exact rc23_2_33320
  · exact rc23_2_33300
  · exact rc23_2_33320
  · exact rc23_2_33300
  · exact rc23_2_33410
  · exact rc23_2_33345

private theorem rc23_3_33792 : rowCube23 3 33792 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 33792 ![0,52224,42240,38400,52224,0,38400,42240,33924,33864,33825,33810,33864,33924,33810,33825] ![256,64,64,64,64,256,64,64,64,64,64,64,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_52224
  · exact rc23_2_42240
  · exact rc23_2_38400
  · exact rc23_2_52224
  · exact rc23_2_0
  · exact rc23_2_38400
  · exact rc23_2_42240
  · exact rc23_2_33924
  · exact rc23_2_33864
  · exact rc23_2_33825
  · exact rc23_2_33810
  · exact rc23_2_33864
  · exact rc23_2_33924
  · exact rc23_2_33810
  · exact rc23_2_33825

private theorem rc23_3_34816 : rowCube23 3 34816 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 34816 ![0,52224,43520,39168,0,52224,43520,39168,34952,34884,34850,34833,34952,34884,34850,34833] ![256,64,64,64,256,64,64,64,64,64,64,64,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_52224
  · exact rc23_2_43520
  · exact rc23_2_39168
  · exact rc23_2_0
  · exact rc23_2_52224
  · exact rc23_2_43520
  · exact rc23_2_39168
  · exact rc23_2_34952
  · exact rc23_2_34884
  · exact rc23_2_34850
  · exact rc23_2_34833
  · exact rc23_2_34952
  · exact rc23_2_34884
  · exact rc23_2_34850
  · exact rc23_2_34833

private theorem rc23_3_36864 : rowCube23 3 36864 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 36864 ![0,61440,61440,0,39168,38400,38400,39168,37008,36960,36960,37008,36873,36870,36870,36873] ![256,64,64,256,64,64,64,64,64,64,64,64,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_61440
  · exact rc23_2_61440
  · exact rc23_2_0
  · exact rc23_2_39168
  · exact rc23_2_38400
  · exact rc23_2_38400
  · exact rc23_2_39168
  · exact rc23_2_37008
  · exact rc23_2_36960
  · exact rc23_2_36960
  · exact rc23_2_37008
  · exact rc23_2_36873
  · exact rc23_2_36870
  · exact rc23_2_36870
  · exact rc23_2_36873

private theorem rc23_3_40960 : rowCube23 3 40960 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 40960 ![0,61440,0,61440,43520,42240,43520,42240,41120,41040,41120,41040,40970,40965,40970,40965] ![256,64,256,64,64,64,64,64,64,64,64,64,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_61440
  · exact rc23_2_0
  · exact rc23_2_61440
  · exact rc23_2_43520
  · exact rc23_2_42240
  · exact rc23_2_43520
  · exact rc23_2_42240
  · exact rc23_2_41120
  · exact rc23_2_41040
  · exact rc23_2_41120
  · exact rc23_2_41040
  · exact rc23_2_40970
  · exact rc23_2_40965
  · exact rc23_2_40970
  · exact rc23_2_40965

private theorem rc23_3_49152 : rowCube23 3 49152 = (1408:ℝ)/16^3 := by
  apply rowStep23 2 49152 ![0,0,61440,61440,52224,52224,49920,49920,49344,49344,49200,49200,49164,49164,49155,49155] ![256,256,64,64,64,64,64,64,64,64,64,64,64,64,64,64] 1408 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_2_0
  · exact rc23_2_0
  · exact rc23_2_61440
  · exact rc23_2_61440
  · exact rc23_2_52224
  · exact rc23_2_52224
  · exact rc23_2_49920
  · exact rc23_2_49920
  · exact rc23_2_49344
  · exact rc23_2_49344
  · exact rc23_2_49200
  · exact rc23_2_49200
  · exact rc23_2_49164
  · exact rc23_2_49164
  · exact rc23_2_49155
  · exact rc23_2_49155

private theorem rc23_4_32768 : rowCube23 4 32768 = (25216:ℝ)/16^4 := by
  apply rowStep23 3 32768 ![0,49152,40960,36864,34816,33792,33280,33024,32896,32832,32800,32784,32776,32772,32770,32769] ![4096,1408,1408,1408,1408,1408,1408,1408,1408,1408,1408,1408,1408,1408,1408,1408] 25216 (by decide) ?_ (by decide)
  intro a
  fin_cases a
  · exact rc23_3_0
  · exact rc23_3_49152
  · exact rc23_3_40960
  · exact rc23_3_36864
  · exact rc23_3_34816
  · exact rc23_3_33792
  · exact rc23_3_33280
  · exact rc23_3_33024
  · exact rc23_3_32896
  · exact rc23_3_32832
  · exact rc23_3_32800
  · exact rc23_3_32784
  · exact rc23_3_32776
  · exact rc23_3_32772
  · exact rc23_3_32770
  · exact rc23_3_32769

theorem scalar_cube23 : cube23 plusRow23 4 (fun x=>sign23 (mono23 x)) = 197/512 := by
  have e : mono23=mask23 32768 := funext (by decide)
  rw [e]
  change rowCube23 4 32768=_
  rw [rc23_4_32768]
  norm_num
end
end PEqualNP.Outside.L_meta_25623_aux

namespace PEqualNP.Outside.L_meta_25623_aux

theorem fullBlockLocal23 {p : ℕ}
    (hblock : cube23 plusRow23 4 (fun x=>sign23 (mono23 x)) = 197/512)
    (f : PKBlock23 p → Bool) (hc : cubic pkBlockAdd (fun z=>xor (f z) (pkBlockTarget z))) :
    8^p*(∑ z, agreementSign false (f z)).natAbs^4 ≤ 7^p*(Fintype.card (PKBlock23 p))^4 := by
  classical
  have eqTarget : target23 (p:=p) (fun _=>true) = pkBlockTarget := by
    funext z
    simp [target23,pkBlockTarget,mono23]
  have hcp (v : Fin 4 → PKBlock23 p) (x : PKBlock23 p) :
      (List.ofFn v).foldl (bd23 plusBlock23) (fun y=>xor (f y) (target23 (fun _=>true) y)) x = false := by
    rw [eqTarget]
    exact hc v x
  have H := cubicBias23 (fun _=>true) f hcp hblock
  have hs (b : Bool) : (agreementSign false b : ℝ) = sign23 b := by
    cases b <;> norm_num [agreementSign,sign23]
  apply fourthFromMean23
  simpa [hs] using H

end PEqualNP.Outside.L_meta_25623_aux

open PEqualNP.Outside.L_meta_25623_aux

theorem PEqualNP.Outside.L_meta_25623 : (∀ (k d : ℕ) (hk : 0 < k), (d = 1 ∨ d = 2) → 4 * d + 4 < k →
  let W := Fin k → Bool
  let idx := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (i : Fin k) => xor (x i) (y i)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (idx (i.val + k - s % k))
  let mix := fun (x : W) (i : Fin k) =>
    xor (xor (x i) (x (idx (i.val + d)))) (x (idx (i.val + k - d)))
  let step := fun (x : W) (i : Fin k) =>
    xor (x i) (!(x (idx (i.val + 1))) && x (idx (i.val + 2)))
  let diff := fun (f : W → Bool) (v x : W) => xor (f x) (f (add x v))
  let stride := 4 * d + 5
  ∀ (s t h : ℕ) (name c₁ c₂ mask : W),
    let observed := fun (key : W) =>
      let initial := mix (add (rot s key) name)
      let middle := add (step initial) (add (rot t key) c₁)
      let out := add (step (mix middle)) (add (rot h key) c₂)
      (List.ofFn (fun bit : Fin k => mask bit && out bit)).foldl xor false
    let weight := (Finset.univ.filter (fun bit : Fin k => mask bit = true)).card
    let packed := ((k / stride) * weight + k - 1) / k
    ∀ (n : ℕ) (leaf : W → Fin n) (query : Fin n → W → W) (answer : Fin n → W)
      (model : Fin n → W → Bool),
      (∀ b x y, query b (add x y) = add (query b x) (query b y)) →
      (∀ b x, leaf x = b ↔ query b x = answer b) →
      (∀ b (v : Fin 4 → W) x, (List.ofFn v).foldl diff (model b) x = false) →
      let signed := Finset.univ.sum (fun sample : W =>
        if observed sample = model (leaf sample) sample then (1 : ℤ) else -1)
      (8 ^ packed * signed.natAbs ^ 4 ≤ 7 ^ packed * (n * 2 ^ k) ^ 4) ∧
      ((∀ x, observed x = model (leaf x) x) → 2 ^ packed ≤ n)) := by
  intro k d hk hd hw
  dsimp only
  intro s t h name c1 c2 mask n leaf query answer model hlin hleaf hm
  obtain ⟨E,hE,low⟩ := RawGrid.embeddedCube k d hk hd hw s t h name c1 c2 mask
  let obs := RawGrid.obs hk d s t h name c1 c2 mask
  exact ⟨globalBound E hE obs low leaf query answer model hlin hleaf hm
    (fullBlockLocal23 scalar_cube23), Leaves.exact_from_cube E hE obs low leaf query answer model hlin hleaf hm⟩
