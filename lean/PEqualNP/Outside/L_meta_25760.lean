import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25760_aux

abbrev W (k : ℕ) := Fin k → ZMod 2

def ixFn (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k :=
  ⟨n % k, Nat.mod_lt _ hk⟩

def rotFn (k : ℕ) (hk : 0 < k) (offset : ℕ) (w : W k) (j : Fin k) : ZMod 2 :=
  w (ixFn k hk (j.val + k - offset % k))

def mixFn (k d : ℕ) (hk : 0 < k) (word : W k) (mid : Fin k) : ZMod 2 :=
  word mid + word (ixFn k hk (mid.val + d)) + word (ixFn k hk (mid.val + k - d % k))

def chiFn (k : ℕ) (hk : 0 < k) (z : W k) (dest : Fin k) : ZMod 2 :=
  z dest + (1 + z (ixFn k hk (dest.val + 1))) * z (ixFn k hk (dest.val + 2))

def polarFn (k : ℕ) (hk : 0 < k) (x y : W k) (site : Fin k) : ZMod 2 :=
  x (ixFn k hk (site.val + 1)) * y (ixFn k hk (site.val + 2)) +
  x (ixFn k hk (site.val + 2)) * y (ixFn k hk (site.val + 1))

def tickFn (k d : ℕ) (hk : 0 < k) (feed : ℕ → ℕ) (tickNo : ℕ) (key state : W k) : W k :=
  chiFn k hk (mixFn k d hk state) + rotFn k hk (feed tickNo) key

def runFn (k d q : ℕ) (hk : 0 < k) (start : ℕ) (feed : ℕ → ℕ)
    (name finalConst : W k) (schedule : Fin q → W k) (key : W k) : W k :=
  tickFn k d hk feed q key ((List.finRange q).foldl
    (fun prev idx => tickFn k d hk feed idx.val key prev + schedule idx)
    (rotFn k hk start key + name)) + finalConst

theorem z2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

theorem vec_add_self {k : ℕ} (x : W k) : x + x = 0 := by
  funext i
  exact z2_add_self (x i)

theorem vec_four_eq_zero {k : ℕ} (x : W k) : x + x + x + x = 0 := by
  funext i
  have h : ∀ a : ZMod 2, a + a + a + a = 0 := by decide
  exact h (x i)

theorem rotFn_add (k : ℕ) (hk : 0 < k) (offset : ℕ) (a b : W k) :
    rotFn k hk offset (a + b) = rotFn k hk offset a + rotFn k hk offset b := by
  funext j
  rfl

theorem mixFn_add (k d : ℕ) (hk : 0 < k) (a b : W k) :
    mixFn k d hk (a + b) = mixFn k d hk a + mixFn k d hk b := by
  funext j
  simp only [mixFn, Pi.add_apply]
  ring

theorem mixFn_zero (k d : ℕ) (hk : 0 < k) :
    mixFn k d hk 0 = 0 := by
  funext j
  simp [mixFn]

theorem mixFn_sum {ι : Type*} (k d : ℕ) (hk : 0 < k) (s : Finset ι) (f : ι → W k) :
    mixFn k d hk (∑ i ∈ s, f i) = ∑ i ∈ s, mixFn k d hk (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mixFn_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, mixFn_add, ih]

theorem polarFn_add_left (k : ℕ) (hk : 0 < k) (a b y : W k) :
    polarFn k hk (a + b) y = polarFn k hk a y + polarFn k hk b y := by
  funext j
  simp only [polarFn, Pi.add_apply]
  ring

theorem polarFn_zero_left (k : ℕ) (hk : 0 < k) (y : W k) :
    polarFn k hk 0 y = 0 := by
  funext j
  simp [polarFn]

theorem polarFn_sum_left {ι : Type*} (k : ℕ) (hk : 0 < k) (s : Finset ι) (f : ι → W k) (y : W k) :
    polarFn k hk (∑ i ∈ s, f i) y = ∑ i ∈ s, polarFn k hk (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polarFn_zero_left]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, polarFn_add_left, ih]

theorem chiFn_add (k : ℕ) (hk : 0 < k) (a b : W k) :
    chiFn k hk (a + b) = chiFn k hk a + chiFn k hk b + polarFn k hk a b := by
  funext dest
  simp only [chiFn, polarFn, Pi.add_apply]
  have h : ∀ a0 a1 a2 b0 b1 b2 : ZMod 2,
      (a0 + b0) + (1 + (a1 + b1)) * (a2 + b2) =
      (a0 + (1 + a1) * a2) + (b0 + (1 + b1) * b2) + (a1 * b2 + a2 * b1) := by decide
  exact h (a dest) (a (ixFn k hk (dest.val + 1))) (a (ixFn k hk (dest.val + 2)))
    (b dest) (b (ixFn k hk (dest.val + 1))) (b (ixFn k hk (dest.val + 2)))

theorem chiFn_add_cancel (k : ℕ) (hk : 0 < k) (a b : W k) :
    chiFn k hk (a + b) + chiFn k hk a = chiFn k hk b + polarFn k hk a b := by
  rw [chiFn_add]
  funext dest
  simp only [Pi.add_apply]
  have h : ∀ x y z : ZMod 2, x + y + z + x = y + z := by decide
  exact h (chiFn k hk a dest) (chiFn k hk b dest) (polarFn k hk a b dest)

theorem chiFn_second_diff (k : ℕ) (hk : 0 < k) (z a b : W k) :
    chiFn k hk (z + a + b) + chiFn k hk (z + a) + chiFn k hk (z + b) + chiFn k hk z =
      polarFn k hk a b := by
  rw [chiFn_add_cancel k hk (z + a) b, add_assoc, chiFn_add_cancel k hk z b, polarFn_add_left]
  funext dest
  simp only [Pi.add_apply]
  have h : ∀ x y w : ZMod 2, (x + (y + w)) + (x + y) = w := by decide
  exact h (chiFn k hk b dest) (polarFn k hk z b dest) (polarFn k hk a b dest)

theorem finRange_succ_eq (m : ℕ) :
    List.finRange (m + 1) = (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_finRange] at h1
    by_cases hm : i < m
    · rw [List.getElem_append_left (by simp [hm])]
      simp
    · have him : i = m := by omega
      rw [List.getElem_append_right (by simp; omega)]
      simp [him, Fin.ext_iff]

theorem runFn_succ (k d m : ℕ) (hk : 0 < k) (start : ℕ) (feed : ℕ → ℕ)
    (name finalConst : W k) (schedule : Fin (m + 1) → W k) (key : W k) :
    runFn k d (m + 1) hk start feed name finalConst schedule key =
      chiFn k hk (mixFn k d hk
        (runFn k d m hk start feed name (schedule (Fin.last m)) (fun i => schedule i.castSucc) key)) +
      rotFn k hk (feed (m + 1)) key + finalConst := by
  unfold runFn tickFn
  rw [finRange_succ_eq m, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil, Fin.val_castSucc, Fin.val_last]

def snocBool {m : ℕ} (mask' : Fin m → Bool) (b : Bool) (j : Fin (m + 1)) : Bool :=
  Fin.lastCases b mask' j

theorem snocBool_castSucc {m : ℕ} (mask' : Fin m → Bool) (b : Bool) (i : Fin m) :
    snocBool mask' b i.castSucc = mask' i := by
  simp [snocBool]

theorem snocBool_last {m : ℕ} (mask' : Fin m → Bool) (b : Bool) :
    snocBool mask' b (Fin.last m) = b := by
  simp [snocBool]

theorem sum_bool_succ {m : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (m + 1) → Bool) → M) :
    (∑ mask : Fin (m + 1) → Bool, f mask) =
      ∑ mask' : Fin m → Bool,
        (f (snocBool mask' true) + f (snocBool mask' false)) := by
  let e : ((Fin m → Bool) × Bool) ≃ (Fin (m + 1) → Bool) :=
    { toFun := fun p => snocBool p.1 p.2
      invFun := fun mask => (fun i => mask i.castSucc, mask (Fin.last m))
      left_inv := fun p => by
        ext i
        · exact snocBool_castSucc p.1 p.2 i
        · exact snocBool_last p.1 p.2
      right_inv := fun mask => by
        funext j
        refine Fin.lastCases ?_ ?_ j
        · exact snocBool_last _ _
        · intro i; exact snocBool_castSucc _ _ i }
  rw [Fintype.sum_equiv e.symm f (fun p => f (e p)) (fun mask => congrArg f (e.apply_symm_apply mask).symm)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun mask' _ => ?_)
  simp [e]

theorem main_ind (k d : ℕ) (hk : 0 < k) (start : ℕ) (feed : ℕ → ℕ)
    (u v base name : W k) :
    ∀ (q : ℕ) (finalConst : W k) (c p : Fin q → W k),
      let delta := fun schedule : Fin q → W k =>
        runFn k d q hk start feed name finalConst schedule (base + u + v) +
        runFn k d q hk start feed name finalConst schedule (base + u) +
        runFn k d q hk start feed name finalConst schedule (base + v) +
        runFn k d q hk start feed name finalConst schedule base
      (∑ mask : Fin q → Bool, delta (fun j => c j + if mask j then p j else 0)) =
        (List.finRange q).foldl (fun acc j => polarFn k hk (mixFn k d hk acc) (mixFn k d hk (p j)))
          (polarFn k hk (mixFn k d hk (rotFn k hk start u)) (mixFn k d hk (rotFn k hk start v))) := by
  intro q
  induction q with
  | zero =>
    intro finalConst c p
    dsimp only
    rw [Fintype.sum_unique]
    simp only [List.finRange_zero, List.foldl_nil, runFn, tickFn]
    have hrot_cancel :
        rotFn k hk (feed 0) (base + u + v) + rotFn k hk (feed 0) (base + u) +
        rotFn k hk (feed 0) (base + v) + rotFn k hk (feed 0) base = 0 := by
      simp only [rotFn_add]
      funext j
      simp only [Pi.add_apply, Pi.zero_apply]
      have h : ∀ a b c : ZMod 2, (a + b + c) + (a + b) + (a + c) + a = 0 := by decide
      exact h (rotFn k hk (feed 0) base j) (rotFn k hk (feed 0) u j) (rotFn k hk (feed 0) v j)
    have h4 : ∀ x1 x2 x3 x4 y1 y2 y3 y4 fc : W k,
        (x1 + y1 + fc) + (x2 + y2 + fc) + (x3 + y3 + fc) + (x4 + y4 + fc) =
        (x1 + x2 + x3 + x4) + (y1 + y2 + y3 + y4) := by
      intro x1 x2 x3 x4 y1 y2 y3 y4 fc
      funext j
      simp only [Pi.add_apply]
      have h : ∀ a1 a2 a3 a4 b1 b2 b3 b4 f : ZMod 2,
          (a1 + b1 + f) + (a2 + b2 + f) + (a3 + b3 + f) + (a4 + b4 + f) =
          (a1 + a2 + a3 + a4) + (b1 + b2 + b3 + b4) := by decide
      exact h (x1 j) (x2 j) (x3 j) (x4 j) (y1 j) (y2 j) (y3 j) (y4 j) (fc j)
    rw [h4, hrot_cancel, add_zero]
    have hm1 : mixFn k d hk (rotFn k hk start (base + u + v) + name) =
        mixFn k d hk (rotFn k hk start base + name) +
        mixFn k d hk (rotFn k hk start u) +
        mixFn k d hk (rotFn k hk start v) := by
      simp only [rotFn_add, mixFn_add]
      ring
    have hm2 : mixFn k d hk (rotFn k hk start (base + u) + name) =
        mixFn k d hk (rotFn k hk start base + name) +
        mixFn k d hk (rotFn k hk start u) := by
      simp only [rotFn_add, mixFn_add]
      ring
    have hm3 : mixFn k d hk (rotFn k hk start (base + v) + name) =
        mixFn k d hk (rotFn k hk start base + name) +
        mixFn k d hk (rotFn k hk start v) := by
      simp only [rotFn_add, mixFn_add]
      ring
    rw [hm1, hm2, hm3]
    exact chiFn_second_diff k hk _ _ _
  | succ m ih =>
    intro finalConst c p
    dsimp only
    rw [finRange_succ_eq m, List.foldl_append, List.foldl_map]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [sum_bool_succ]
    let c' : Fin m → W k := fun i => c i.castSucc
    let p' : Fin m → W k := fun i => p i.castSucc
    let cLast : W k := c (Fin.last m)
    let pLast : W k := p (Fin.last m)
    have hpair : ∀ mask' : Fin m → Bool,
        let sT : Fin (m + 1) → W k := fun j => c j + if snocBool mask' true j then p j else 0
        let sF : Fin (m + 1) → W k := fun j => c j + if snocBool mask' false j then p j else 0
        let s' : Fin m → W k := fun i => c' i + if mask' i then p' i else 0
        let d_m :=
          runFn k d m hk start feed name cLast s' (base + u + v) +
          runFn k d m hk start feed name cLast s' (base + u) +
          runFn k d m hk start feed name cLast s' (base + v) +
          runFn k d m hk start feed name cLast s' base
        (runFn k d (m + 1) hk start feed name finalConst sT (base + u + v) +
         runFn k d (m + 1) hk start feed name finalConst sT (base + u) +
         runFn k d (m + 1) hk start feed name finalConst sT (base + v) +
         runFn k d (m + 1) hk start feed name finalConst sT base) +
        (runFn k d (m + 1) hk start feed name finalConst sF (base + u + v) +
         runFn k d (m + 1) hk start feed name finalConst sF (base + u) +
         runFn k d (m + 1) hk start feed name finalConst sF (base + v) +
         runFn k d (m + 1) hk start feed name finalConst sF base) =
        polarFn k hk (mixFn k d hk d_m) (mixFn k d hk pLast) := by
      intro mask'
      dsimp only
      let sT : Fin (m + 1) → W k := fun j => c j + if snocBool mask' true j then p j else 0
      let sF : Fin (m + 1) → W k := fun j => c j + if snocBool mask' false j then p j else 0
      let s' : Fin m → W k := fun i => c' i + if mask' i then p' i else 0
      have hsT_cast : (fun i : Fin m => sT i.castSucc) = s' := by
        funext i; simp [sT, s', c', p', snocBool_castSucc]
      have hsF_cast : (fun i : Fin m => sF i.castSucc) = s' := by
        funext i; simp [sF, s', c', p', snocBool_castSucc]
      have hsT_last : sT (Fin.last m) = cLast + pLast := by
        simp [sT, cLast, pLast, snocBool_last]
      have hsF_last : sF (Fin.last m) = cLast := by
        simp [sF, cLast, snocBool_last]
      have htoggle : ∀ key : W k,
          runFn k d (m + 1) hk start feed name finalConst sT key +
          runFn k d (m + 1) hk start feed name finalConst sF key =
          chiFn k hk (mixFn k d hk pLast) +
          polarFn k hk (mixFn k d hk (runFn k d m hk start feed name cLast s' key))
            (mixFn k d hk pLast) := by
        intro key
        rw [runFn_succ, runFn_succ, hsT_cast, hsF_cast, hsT_last, hsF_last]
        have hrun_add :
            runFn k d m hk start feed name (cLast + pLast) s' key =
            runFn k d m hk start feed name cLast s' key + pLast := by
          unfold runFn
          ring
        rw [hrun_add, mixFn_add]
        have hcancel : ∀ x1 x2 r fc : W k,
            (x1 + r + fc) + (x2 + r + fc) = x1 + x2 := by
          intro x1 x2 r fc
          funext j
          simp only [Pi.add_apply]
          have h : ∀ a b c d : ZMod 2, (a + c + d) + (b + c + d) = a + b := by decide
          exact h (x1 j) (x2 j) (r j) (fc j)
        rw [hcancel]
        exact chiFn_add_cancel k hk _ _
      have hrearr : ∀ a1 a2 a3 a4 b1 b2 b3 b4 : W k,
          (a1 + a2 + a3 + a4) + (b1 + b2 + b3 + b4) =
          (a1 + b1) + (a2 + b2) + (a3 + b3) + (a4 + b4) := by
        intro a1 a2 a3 a4 b1 b2 b3 b4
        ring
      rw [hrearr, htoggle (base + u + v), htoggle (base + u), htoggle (base + v), htoggle base]
      have hconst4 : ∀ cc x1 x2 x3 x4 : W k,
          (cc + x1) + (cc + x2) + (cc + x3) + (cc + x4) = x1 + x2 + x3 + x4 := by
        intro cc x1 x2 x3 x4
        funext j
        simp only [Pi.add_apply]
        have h : ∀ t a1 a2 a3 a4 : ZMod 2,
            (t + a1) + (t + a2) + (t + a3) + (t + a4) = a1 + a2 + a3 + a4 := by decide
        exact h (cc j) (x1 j) (x2 j) (x3 j) (x4 j)
      rw [hconst4]
      simp only [mixFn_add, polarFn_add_left]
      rfl
    have hsum_eq :
        (∑ mask' : Fin m → Bool,
          ((runFn k d (m + 1) hk start feed name finalConst
              (fun j => c j + if snocBool mask' true j then p j else 0) (base + u + v) +
            runFn k d (m + 1) hk start feed name finalConst
              (fun j => c j + if snocBool mask' true j then p j else 0) (base + u) +
            runFn k d (m + 1) hk start feed name finalConst
              (fun j => c j + if snocBool mask' true j then p j else 0) (base + v) +
            runFn k d (m + 1) hk start feed name finalConst
              (fun j => c j + if snocBool mask' true j then p j else 0) base) +
           (runFn k d (m + 1) hk start feed name finalConst
              (fun j => c j + if snocBool mask' false j then p j else 0) (base + u + v) +
            runFn k d (m + 1) hk start feed name finalConst
              (fun j => c j + if snocBool mask' false j then p j else 0) (base + u) +
            runFn k d (m + 1) hk start feed name finalConst
              (fun j => c j + if snocBool mask' false j then p j else 0) (base + v) +
            runFn k d (m + 1) hk start feed name finalConst
              (fun j => c j + if snocBool mask' false j then p j else 0) base))) =
        ∑ mask' : Fin m → Bool,
          polarFn k hk (mixFn k d hk
            (runFn k d m hk start feed name cLast (fun i => c' i + if mask' i then p' i else 0) (base + u + v) +
             runFn k d m hk start feed name cLast (fun i => c' i + if mask' i then p' i else 0) (base + u) +
             runFn k d m hk start feed name cLast (fun i => c' i + if mask' i then p' i else 0) (base + v) +
             runFn k d m hk start feed name cLast (fun i => c' i + if mask' i then p' i else 0) base))
            (mixFn k d hk pLast) :=
      Finset.sum_congr rfl (fun mask' _ => hpair mask')
    rw [hsum_eq, ← polarFn_sum_left, ← mixFn_sum]
    have hih := ih cLast c' p'
    dsimp only at hih
    rw [hih]

theorem main : (∀ (k d q : ℕ) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n%k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (offset : ℕ) (w : W) (j : Fin k) => w (ix (j.val+k-offset % k))
  let mix := fun (word : W) (mid : Fin k) =>
    word mid + word (ix (mid.val+d)) + word (ix (mid.val+k-d%k))
  let chi := fun (z : W) (dest : Fin k) =>
    z dest + (1+z (ix (dest.val+1)))*z (ix (dest.val+2))
  let polar := fun (x y : W) (site : Fin k) =>
    x (ix (site.val+1))*y (ix (site.val+2)) + x (ix (site.val+2))*y (ix (site.val+1))
  ∀ (start : ℕ) (feed : ℕ → ℕ),
    let tick := fun (tickNo : ℕ) (key state : W) => chi (mix state) + rot (feed tickNo) key
    let run := fun (name finalConst : W) (schedule : Fin q → W) (key : W) =>
      tick q key ((List.finRange q).foldl
        (fun prev idx => tick idx.val key prev + schedule idx) (rot start key + name)) + finalConst
    ∀ (u v base name finalConst : W) (c p : Fin q → W),
      let delta := fun schedule : Fin q → W =>
        run name finalConst schedule (base+u+v) + run name finalConst schedule (base+u) +
        run name finalConst schedule (base+v) + run name finalConst schedule base
      (∑ mask : Fin q → Bool, delta (fun j => c j + if mask j then p j else 0)) =
        (List.finRange q).foldl (fun acc j => polar (mix acc) (mix (p j)))
          (polar (mix (rot start u)) (mix (rot start v)))) := by
  intro k d q hk
  dsimp only
  intro start feed u v base name finalConst c p
  exact main_ind k d hk start feed u v base name q finalConst c p

end PEqualNP.Outside.L_meta_25760_aux

theorem PEqualNP.Outside.L_meta_25760 : (∀ (k d q : ℕ) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n%k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (offset : ℕ) (w : W) (j : Fin k) => w (ix (j.val+k-offset % k))
  let mix := fun (word : W) (mid : Fin k) =>
    word mid + word (ix (mid.val+d)) + word (ix (mid.val+k-d%k))
  let chi := fun (z : W) (dest : Fin k) =>
    z dest + (1+z (ix (dest.val+1)))*z (ix (dest.val+2))
  let polar := fun (x y : W) (site : Fin k) =>
    x (ix (site.val+1))*y (ix (site.val+2)) + x (ix (site.val+2))*y (ix (site.val+1))
  ∀ (start : ℕ) (feed : ℕ → ℕ),
    let tick := fun (tickNo : ℕ) (key state : W) => chi (mix state) + rot (feed tickNo) key
    let run := fun (name finalConst : W) (schedule : Fin q → W) (key : W) =>
      tick q key ((List.finRange q).foldl
        (fun prev idx => tick idx.val key prev + schedule idx) (rot start key + name)) + finalConst
    ∀ (u v base name finalConst : W) (c p : Fin q → W),
      let delta := fun schedule : Fin q → W =>
        run name finalConst schedule (base+u+v) + run name finalConst schedule (base+u) +
        run name finalConst schedule (base+v) + run name finalConst schedule base
      (∑ mask : Fin q → Bool, delta (fun j => c j + if mask j then p j else 0)) =
        (List.finRange q).foldl (fun acc j => polar (mix acc) (mix (p j)))
          (polar (mix (rot start u)) (mix (rot start v)))) :=
  PEqualNP.Outside.L_meta_25760_aux.main
