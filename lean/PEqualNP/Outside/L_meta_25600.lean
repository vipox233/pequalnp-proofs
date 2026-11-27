import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25594

namespace PEqualNP.Outside.L_meta_25600_aux.Packing25600

theorem average {k L b : ℕ} (hk : 0 < k) (hL : 0 < L) (mask : Fin k → Bool)
    (H : ∀ chosen : Finset (Fin k), (∀ i ∈ chosen, mask i = true) →
      (∀ i ∈ chosen, ∀ j ∈ chosen, i ≠ j → L ≤ (j.val + k - i.val) % k) →
      chosen.card ≤ b) :
    (k / L) * (Finset.univ.filter (fun pos : Fin k => mask pos = true)).card ≤ k * b := by
  classical
  let : NeZero k := ⟨hk.ne'⟩
  have room (a : Fin (k/L)) : a.val * L + L ≤ k := by
    calc
      _ = (a.val+1)*L := (Nat.succ_mul _ _).symm
      _ ≤ (k/L)*L := Nat.mul_le_mul_right L a.isLt
      _ ≤ k := Nat.div_mul_le_self _ _
  let p (a : Fin (k/L)) : Fin k := ⟨a.val*L, by have := room a; omega⟩
  have pinj : Function.Injective p := by
    intro i j h
    have e : i.val * L = j.val * L := congrArg Fin.val h
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hL e)
  have sep (a c : Fin (k/L)) (hac : a ≠ c) : L ≤ (p c - p a).val := by
    have ne : a.val ≠ c.val := fun e => hac (Fin.ext e)
    rcases lt_or_gt_of_ne ne with h | h
    · have hh := Nat.mul_le_mul_right L (show a.val + 1 ≤ c.val from h)
      rw [Nat.succ_mul] at hh
      have hp : p a ≤ p c := by change a.val * L ≤ c.val * L; omega
      rw [Fin.sub_val_of_le hp]
      change L ≤ c.val * L - a.val * L
      omega
    · have hc := Nat.mul_lt_mul_of_pos_right h hL
      have ha := room a
      rw [Fin.val_sub]
      change L ≤ (k - a.val * L + c.val * L) % k
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  let f (r : Fin k) (a : Fin (k/L)) := r + p a
  let I (r : Fin k) : ℕ := if mask r = true then 1 else 0
  have slice (r : Fin k) : (∑ a : Fin (k/L), I (f r a)) ≤ b := by
    let t := Finset.univ.filter (fun a : Fin (k/L) => mask (f r a) = true)
    have hf : Function.Injective (f r) := by
      intro i j h
      exact pinj (add_left_cancel h)
    have hbound := H (t.image (f r)) (by
      intro i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp ha).2) (by
      intro i hi j hj hij
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hj
      have hne : a ≠ c := fun e => hij (congrArg (f r) e)
      have heq : f r c - f r a = p c - p a := by dsimp [f]; abel
      have hd : L ≤ (f r c - f r a).val := by rw [heq]; exact sep a c hne
      rw [Fin.val_sub] at hd
      have hv := (f r a).isLt
      have e : (f r c).val + k - (f r a).val = k - (f r a).val + (f r c).val := by omega
      simpa only [e] using hd)
    rw [Finset.card_image_of_injective _ hf] at hbound
    simpa only [t, Finset.card_filter, I] using hbound
  have column (a : Fin (k/L)) : ∑ r : Fin k, I (f r a) =
      (Finset.univ.filter (fun pos : Fin k => mask pos = true)).card := by
    calc
      _ = ∑ r : Fin k, I r := Equiv.sum_comp (Equiv.addRight (p a)) I
      _ = _ := (Finset.card_filter _ _).symm
  calc
    _ = ∑ a : Fin (k/L), ∑ r : Fin k, I (f r a) := by simp [column]
    _ = ∑ r : Fin k, ∑ a : Fin (k/L), I (f r a) := Finset.sum_comm
    _ ≤ ∑ _r : Fin k, b := Finset.sum_le_sum fun r _ => slice r
    _ = _ := by simp

end PEqualNP.Outside.L_meta_25600_aux.Packing25600

namespace PEqualNP.Outside.L_meta_25600_aux
open PEqualNP.Outside.L_meta_25594_aux

def blockOffset256 (d : Nat) (s : Fin 4) : Nat :=
  ![0,1,2*d+1,2*d+2] s

theorem blockOffset256_le (d : Nat) (s : Fin 4) : blockOffset256 d s ≤ 2*d+2 := by
  fin_cases s <;> simp [blockOffset256]

theorem blockOffset256_injective {d : Nat} (hd : 0<d) : Function.Injective (blockOffset256 d) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [blockOffset256] at * <;> omega

def blockPos256 {k : Nat} (hk : 0<k) (d : Nat) (S : Finset (Fin k)) (q : S × Fin 4) : Fin k :=
  at94 hk d q.1.val (blockOffset256 d q.2)

private theorem closeFromOffsets256 {k L a b : Nat} (i j : Fin k)
    (ha : a≤L) (hba : b≤a) (hL : L<k) (hh : i.val+a ≡ j.val+b [MOD k]) :
    (j.val+k-i.val)%k ≤ L := by
  have sm : i.val+(a-b) ≡ j.val [MOD k] := by
    apply Nat.ModEq.add_right_cancel' b
    convert hh using 1
    omega
  have wrap : j.val ≡ j.val+k [MOD k] := by
    unfold Nat.ModEq
    simp
  have sm' : i.val+(a-b) ≡ i.val+(j.val+k-i.val) [MOD k] := by
    convert sm.trans wrap using 1
    omega
  have s := Nat.ModEq.add_left_cancel' i.val sm'
  unfold Nat.ModEq at s
  rw [Nat.mod_eq_of_lt (by omega : a-b<k)] at s
  omega

theorem blockPos256_injective {k d : Nat} (hk : 0<k) (hd : 0<d) (hkD : 4*d+4<k)
    (S : Finset (Fin k)) (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 4*d+5≤(j.val+k-i.val)%k) :
    Function.Injective (blockPos256 hk d S) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ eqv
  change at94 hk d i.val (blockOffset256 d a) = at94 hk d j.val (blockOffset256 d b) at eqv
  have ha := blockOffset256_le d a
  have hb := blockOffset256_le d b
  by_cases e : i=j
  · subst j
    have e' := (offEq94 hk d i.val (by omega : blockOffset256 d a < k) (by omega : blockOffset256 d b < k)).mp eqv
    rw [blockOffset256_injective hd e']
  · have hne : i.val ≠ j.val := fun h => e (Subtype.ext h)
    have fs := hsep i.val i.property j.val j.property hne
    have ft := hsep j.val j.property i.val i.property hne.symm
    have ee : anch94 d i.val+blockOffset256 d a ≡ anch94 d j.val+blockOffset256 d b [MOD k] :=
      congrArg Fin.val eqv
    have eqn : i.val.val+blockOffset256 d a ≡ j.val.val+blockOffset256 d b [MOD k] := by
      apply Nat.ModEq.add_left_cancel' (k-d+2)
      simpa only [anch94, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ee
    rcases le_total (blockOffset256 d b) (blockOffset256 d a) with ord | ord
    · have := closeFromOffsets256 i.val j.val ha ord (by omega) eqn
      omega
    · have := closeFromOffsets256 j.val i.val hb ord (by omega) eqn.symm
      omega

noncomputable def blockEmbed256 {k : Nat} (hk : 0<k) (d : Nat) (S : Finset (Fin k))
    (z : S → Fin 4 → Bool) : Word94 k := by
  classical
  exact fun i => if h : ∃ q, blockPos256 hk d S q=i then z h.choose.1 h.choose.2 else false

theorem blockEmbed256_at {k d : Nat} (hk : 0<k) (hd : 0<d) (hkD : 4*d+4<k)
    (S : Finset (Fin k)) (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 4*d+5≤(j.val+k-i.val)%k)
    (z : S → Fin 4 → Bool) (q : S × Fin 4) :
    blockEmbed256 hk d S z (blockPos256 hk d S q)=z q.1 q.2 := by
  classical
  have h : ∃ q', blockPos256 hk d S q' = blockPos256 hk d S q := ⟨q,rfl⟩
  simp only [blockEmbed256, dite_eq_left h]
  rw [blockPos256_injective hk hd hkD S hsep h.choose_spec]

theorem blockEmbed256_add {k : Nat} (hk : 0<k) (d : Nat) (S : Finset (Fin k))
    (z w : S → Fin 4 → Bool) :
    blockEmbed256 hk d S (fun i j => xor (z i j) (w i j)) =
    add94 (blockEmbed256 hk d S z) (blockEmbed256 hk d S w) := by
  classical
  funext i
  by_cases h : ∃ q, blockPos256 hk d S q=i <;> simp [blockEmbed256,add94,h]

theorem blockEmbed256_unit {k d : Nat} (hk : 0<k) (hd : 0<d) (hkD : 4*d+4<k)
    (S : Finset (Fin k)) (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 4*d+5≤(j.val+k-i.val)%k)
    (q : S × Fin 4) : blockEmbed256 hk d S (fun i j => decide ((i,j)=q)) = dir94 (blockPos256 hk d S q) := by
  classical
  funext i
  by_cases h : ∃ p, blockPos256 hk d S p=i
  · obtain ⟨p,rfl⟩ := h
    rw [blockEmbed256_at hk hd hkD S hsep]
    simp [dir94, (blockPos256_injective hk hd hkD S hsep).eq_iff]
  · have hne : i ≠ blockPos256 hk d S q := fun e => h ⟨q,e.symm⟩
    simp [dir94,blockEmbed256,h,hne]

end PEqualNP.Outside.L_meta_25600_aux

namespace PEqualNP.Outside.L_meta_25600_aux

open PEqualNP.Outside.L_meta_25594_aux

private theorem close_of_offsets {k D : Nat} (i j : Fin k) {l r : Nat}
    (hl : l ≤ 2*D) (ord : r ≤ l) (bound : 2*D<k)
    (hh : i.val+l ≡ j.val+r [MOD k]) : (j.val+k-i.val)%k ≤ 2*D := by
  have sm : i.val+(l-r) ≡ j.val [MOD k] := by
    apply Nat.ModEq.add_right_cancel' r
    convert hh using 1 <;> omega
  have wrap : j.val ≡ j.val+k [MOD k] := by
    unfold Nat.ModEq
    simp
  have sm' : i.val+(l-r) ≡ i.val+(j.val+k-i.val) [MOD k] := by
    convert sm.trans wrap using 1 <;> omega
  have s := Nat.ModEq.add_left_cancel' i.val sm'
  unfold Nat.ModEq at s
  rw [Nat.mod_eq_of_lt (by omega : l-r<k)] at s
  omega

theorem far_no_arc {k d D : Nat} (hk : 0<k) (bound : 2*D<k)
    (i j z : Fin k) (s t a b : Nat) (hs : s≤D) (ht : t≤D) (ha : a≤D) (hb : b≤D)
    (fjz : 2*D+1 ≤ (z.val+k-j.val)%k) (fzj : 2*D+1 ≤ (j.val+k-z.val)%k)
    (ea : at94 hk d i a=at94 hk d j s) (eb : at94 hk d i b=at94 hk d z t) : False := by
  have extract (i j : Fin k) (a s : Nat) (e : at94 hk d i a=at94 hk d j s) :
      i.val+a ≡ j.val+s [MOD k] := by
    have eqv : anch94 d i+a ≡ anch94 d j+s [MOD k] := congrArg Fin.val e
    apply Nat.ModEq.add_left_cancel' (k-d+2)
    simpa only [anch94, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using eqv
  have one := extract i j a s ea
  have two := extract i z b t eb
  have off : j.val+(s+b) ≡ z.val+(t+a) [MOD k] := by
    apply Nat.ModEq.add_left_cancel' i.val
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using one.symm.add two
  by_cases ord : t+a ≤ s+b
  · have := close_of_offsets j z (by omega) ord bound off
    omega
  · have := close_of_offsets z j (by omega) (by omega) bound off.symm
    omega

theorem crossFour {k} (hk : 0<k) (d : Nat) (hw : 4*d+4<k)
    (fb : Word94 k→Word94 k) (hf : ∀a b, fb (add94 a b)=add94 (fb a) (fb b))
    (ofs : Word94 k) (j z : Fin k) (r t : Nat) (hr : r≤2*d+2) (ht : t≤2*d+2)
    (fjz : 4*d+5≤(z.val+k-j.val)%k) (fzj : 4*d+5≤(j.val+k-z.val)%k)
    (u v x : Word94 k) (i : Fin k) :
    let l:=dir94 (at94 hk d j r)
    let h:=dir94 (at94 hk d z t)
    D94 v (D94 u (D94 h (D94 l (fun w=>bit94 (output94 hk d fb ofs w i))))) x=0 := by
  intro l h
  let Q:=q94 hk d fb ofs i
  let B:=B94 hk d i
  have law (a b w : Word94 k) (s : Nat) : D94 b (D94 a (Q (s+1))) w=B s a b :=
    (qPol94 hk fb ofs hf i (s+1) a b w).trans (polNext94 hk i s a b)
  have eqF : (fun w=>bit94 (output94 hk d fb ofs w i))=fun w=>Q 0 w+Q 2 w+Q 1 w*Q 2 w :=
    funext (fun w=>outEval94 hk d (by omega) fb ofs w i)
  rw [eqF]
  have calc4 (a : B 0 l h=0) (b : B 1 l h=0) :=
    polynomial94 l h u v x (Q 1) (Q 2) (Q 0) (B 0) (B 1) (pol94 hk d i 0)
      (fun a b w=>law a b w 0) (fun a b w=>law a b w 1) (qPol94 hk fb ofs hf i 0) a b
  by_cases aa : ∃ s, s≤2*d+2 ∧ at94 hk d i s=at94 hk d j r
  · obtain ⟨a,al,az⟩ := aa
    have kill (s : Nat) (hs : s≤1) (w : Word94 k) : B s h w=0 :=
      blockGone94 hk i _ s hs (fun b bl eqn=>far_no_arc hk (by omega) i j z r t a b
        hr ht al bl (by omega) (by omega) az eqn) w
    have c0 : B 0 l h=0 := (bSym94 hk d 0 i l h).trans (kill 0 (by omega) l)
    have c1 : B 1 l h=0 := (bSym94 hk d 1 i l h).trans (kill 1 (by omega) l)
    rw [calc4 c0 c1,kill 1 (by omega) v,kill 1 (by omega) u,kill 0 (by omega) u,kill 0 (by omega) v]
    ring
  · have kill (s : Nat) (hs : s≤1) (w : Word94 k) : B s l w=0 :=
      blockGone94 hk i _ s hs (fun a al eqn=>aa ⟨a,al,eqn⟩) w
    rw [calc4 (kill 0 (by omega) h) (kill 1 (by omega) h),kill 0 (by omega) u,kill 0 (by omega) v,
      kill 1 (by omega) u,kill 1 (by omega) v]
    ring
end PEqualNP.Outside.L_meta_25600_aux

namespace PEqualNP.Outside.L_meta_25600_aux

abbrev RW (R : Type*) := R → Fin 4 → Bool

def radd {R : Type*} (x y : RW R) : RW R := fun i j => xor (x i j) (y i j)
def rdiff {R : Type*} (f : RW R → Bool) (a x : RW R) := xor (f x) (f (radd x a))
def ru {R : Type*} [DecidableEq R] (i : R × Fin 4) : RW R := fun j h=>decide ((j,h)=i)
def rset {R : Type*} [DecidableEq R] (s : Finset (R × Fin 4)) : RW R := fun j h=>decide ((j,h)∈s)

theorem rc {R : Type*} (f : RW R→Bool) (a b : RW R) :
    rdiff (rdiff f a) b=rdiff (rdiff f b) a := by
  have swap (x : RW R) : radd (radd x b) a=radd (radd x a) b := by
    funext i j
    simp only [radd, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  funext x
  simp only [rdiff, swap, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem extend1 {R : Type*} [Fintype R] [DecidableEq R] (f : RW R→Bool)
    (hh : ∀ i x, rdiff f (ru i) x=false) : ∀ a x, rdiff f a x=false := by
  intro a
  have fix (i : R×Fin 4) (x : RW R) : f (radd x (ru i))=f x := by
    have h := hh i x
    unfold rdiff at h
    cases h1 : f x <;> cases h2 : f (radd x (ru i)) <;> simp_all
  have fixes (s : Finset (R×Fin 4)) (x : RW R) : f (radd x (rset s))=f x := by
    induction s using Finset.induction_on with
    | empty =>
      have e : radd x (rset ∅)=x := by funext i j; simp [radd,rset]
      rw [e]
    | insert t s ht ih =>
      have e : radd x (rset (insert t s))=radd (radd x (rset s)) (ru t) := by
        funext i j
        by_cases eq : (i,j)=t
        · have nm : (i,j)∉s := eq ▸ ht
          simp [radd,rset,ru,eq,ht]
        · simp [radd,rset,ru,eq]
      rw [e,fix,ih]
  let s := Finset.univ.filter (fun i : R×Fin 4=>a i.1 i.2=true)
  have ex : rset s=a := by funext i j; simp [rset,s]
  intro x
  rw [rdiff,←ex,fixes]
  simp

abbrev r4 {R : Type*} (f : RW R→Bool) (a b c d : RW R) := rdiff (rdiff (rdiff (rdiff f a) b) c) d

theorem extend4 {R : Type*} [Fintype R] [DecidableEq R] (f : RW R→Bool)
    (hunit : ∀ i j k l x, r4 f (ru i) (ru j) (ru k) (ru l) x=false) :
    ∀ a b c d x, r4 f a b c d x=false := by
  have h4 (i j k : R×Fin 4) (d x : RW R) : r4 f (ru i) (ru j) (ru k) d x=false :=
    extend1 _ (hunit i j k) d x
  have h3 (i j : R×Fin 4) (c d x : RW R) : r4 f (ru i) (ru j) c d x=false := by
    unfold r4
    rw [rc _ c d]
    apply extend1
    intro k y
    rw [rc _ d (ru k)]
    exact h4 i j k d y
  have h2 (i : R×Fin 4) (b c d x : RW R) : r4 f (ru i) b c d x=false := by
    unfold r4
    rw [rc _ b c, rc _ b d]
    apply extend1
    intro j y
    rw [rc _ d (ru j), rc _ c (ru j)]
    exact h3 i j c d y
  intro a b c d x
  unfold r4
  rw [rc _ a b, rc _ a c, rc _ a d]
  apply extend1
  intro i y
  rw [rc _ d (ru i), rc _ c (ru i), rc _ b (ru i)]
  exact h2 i b c d y

end PEqualNP.Outside.L_meta_25600_aux

namespace PEqualNP.Outside.L_meta_25600_aux

theorem rxx {R : Type*} (f : RW R→Bool) (a : RW R) :
    rdiff (rdiff f a) a=fun _=>false := by
  funext x
  have e : radd (radd x a) a=x := by funext i j; simp [radd,Bool.xor_assoc]
  simp [rdiff,e,Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

@[simp] theorem rz {R : Type*} (a : RW R) : rdiff (fun _=>false) a=fun _=>false := by rfl

theorem basis4 {R : Type*} [Fintype R] [DecidableEq R] (f : RW R→Bool)
    (hm : ∀ (i j : R×Fin 4), i.1≠j.1 → ∀ (a b x : RW R), r4 f (ru i) (ru j) a b x=false)
    (hs : ∀ (i : R) x, r4 f (ru (i,0)) (ru (i,3)) (ru (i,1)) (ru (i,2)) x=false) :
    ∀ a b c d x, r4 f a b c d x=false := by
  apply extend4
  rintro ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ ⟨l,d⟩ x
  by_cases ij : i=j
  · subst j
    by_cases ik : i=k
    · subst k
      by_cases il : i=l
      · subst l
        have rule : ∀ a b c d : Fin 4, List.Perm [a,b,c,d] [0,3,1,2] ∨
            a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d := by decide
        rcases rule a b c d with perm|e|e|e|e|e|e
        · have pr := perm.map (fun q=>ru (i,q))
          have h := pr.foldl_eq' (f:=rdiff) (fun a _ b _ w=>rc w a b) f
          exact (congrFun h x).trans (hs i x)
        · subst b; simp [r4,rxx]
        · subst c; unfold r4; rw [rc _ (ru (i,b)) (ru (i,a)),rxx]; rfl
        · subst d; unfold r4; rw [rc _ (ru (i,c)) (ru (i,a)),rc _ (ru (i,b)) (ru (i,a)),rxx]; rfl
        · subst c; simp [r4,rxx]
        · subst d; unfold r4; rw [rc _ (ru (i,c)) (ru (i,b)),rxx]; rfl
        · subst d; simp [r4,rxx]
      · unfold r4; rw [rc _ (ru (i,c)) (ru (l,d)),rc _ (ru (i,b)) (ru (l,d))]
        exact hm (i,a) (l,d) il _ _ x
    · unfold r4; rw [rc _ (ru (i,b)) (ru (k,c))]
      exact hm (i,a) (k,c) ik _ _ x
  · exact hm (i,a) (j,b) ij _ _ x
end PEqualNP.Outside.L_meta_25600_aux

namespace PEqualNP.Outside.L_meta_25600_aux
open PEqualNP.Outside.L_meta_25594_aux

def block256 (z : Fin 4→Bool) := (List.ofFn z).all id
def blocks256 {p : Nat} (z : RW (Fin p)) :=
  (List.ofFn (fun i=>block256 (z i))).foldl xor false

private theorem parityList (l : List Bool) (a : Bool) :
    bit94 (l.foldl xor a)=bit94 a+(l.map bit94).sum := by
  induction l generalizing a with
  | nil => simp
  | cons h t ih => rw [List.foldl_cons,ih,bit_xor];simp [add_assoc]

theorem parityFn {n : Nat} (f : Fin n→Bool) :
    bit94 ((List.ofFn f).foldl xor false)=∑ i,bit94 (f i) := by
  rw [parityList,List.map_ofFn,List.sum_ofFn]
  simp [bit94,Function.comp_apply]

theorem r4_parity {p : Nat} (a b c d x : RW (Fin p)) :
    bit94 (r4 blocks256 a b c d x)=∑ i,bit94 (r4 (fun z=>block256 (z i)) a b c d x) := by
  simp only [r4,rdiff,bit_xor,blocks256,parityFn,Finset.sum_add_distrib]

theorem d_wrong_row {R : Type*} [DecidableEq R] (f : (Fin 4→Bool)→Bool)
    (q : R×Fin 4) (i : R) (hi : i≠q.1) :
    rdiff (fun z=>f (z i)) (ru q) = fun _=>false := by
  funext z
  have k : radd z (ru q) i=z i := by
    funext h
    have hq : (i,h)≠q := fun e=>hi (congrArg Prod.fst e)
    simp [radd,ru,hq]
  simp [rdiff,k]

theorem blocks_mixed {p : Nat} (q t : Fin p×Fin 4) (ht : q.1≠t.1)
    (a b x : RW (Fin p)) : r4 blocks256 (ru q) (ru t) a b x=false := by
  apply bit_inj
  rw [r4_parity]
  change _=0
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hq : i=q.1
  · have h : i≠t.1 := hq ▸ ht
    unfold r4
    rw [rc _ (ru q) (ru t),d_wrong_row block256 t i h]; rfl
  · unfold r4; rw [d_wrong_row block256 q i hq]; rfl

private def dirCol (q i : Fin 4) := decide (i=q)
private def dc (f : (Fin 4→Bool)→Bool) (a x : Fin 4→Bool) := xor (f x) (f (fun i=>xor (x i) (a i)))

private theorem rowDiff {R : Type*} (i : R) (f : (Fin 4→Bool)→Bool) (a : RW R) :
    rdiff (fun z=>f (z i)) a=fun z=>dc f (a i) (z i) := rfl

theorem canonical_product (x : Fin 4→Bool) :
    dc (dc (dc (dc block256 (dirCol 0)) (dirCol 3)) (dirCol 1)) (dirCol 2) x=true := by
  revert x
  decide

theorem blocks_same {p : Nat} (i : Fin p) (x : RW (Fin p)) :
    r4 blocks256 (ru (i,0)) (ru (i,3)) (ru (i,1)) (ru (i,2)) x=true := by
  apply bit_inj
  rw [r4_parity]
  change _=1
  have one : bit94 (r4 (fun z=>block256 (z i))
        (ru (i,0)) (ru (i,3)) (ru (i,1)) (ru (i,2)) x)=1 := by
    have ru1 (c : Fin 4) : ru (i,c) i=dirCol c := by funext j;simp [ru,dirCol]
    simp only [r4,rowDiff,ru1,canonical_product]; rfl
  rw [Finset.sum_eq_single i]
  · exact one
  · intro j hj hi
    unfold r4; rw [d_wrong_row block256 (i,0) j hi];rfl
  · simp

theorem dXor {R : Type*} (f g : RW R→Bool) (h : RW R) :
    rdiff (fun x=>xor (f x) (g x)) h=fun x=>xor (rdiff f h x) (rdiff g h x) := by
  funext x
  simp [rdiff,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

theorem r4xor {R : Type*} (f g : RW R→Bool) (a b c d x : RW R) :
    r4 (fun y=>xor (f y) (g y)) a b c d x=xor (r4 f a b c d x) (r4 g a b c d x) := by
  simp only [r4,dXor]
end PEqualNP.Outside.L_meta_25600_aux

namespace PEqualNP.Outside.L_meta_25600_aux
open PEqualNP.Outside.L_meta_25594_aux

def mo256 {k : Nat} (hk : 0<k) (d : Nat) (fb : Word94 k→Word94 k)
    (ofs mask : Word94 k) : Word94 k→Bool := fun x=>(List.ofFn (fun i : Fin k=>mask i && output94 hk d fb ofs x i)).foldl xor false

theorem diff_aff {R : Type*} {k} (A E : RW R→Word94 k)
    (hA : ∀ x y, A (radd x y)=add94 (A x) (E y))
    (f : Word94 k→Bool) (y : RW R) :
    rdiff (fun x=>f (A x)) y=fun x=>boolDiff94 f (E y) (A x) := by
  funext x
  simp only [rdiff,boolDiff94,hA]

theorem restriction256 {k d p : Nat} (hk : 0<k) (hd : 0<d) (hw : 4*d+4<k)
    (fb : Word94 k→Word94 k) (hf : ∀ a b, fb (add94 a b)=add94 (fb a) (fb b))
    (ofs mask : Word94 k) (J : Fin p→Fin k)
    (hm : ∀ j, mask (J j)=true)
    (hs : ∀ i j, i≠j→4*d+5≤((J j).val+k-(J i).val)%k)
    (A E : RW (Fin p)→Word94 k)
    (hA : ∀ x y, A (radd x y)=add94 (A x) (E y))
    (hu : ∀ q : Fin p×Fin 4, E (ru q)=dir94 (at94 hk d (J q.1) (blockOffset256 d q.2))) :
    ∀ a b c e x, r4 (fun z=>xor (mo256 hk d fb ofs mask (A z)) (blocks256 z)) a b c e x=false := by
  apply basis4
  · intro q t hqt a b x
    rw [r4xor,blocks_mixed q t hqt]
    simp only [Bool.xor_false]
    unfold r4
    simp only [diff_aff A E hA,hu]
    apply bit_inj
    have det := maskedFour94 (output94 hk d fb ofs) mask (J q.1)
      (dir94 (at94 hk d (J q.1) (blockOffset256 d q.2)))
      (dir94 (at94 hk d (J t.1) (blockOffset256 d t.2)))
      (E a) (E b) (A x) 0 (fun i=>by
        rw [crossFour hk d hw fb hf ofs (J q.1) (J t.1) _ _ (blockOffset256_le d q.2)
          (blockOffset256_le d t.2) (hs q.1 t.1 hqt) (hs t.1 q.1 hqt.symm) (E a) (E b) (A x) i]
        simp)
    unfold mo256
    simpa only [mul_zero,show bit94 false=0 from rfl] using det
  · intro j x
    rw [r4xor,blocks_same]
    simp only [Bool.xor_true, Bool.not_eq_false']
    unfold r4
    simp only [diff_aff A E hA,hu]
    let r := at94 hk d (J j) 1
    let t := at94 hk d (J j) (2*d+1)
    have ne : r≠t := fun h=>by
      have := (offEq94 hk d (J j) (by omega : 1<k) (by omega : 2*d+1<k)).mp h
      omega
    have det := maskedFour94 (output94 hk d fb ofs) mask (J j)
      (dir94 (at94 hk d (J j) 0)) (dir94 (at94 hk d (J j) (2*d+2)))
      (dir94 r) (dir94 t) (A x) 1 (fun i=>by
        have h := select94 hk d hd hw fb hf ofs (J j) (dir94 r) (dir94 t) (A x) i
        change _=(if i=J j then bit94 (dir94 r r)*bit94 (dir94 t t)+bit94 (dir94 t r)*bit94 (dir94 r t) else 0) at h
        simpa [dir94,ne,ne.symm,bit94] using h)
    apply bit_inj
    unfold mo256
    simpa [blockOffset256,hm,r,t,bit94] using det
end PEqualNP.Outside.L_meta_25600_aux

namespace PEqualNP.Outside.L_meta_25600_aux
open PEqualNP.Outside.L_meta_25594_aux

theorem chosenEmbedding256 {k d : Nat} (hk : 0<k) (hd : 0<d) (hkD : 4*d+4<k)
    (mask : Word94 k) (S : Finset (Fin k)) (hm : ∀ i ∈ S, mask i=true)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i≠j → 4*d+5≤(j.val+k-i.val)%k) :
    ∃ (J : Fin S.card → Fin k) (E : RW (Fin S.card) → Word94 k),
      (∀ j, mask (J j)=true) ∧
      (∀ i j, i≠j → 4*d+5≤((J j).val+k-(J i).val)%k) ∧
      (∀ x y, E (radd x y)=add94 (E x) (E y)) ∧
      (∀ q : Fin S.card × Fin 4, E (ru q)=dir94 (at94 hk d (J q.1) (blockOffset256 d q.2))) := by
  classical
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  let J := fun i : Fin S.card => (e.symm i).val
  let E := fun x : RW (Fin S.card) => blockEmbed256 hk d S (fun i j => x (e i) j)
  refine ⟨J,E,fun j => hm _ (e.symm j).property,?_,?_,?_⟩
  · intro i j hij
    apply hsep _ (e.symm i).property _ (e.symm j).property
    intro he
    exact hij (e.symm.injective (Subtype.ext he))
  · intro x y
    exact blockEmbed256_add hk d S _ _
  · rintro ⟨a,b⟩
    have ueq : (fun (i:S) (j:Fin 4) => ru (a,b) (e i) j) =
        fun (i:S) (j:Fin 4) => decide ((i,j)=(e.symm a,b)) := by
      funext i j
      simp only [ru, Prod.mk.injEq, Equiv.apply_eq_iff_eq_symm_apply]
    change blockEmbed256 hk d S _ = _
    rw [ueq]
    exact blockEmbed256_unit hk hd hkD S hsep (e.symm a,b)

end PEqualNP.Outside.L_meta_25600_aux

namespace PEqualNP.Outside.L_meta_25600_aux.Blocks

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

end PEqualNP.Outside.L_meta_25600_aux.Blocks

namespace PEqualNP.Outside.L_meta_25600_aux
open PEqualNP.Outside.L_meta_25594_aux

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

theorem xor_fold_diff {A : Type*} (pa : A → A → A) (l : List A) (f g : A → Bool) (x : A) :
    l.foldl (diffOn pa) (fun b => xor (f b) (g b)) x =
      xor (l.foldl (diffOn pa) f x) (l.foldl (diffOn pa) g x) := by
  induction l generalizing f g with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    have he : diffOn pa (fun b => xor (f b) (g b)) a =
        fun b => xor (diffOn pa f a b) (diffOn pa g a b) := by
      funext b
      simp only [diffOn]
      cases f b <;> cases g b <;> cases f (pa b a) <;> cases g (pa b a) <;> decide
    rw [he, ih]

theorem affineFourth {p} (aff lin : BlockW p → Bool)
    (ha : ∀ x u, aff (plusB x u) = xor (aff x) (lin u)) (v : Fin 4 → BlockW p) (x : BlockW p) :
    (List.ofFn v).foldl (diffOn plusB) aff x = false := by
  have h1 (u) : diffOn plusB aff u = fun _ => lin u := by
    funext a; rw [diffOn, ha]; cases aff a <;> cases lin u <;> decide
  have h2 (b : Bool) (u : BlockW p) : diffOn plusB (fun _ => b) u = fun _ => false := by
    funext a; exact Bool.xor_self _
  simp [List.ofFn_succ, List.foldl_cons, h1,h2]

theorem blockBound {p k l c : ℕ} (hp : 0<p)
    (test : BlockW p → Fin l → Bool) (ask : Word94 k → Fin c → Bool)
    (lift : BlockW p → Word94 k) (base : Word94 k)
    (htest : ∀ x y i, test (plusB x y) i = xor (test x i) (test y i))
    (hask : ∀ x y i, ask (add94 x y) i = xor (ask x i) (ask y i))
    (hlift : ∀ x y, lift (plusB x y) = add94 (lift x) (lift y))
    (actual : Word94 k → Bool) (core aff lin : BlockW p → Bool)
    (hag : ∀ x, test x = (fun _ => false) →
      xor (core x) (aff x) = actual (add94 base (lift x)))
    (haff : ∀ x u, aff (plusB x u) = xor (aff x) (lin u))
    (hlower : ∀ v x, (List.ofFn (v : Fin 4 → BlockW p)).foldl (diffOn plusB)
      (fun b => xor (core b) (blockProduct b)) x = false)
    (hdrop : ∀ (v : Fin 4 → Word94 k) x, ask x = ask base →
      (∀ j i, ask (v j) i = false) → (List.ofFn v).foldl (diffOn add94) actual x = false) :
    p ≤ c+l := by
  let lower := fun b => xor (core b) (blockProduct b)
  let pred := fun (x : BlockW p) => Fin.append (ask (lift x)) (test x)
  have hpLin (x y : BlockW p) (i : Fin (c+l)) : pred (plusB x y) i = xor (pred x i) (pred y i) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [pred,hlift] using hask (lift x) (lift y) j
    · simpa [pred] using htest x y j
  have predZero := zeroOfAdd pred hpLin
  have lowerEq : (fun input => xor (blockProduct input) (lower input)) = core := by
    funext b
    simp only [lower]; cases core b <;> cases blockProduct b <;> rfl
  have bound := PEqualNP.Outside.L_meta_25600_aux.Blocks.blockQueryLowerBound p 4 hp (by decide) lower hlower
  apply bound (c+l) pred hpLin (fun _ _ => false)
  intro v x hx hv
  rw [show (fun input => xor ((List.ofFn (fun block : Fin p => (List.ofFn (input block)).all id)).foldl xor false) (lower input)) = core from lowerEq]
  let P := fun a : BlockW p => test a = fun _ => false
  have closed (a b : BlockW p) (h : P a) (g : P b) : P (plusB a b) := by
    funext i; rw [htest]
    rw [show test a i = false from congrFun h i, show test b i = false from congrFun g i]; rfl
  have hpx : pred x = fun _ => false := hx.trans predZero
  have P0 : P x := by
    funext i; simpa [pred] using congrFun hpx (Fin.natAdd c i)
  have Pj (j) : P (v j) := by
    funext i; simpa [pred] using hv j (Fin.natAdd c i)
  have qa : ask (add94 base (lift x)) = ask base := by
    funext i; rw [hask]
    have he : ask (lift x) i = false := by simpa [pred] using congrFun hpx (Fin.castAdd l i)
    simp [he]
  have qv (j i) : ask (lift (v j)) i = false := by simpa [pred] using hv j (Fin.castAdd l i)
  have affpoint (a u : BlockW p) : add94 base (lift (plusB a u)) = add94 (add94 base (lift a)) (lift u) := by
    rw [hlift]; funext i; exact (Bool.xor_assoc ..).symm
  have tr := diff_pull_branch plusB add94 P closed _ lift affpoint _ actual hag (List.ofFn v)
    (fun u hu => by obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hu; exact Pj j) x P0
  rw [List.map_ofFn, xor_fold_diff, affineFourth aff lin haff, Bool.xor_false] at tr
  exact tr.trans (hdrop (lift ∘ v) _ qa qv)
end PEqualNP.Outside.L_meta_25600_aux

namespace PEqualNP.Outside.L_meta_25600_aux.Orbit

def ix {k : ℕ} (hk : 0 < k) (pos : ℕ) : Fin k := ⟨pos % k, Nat.mod_lt _ hk⟩

lemma ix_eq_iff {k : ℕ} (hk : 0 < k) (a b : ℕ) : ix hk a = ix hk b ↔ a % k = b % k := by
  simp [ix, Fin.ext_iff]

lemma ix_add_k {k : ℕ} (hk : 0 < k) (a : ℕ) : ix hk (a + k) = ix hk a := by
  rw [ix_eq_iff, Nat.add_mod_right]

lemma ix_self {k : ℕ} (hk : 0 < k) (a : Fin k) : ix hk a.val = a := by
  ext
  exact Nat.mod_eq_of_lt a.2

lemma ix_val_add {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ix hk ((ix hk a).val + b) = ix hk (a + b) := by
  rw [ix_eq_iff]
  simp only [ix]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ix_add_sub_mod {k : ℕ} (hk : 0 < k) (a s : ℕ) :
    ix hk ((ix hk a).val + k - s % k) = ix hk (a + (k - s % k)) := by
  have hs : s % k < k := Nat.mod_lt _ hk
  have h1 : (ix hk a).val + k - s % k = (ix hk a).val + (k - s % k) := by omega
  rw [h1, ix_val_add]

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

lemma zmod2_sum_three_cancel (a b : ZMod 2) : a + b + (a + b) = 0 := by
  fin_cases a <;> fin_cases b <;> decide

def rotLin {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  { toFun := fun w j => w (ix hk (j.val + k - s % k))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

lemma rotLin_bijective {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Function.Bijective (rotLin hk s) := by
  let inv : (Fin k → ZMod 2) → (Fin k → ZMod 2) := fun w j => w (ix hk (j.val + s % k))
  have hs : s % k < k := Nat.mod_lt _ hk
  have h1 : ∀ w, inv (rotLin hk s w) = w := by
    intro w
    ext j
    simp only [inv, rotLin, LinearMap.coe_mk, AddHom.coe_mk]
    have hidx : ix hk ((ix hk (j.val + s % k)).val + k - s % k) = j := by
      rw [ix_add_sub_mod hk (j.val + s % k) s]
      have heq : j.val + s % k + (k - s % k) = j.val + k := by omega
      rw [heq, ix_add_k, ix_self]
    rw [hidx]
  have h2 : ∀ w, rotLin hk s (inv w) = w := by
    intro w
    ext j
    simp only [inv, rotLin, LinearMap.coe_mk, AddHom.coe_mk]
    have hidx : ix hk ((ix hk (j.val + k - s % k)).val + s % k) = j := by
      rw [ix_val_add]
      have heq : j.val + k - s % k + s % k = j.val + k := by omega
      rw [heq, ix_add_k, ix_self]
    rw [hidx]
  exact Function.bijective_iff_has_inverse.mpr ⟨inv, h1, h2⟩

def mixLin {k : ℕ} (hk : 0 < k) (d : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  { toFun := fun z m => z m + z (ix hk (m.val + d)) + z (ix hk (m.val + k - d % k))
    map_add' := fun x y => by ext m; simp only [Pi.add_apply]; ring
    map_smul' := fun c x => by ext m; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

def orb {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) : Fin k :=
  ix hk (r.val + t * d)

lemma orb_add_one {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) :
    ix hk ((orb hk d r t).val + d) = orb hk d r (t + 1) := by
  simp only [orb, ix_val_add]
  congr 1; ring

lemma orb_sub_one {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) :
    ix hk ((orb hk d r (t + 1)).val + k - d % k) = orb hk d r t := by
  simp only [orb, ix_add_sub_mod]
  rw [ix_eq_iff]
  have hd : d % k < k := Nat.mod_lt _ hk
  have htd : (t + 1) * d = t * d + d := by ring
  have h1 : r.val + (t + 1) * d + (k - d % k) = (r.val + t * d) + (d + k - d % k) := by
    rw [htd]; omega
  rw [h1, Nat.add_mod]
  have h2 : (d + k - d % k) % k = 0 := by
    have hdiv := Nat.div_add_mod d k
    have hmul : (d / k + 1) * k = k * (d / k) + k := by ring
    have h3 : d + k - d % k = (d / k + 1) * k := by rw [hmul]; omega
    rw [h3, Nat.mul_mod_left]
  rw [h2, Nat.add_zero, Nat.mod_mod]

lemma orb_period {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) :
    orb hk d r (t + k / Nat.gcd k d) = orb hk d r t := by
  simp only [orb, ix_eq_iff]
  have hg0 : 0 < Nat.gcd k d := Nat.gcd_pos_of_pos_left d hk
  have h1k : Nat.gcd k d * (k / Nat.gcd k d) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k d)
  have h1d : Nat.gcd k d * (d / Nat.gcd k d) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right k d)
  have hmul : (k / Nat.gcd k d) * d = k * (d / Nat.gcd k d) := by
    apply Nat.eq_of_mul_eq_mul_left hg0
    calc
      Nat.gcd k d * ((k / Nat.gcd k d) * d) = (Nat.gcd k d * (k / Nat.gcd k d)) * d := by ring
      _ = k * d := by rw [h1k]
      _ = k * (Nat.gcd k d * (d / Nat.gcd k d)) := by rw [h1d]
      _ = Nat.gcd k d * (k * (d / Nat.gcd k d)) := by ring
  have h1 : r.val + (t + k / Nat.gcd k d) * d = (r.val + t * d) + k * (d / Nat.gcd k d) := by
    rw [Nat.add_mul, hmul]; ring
  rw [h1, Nat.add_mul_mod_self_left]

lemma orb_bijective {k : ℕ} (hk : 0 < k) (d : ℕ) (hd : 0 < d) :
    Function.Bijective (fun p : Fin (Nat.gcd k d) × Fin (k / Nat.gcd k d) =>
      orb hk d p.1 p.2.val) := by
  have hg_pos : 0 < Nat.gcd k d := Nat.gcd_pos_of_pos_left d hk
  have hg_dvd_k : Nat.gcd k d ∣ k := Nat.gcd_dvd_left k d
  have hg_dvd_d : Nat.gcd k d ∣ d := Nat.gcd_dvd_right k d
  have hk_eq : Nat.gcd k d * (k / Nat.gcd k d) = k := Nat.mul_div_cancel' hg_dvd_k
  have hd_eq : Nat.gcd k d * (d / Nat.gcd k d) = d := Nat.mul_div_cancel' hg_dvd_d
  have hcop : Nat.Coprime (k / Nat.gcd k d) (d / Nat.gcd k d) :=
    Nat.coprime_div_gcd_div_gcd hg_pos
  have hcard : Fintype.card (Fin (Nat.gcd k d) × Fin (k / Nat.gcd k d)) = Fintype.card (Fin k) := by
    simp [hk_eq]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, hcard⟩
  intro ⟨r1, t1⟩ ⟨r2, t2⟩ heq
  simp only [orb, ix_eq_iff] at heq
  have hr_eq : r1 = r2 := by
    have hmod_g : ∀ a, (a % k) % Nat.gcd k d = a % Nat.gcd k d := fun a =>
      Nat.mod_mod_of_dvd a hg_dvd_k
    have h1 := congrArg (fun x => x % Nat.gcd k d) heq
    rw [hmod_g, hmod_g] at h1
    have hmul_g : ∀ t, (t * d) % Nat.gcd k d = 0 := fun t =>
      Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hg_dvd_d t)
    rw [Nat.add_mod, hmul_g, Nat.add_zero, Nat.mod_mod,
      Nat.add_mod, hmul_g, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt r1.2, Nat.mod_eq_of_lt r2.2] at h1
    exact Fin.ext h1
  subst hr_eq
  have ht_eq : t1 = t2 := by
    have haux : ∀ a b : Fin (k / Nat.gcd k d), a.val ≤ b.val →
        (r1.val + a.val * d) % k = (r1.val + b.val * d) % k → a = b := by
      intro a b hab hmod
      have hdvd : k ∣ (r1.val + b.val * d) - (r1.val + a.val * d) := by
        exact (Nat.modEq_iff_dvd' (by nlinarith)).mp hmod
      have hsub : (r1.val + b.val * d) - (r1.val + a.val * d) = (b.val - a.val) * d := by
        rw [Nat.add_sub_add_left, ← Nat.sub_mul]
      have hdvd' : (Nat.gcd k d * (k / Nat.gcd k d)) ∣
          (b.val - a.val) * (Nat.gcd k d * (d / Nat.gcd k d)) := by
        rwa [hk_eq, hd_eq, ← hsub]
      have hdvd2 : (k / Nat.gcd k d) ∣ (b.val - a.val) * (d / Nat.gcd k d) := by
        have hrew : (b.val - a.val) * (Nat.gcd k d * (d / Nat.gcd k d)) =
            Nat.gcd k d * ((b.val - a.val) * (d / Nat.gcd k d)) := by ring
        rw [hrew] at hdvd'
        exact (mul_dvd_mul_iff_left (ne_of_gt hg_pos)).mp hdvd'
      have hdvd3 : (k / Nat.gcd k d) ∣ (b.val - a.val) := hcop.dvd_of_dvd_mul_right hdvd2
      have hlt : b.val - a.val < k / Nat.gcd k d := by omega
      have h0 : b.val - a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd3 hlt
      ext; omega
    by_cases hle : t1.val ≤ t2.val
    · exact haux t1 t2 hle heq
    · exact (haux t2 t1 (by omega) heq.symm).symm
  subst ht_eq
  rfl

lemma ker_seq_period3 {k : ℕ} (hk : 0 < k) (d : ℕ)
    (z : Fin k → ZMod 2) (hz : mixLin hk d z = 0)
    (r : Fin (Nat.gcd k d)) (t : ℕ) :
    z (orb hk d r t) =
      if t % 3 = 0 then z (orb hk d r 0)
      else if t % 3 = 1 then z (orb hk d r 1)
      else z (orb hk d r 0) + z (orb hk d r 1) := by
  have hstep : ∀ n : ℕ, z (orb hk d r (n + 2)) = z (orb hk d r (n + 1)) + z (orb hk d r n) := by
    intro n
    have h0 := congrFun hz (orb hk d r (n + 1))
    simp only [mixLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
    rw [orb_add_one hk d r (n + 1), orb_sub_one hk d r n] at h0
    have h1 := congrArg (fun x => x + z (orb hk d r (n + 2))) h0
    simp only [zero_add] at h1
    have hlhs : z (orb hk d r (n + 1)) + z (orb hk d r (n + 2)) + z (orb hk d r n) +
        z (orb hk d r (n + 2)) = z (orb hk d r (n + 1)) + z (orb hk d r n) := by
      have hz2 := zmod2_add_self (z (orb hk d r (n + 2)))
      calc
        z (orb hk d r (n + 1)) + z (orb hk d r (n + 2)) + z (orb hk d r n) +
            z (orb hk d r (n + 2))
            = z (orb hk d r (n + 1)) + z (orb hk d r n) +
              (z (orb hk d r (n + 2)) + z (orb hk d r (n + 2))) := by ring
        _ = z (orb hk d r (n + 1)) + z (orb hk d r n) := by rw [hz2, add_zero]
    rw [hlhs] at h1
    exact h1.symm
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    match t with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      rw [hstep n, ih (n + 1) (by omega), ih n (by omega)]
      have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hmod with h0 | h1 | h2
      · have h1' : (n + 1) % 3 = 1 := by omega
        have h2' : (n + 2) % 3 = 2 := by omega
        simp only [h0, h1', h2', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one]
        ring
      · have h1' : (n + 1) % 3 = 2 := by omega
        have h2' : (n + 2) % 3 = 0 := by omega
        simp only [h1, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_add_self (z (orb hk d r 1))
        calc
          z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 1)
              = z (orb hk d r 0) + (z (orb hk d r 1) + z (orb hk d r 1)) := by ring
          _ = z (orb hk d r 0) := by rw [this, add_zero]
      · have h1' : (n + 1) % 3 = 0 := by omega
        have h2' : (n + 2) % 3 = 1 := by omega
        simp only [h2, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_add_self (z (orb hk d r 0))
        calc
          z (orb hk d r 0) + (z (orb hk d r 0) + z (orb hk d r 1))
              = (z (orb hk d r 0) + z (orb hk d r 0)) + z (orb hk d r 1) := by ring
          _ = z (orb hk d r 1) := by rw [this, zero_add]

lemma finrank_ker_mixLin {k : ℕ} (hk : 0 < k) (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (LinearMap.ker (mixLin hk d)) =
      if 3 ∣ k / Nat.gcd k d then 2 * Nat.gcd k d else 0 := by
  let g := Nat.gcd k d
  let L := k / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hk
  have hg_dvd_k : g ∣ k := Nat.gcd_dvd_left k d
  have hL_pos : 0 < L := Nat.div_pos (Nat.le_of_dvd hk hg_dvd_k) hg_pos
  let e : (Fin g × Fin L) ≃ Fin k := Equiv.ofBijective _ (orb_bijective hk d hd)
  split_ifs with hsing
  · have hL3 : 3 ≤ L := Nat.le_of_dvd hL_pos hsing
    let mkVec : (Fin g × Fin 2 → ZMod 2) → (Fin k → ZMod 2) := fun a v =>
      let p := e.symm v
      if p.2.val % 3 = 0 then a (p.1, 0)
      else if p.2.val % 3 = 1 then a (p.1, 1)
      else a (p.1, 0) + a (p.1, 1)
    have hmk_orb : ∀ a (r : Fin g) (t : ℕ),
        mkVec a (orb hk d r t) =
          if t % 3 = 0 then a (r, 0)
          else if t % 3 = 1 then a (r, 1)
          else a (r, 0) + a (r, 1) := by
      intro a r t
      have hdiv : t = (t / L) * L + t % L := (Nat.div_add_mod' t L).symm
      have horb_mod : orb hk d r t = orb hk d r (t % L) := by
        have hstep : ∀ q : ℕ, orb hk d r (q * L + t % L) = orb hk d r (t % L) := by
          intro q
          induction q with
          | zero => simp
          | succ q ih =>
            rw [show (q + 1) * L + t % L = (q * L + t % L) + L by ring, orb_period, ih]
        conv_lhs => rw [hdiv]
        exact hstep (t / L)
      have he_symm : e.symm (orb hk d r (t % L)) = (r, ⟨t % L, Nat.mod_lt _ hL_pos⟩) := by
        apply e.injective
        rw [Equiv.apply_symm_apply]
        rfl
      have hmod3 : (t % L) % 3 = t % 3 := Nat.mod_mod_of_dvd t hsing
      simp only [mkVec, horb_mod, he_symm, hmod3]
    have hmk_ker : ∀ a, mixLin hk d (mkVec a) = 0 := by
      intro a
      ext v
      have hv : v = orb hk d (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
      let r := (e.symm v).1
      let t := (e.symm v).2.val
      have hv_eq : v = orb hk d r (t + L) := by
        rw [orb_period]; exact hv
      simp only [mixLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      rw [hv_eq, orb_add_one, show t + L = (t + L - 1) + 1 by omega, orb_sub_one]
      rw [hmk_orb, hmk_orb, hmk_orb]
      have hmod : (t + L - 1) % 3 = 0 ∨ (t + L - 1) % 3 = 1 ∨ (t + L - 1) % 3 = 2 := by omega
      rcases hmod with h0 | h1 | h2
      · have h1' : (t + L - 1 + 1) % 3 = 1 := by omega
        have h2' : (t + L - 1 + 1 + 1) % 3 = 2 := by omega
        simp only [h0, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_sum_three_cancel (a (r, 0)) (a (r, 1))
        calc
          a (r, 1) + (a (r, 0) + a (r, 1)) + a (r, 0)
              = a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) := by ring
          _ = 0 := this
      · have h1' : (t + L - 1 + 1) % 3 = 2 := by omega
        have h2' : (t + L - 1 + 1 + 1) % 3 = 0 := by omega
        simp only [h1, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_sum_three_cancel (a (r, 0)) (a (r, 1))
        calc
          a (r, 0) + a (r, 1) + a (r, 0) + a (r, 1)
              = a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) := by ring
          _ = 0 := this
      · have h1' : (t + L - 1 + 1) % 3 = 0 := by omega
        have h2' : (t + L - 1 + 1 + 1) % 3 = 1 := by omega
        simp only [h2, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        exact zmod2_sum_three_cancel (a (r, 0)) (a (r, 1))
    let Ψ : (Fin g × Fin 2 → ZMod 2) →ₗ[ZMod 2] LinearMap.ker (mixLin hk d) :=
      { toFun := fun a => ⟨mkVec a, hmk_ker a⟩
        map_add' := fun a1 a2 => by
          apply Subtype.ext; ext v; simp only [mkVec, Submodule.coe_add, Pi.add_apply]
          split_ifs <;> ring
        map_smul' := fun c a => by
          apply Subtype.ext; ext v
          simp only [mkVec, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> ring }
    have hΨ_bij : Function.Bijective Ψ := by
      constructor
      · intro a1 a2 heq
        have hval : mkVec a1 = mkVec a2 := congrArg Subtype.val heq
        ext ⟨r, c⟩
        fin_cases c
        · have h0 := congrFun hval (orb hk d r 0)
          simpa [hmk_orb] using h0
        · have h1 := congrFun hval (orb hk d r 1)
          simpa [hmk_orb] using h1
      · rintro ⟨z, hz⟩
        let a : Fin g × Fin 2 → ZMod 2 := fun rc =>
          if rc.2.val = 0 then z (orb hk d rc.1 0) else z (orb hk d rc.1 1)
        refine ⟨a, ?_⟩
        apply Subtype.ext
        ext v
        have hv : v = orb hk d (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
        conv_lhs => rw [hv]
        conv_rhs => rw [hv]
        change mkVec a (orb hk d (e.symm v).1 (e.symm v).2.val) =
          z (orb hk d (e.symm v).1 (e.symm v).2.val)
        rw [hmk_orb, ker_seq_period3 hk d z hz]
        simp [a]
    have hequiv := LinearEquiv.ofBijective Ψ hΨ_bij
    rw [← hequiv.finrank_eq]
    simp [g, Nat.mul_comm]
  · have hker_bot : LinearMap.ker (mixLin hk d) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro z hz
      ext v
      have hv : v = orb hk d (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
      rw [hv]
      let r := (e.symm v).1
      have h0 : z (orb hk d r L) = z (orb hk d r 0) := by
        simpa using congrArg z (orb_period hk d r 0)
      have h1 : z (orb hk d r (L + 1)) = z (orb hk d r 1) := by
        have hp := orb_period hk d r 1
        rw [show 1 + L = L + 1 by omega] at hp
        exact congrArg z hp
      rw [ker_seq_period3 hk d z hz r L] at h0
      rw [ker_seq_period3 hk d z hz r (L + 1)] at h1
      have hmod : L % 3 = 1 ∨ L % 3 = 2 := by
        have hne : L % 3 ≠ 0 := fun h => hsing (Nat.dvd_of_mod_eq_zero h)
        omega
      have hzero01 : z (orb hk d r 0) = 0 ∧ z (orb hk d r 1) = 0 := by
        rcases hmod with hm1 | hm2
        · have hm1' : (L + 1) % 3 = 2 := by omega
          simp only [hm1, hm1', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
            OfNat.ofNat_ne_one] at h0 h1
          have hz0 : z (orb hk d r 0) = 0 := by
            have := congrArg (fun x => x + z (orb hk d r 1)) h1
            have hrhs : z (orb hk d r 1) + z (orb hk d r 1) = 0 := zmod2_add_self _
            have hlhs : z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 1) =
                z (orb hk d r 0) := by
              rw [add_assoc, hrhs, add_zero]
            rw [hlhs, hrhs] at this
            exact this
          exact ⟨hz0, by rw [h0, hz0]⟩
        · have hm2' : (L + 1) % 3 = 0 := by omega
          simp only [hm2, hm2', ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at h0 h1
          have hz1 : z (orb hk d r 1) = 0 := by
            have := congrArg (fun x => x + z (orb hk d r 0)) h0
            have hrhs : z (orb hk d r 0) + z (orb hk d r 0) = 0 := zmod2_add_self _
            have hlhs : z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 0) =
                z (orb hk d r 1) := by
              calc
                z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 0)
                    = (z (orb hk d r 0) + z (orb hk d r 0)) + z (orb hk d r 1) := by ring
                _ = z (orb hk d r 1) := by rw [hrhs, zero_add]
            rw [hlhs, hrhs] at this
            exact this
          exact ⟨by rw [h1, hz1], hz1⟩
      rw [ker_seq_period3 hk d z hz r (e.symm v).2.val, hzero01.1, hzero01.2]
      simp
    rw [hker_bot]
    simp

lemma ker_loss_of_mix_rot {k : ℕ} (hk : 0 < k) (d : ℕ) (hd : 0 < d) (s : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.ker ((mixLin hk d).comp (rotLin hk s))) =
      if (k / Nat.gcd k d) % 3 = 0 then 2 * Nat.gcd k d else 0 := by
  have hr : LinearMap.range ((mixLin hk d).comp (rotLin hk s)) = LinearMap.range (mixLin hk d) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr (rotLin_bijective hk s).surjective,
      Submodule.map_top]
  have h1 := ((mixLin hk d).comp (rotLin hk s)).finrank_range_add_finrank_ker
  have h2 := (mixLin hk d).finrank_range_add_finrank_ker
  rw [hr] at h1
  have hker := finrank_ker_mixLin hk d hd
  simp only [Nat.dvd_iff_mod_eq_zero] at hker
  omega

end PEqualNP.Outside.L_meta_25600_aux.Orbit
namespace PEqualNP.Outside.L_meta_25600_aux.Kernel25600

open LinearMap Module PEqualNP.Outside.L_meta_25600_aux.Orbit

private def enc (b : Bool) : ZMod 2 := if b then 1 else 0
private def dec (z : ZMod 2) : Bool := decide (z = 1)
private lemma enc_xor (a b : Bool) : enc (xor a b) = enc a + enc b := by cases a <;> cases b <;> decide
private lemma dec_add (a b : ZMod 2) : dec (a+b) = xor (dec a) (dec b) := by fin_cases a <;> fin_cases b <;> decide
private lemma enc_dec (a : ZMod 2) : enc (dec a) = a := by
  by_cases ha : a = 0
  · subst a; rfl
  · rw [zmod2_eq_one_of_ne_zero ha]; rfl
private lemma dec_enc (b : Bool) : dec (enc b) = b := by cases b <;> decide

private def wordMap {i j : Type*} (A : (i → ZMod 2) →ₗ[ZMod 2] (j → ZMod 2))
    (x : i → Bool) (t : j) := dec (A (fun r => enc (x r)) t)

private theorem wordMap_add {i j : Type*} (A : (i → ZMod 2) →ₗ[ZMod 2] (j → ZMod 2))
    (x y : i → Bool) (t : j) : wordMap A (fun r => xor (x r) (y r)) t =
      xor (wordMap A x t) (wordMap A y t) := by
  have h : (fun r => enc (xor (x r) (y r))) = (fun r => enc (x r)) + (fun r => enc (y r)) := by
    funext r; exact enc_xor _ _
  simp only [wordMap, h, map_add, Pi.add_apply, dec_add]

theorem mix_section {k : ℕ} (hk : 0 < k) (d : ℕ) (hd : 0 < d) (hdk : d < k) (s : ℕ) :
    let W := Fin k → Bool
    let idx := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let add := fun (x y : W) (i : Fin k) => xor (x i) (y i)
    let rot := fun (s' : ℕ) (x : W) (i : Fin k) => x (idx (i.val + k - s' % k))
    let mix := fun (x : W) (i : Fin k) => xor (xor (x i) (x (idx (i.val + d)))) (x (idx (i.val + k - d)))
    let loss := if (k / Nat.gcd k d) % 3 = 0 then 2 * Nat.gcd k d else 0
    ∃ (lift : W → W) (test : W → Fin loss → Bool),
      (∀ x y i, lift (add x y) i = xor (lift x i) (lift y i)) ∧
      (∀ x y i, test (add x y) i = xor (test x i) (test y i)) ∧
      ∀ y, (∀ i, test y i = false) → mix (rot s (lift y)) = y := by
  classical
  intro W idx add rot mix loss
  let V := Fin k → ZMod 2
  let A := (mixLin hk d).comp (rotLin hk s)
  let M := range A
  have hr := A.finrank_range_add_finrank_ker
  have hq := M.finrank_quotient_add_finrank
  have ha : finrank (ZMod 2) (ker A) = loss := ker_loss_of_mix_rot hk d hd s
  have hc : finrank (ZMod 2) (V ⧸ M) = loss := by
    change finrank (ZMod 2) M + finrank (ZMod 2) (ker A) = finrank (ZMod 2) V at hr
    change finrank (ZMod 2) (V ⧸ M) + finrank (ZMod 2) M = finrank (ZMod 2) V at hq
    omega
  let e := (Module.finBasisOfFinrankEq (ZMod 2) (V ⧸ M) hc).equivFun
  let T := e.toLinearMap.comp M.mkQ
  obtain ⟨sec, hs⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  obtain ⟨proj, hp⟩ := M.subtype.exists_leftInverse_of_injective M.ker_subtype
  let L := sec.comp proj
  refine ⟨wordMap L, wordMap T, wordMap_add L, wordMap_add T, ?_⟩
  intro y hy
  let y' : V := fun i => enc (y i)
  have htest : T y' = 0 := by
    funext i
    have hi := congrArg enc (hy i)
    change enc (dec (T y' i)) = enc false at hi
    change T y' i = (0 : ZMod 2)
    rw [enc_dec] at hi
    exact hi
  have hm : y' ∈ M := by
    apply (Submodule.Quotient.mk_eq_zero M).mp
    apply e.injective
    simpa [T] using htest
  let z : M := ⟨y', hm⟩
  have hz : proj y' = z := LinearMap.congr_fun hp z
  have hsec : A (sec z) = y' := congrArg Subtype.val (LinearMap.congr_fun hs z)
  have hl : A (L y') = y' := by change A (sec (proj y')) = y'; rwa [hz]
  funext i
  have h := congrArg dec (congrFun hl i)
  simp only [A, mixLin, rotLin, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Nat.mod_eq_of_lt hdk, dec_add, y', dec_enc] at h
  exact h

end PEqualNP.Outside.L_meta_25600_aux.Kernel25600

namespace PEqualNP.Outside.L_meta_25600_aux.Kernel25600
open PEqualNP.Outside.L_meta_25594_aux

def rotate {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Word94 k) (i : Fin k) := x (idx94 hk (i.val+k-s%k))
def masked {k : ℕ} (mask x : Word94 k) := (List.ofFn (fun i => mask i && x i)).foldl xor false

theorem rot_add {k} (hk : 0<k) (s) (x y : Word94 k) :
    rotate hk s (add94 x y) = add94 (rotate hk s x) (rotate hk s y) := rfl

theorem rawMix_add {k} (hk : 0<k) (d) (x y : Word94 k) :
    rawMix94 hk d (add94 x y) = add94 (rawMix94 hk d x) (rawMix94 hk d y) := by
  funext i
  simp only [rawMix94, add94, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

private theorem parity_add_list (a : List (Bool × Bool)) (u v : Bool) :
    (a.map (fun x => xor x.1 x.2)).foldl xor (xor u v) =
      xor ((a.map Prod.fst).foldl xor u) ((a.map Prod.snd).foldl xor v) := by
  induction a generalizing u v with
  | nil => rfl
  | cons p a ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [show xor (xor u v) (xor p.1 p.2) = xor (xor u p.1) (xor v p.2) by
      simp only [Bool.xor_comm, Bool.xor_left_comm],ih]

theorem masked_add {k} (mask x y : Word94 k) : masked mask (add94 x y) = xor (masked mask x) (masked mask y) := by
  unfold masked
  have h := parity_add_list (List.ofFn fun i : Fin k => (mask i && x i, mask i && y i)) false false
  simp only [List.map_ofFn, Bool.false_xor] at h
  have e : (fun i => mask i && add94 x y i) = (fun i => xor (mask i && x i) (mask i && y i)) := by
    funext i
    dsimp only [add94]
    cases mask i <;> rfl
  rw [e]
  exact h

theorem add_insert {k} (x y z : Word94 k) : add94 (add94 x y) z = add94 (add94 x z) y := by
  funext i
  simp only [add94, Bool.xor_comm, Bool.xor_left_comm]

def initial {k} (hk : 0<k) (d s : ℕ) (name x : Word94 k) := rawMix94 hk d (add94 (rotate hk s x) name)

def correction {k} (hk : 0<k) (t : ℕ) (lift : Word94 k→Word94 k) (q0 base c1 : Word94 k) :=
  add94 (rotate hk t (lift q0)) (add94 (rotate hk t base) c1)

def actual {k} (hk : 0<k) (d s t h : ℕ) (name c1 c2 mask key : Word94 k) :=
  let inp := initial hk d s name key
  let mid := add94 (rawStep94 hk inp) (add94 (rotate hk t key) c1)
  masked mask (add94 (rawStep94 hk (rawMix94 hk d mid)) (add94 (rotate hk h key) c2))

theorem initial_add {k} (hk : 0<k) (d s : ℕ) (name base v : Word94 k) :
    initial hk d s name (add94 base v) = add94 (initial hk d s name base) (rawMix94 hk d (rotate hk s v)) := by
  unfold initial
  rw [rot_add, add_insert, rawMix_add]

theorem round_agrees {k} (hk : 0<k) (d s t h : ℕ) (name c1 c2 mask base : Word94 k)
    (lift : Word94 k→Word94 k) (hlift : ∀ x y, lift (add94 x y) = add94 (lift x) (lift y))
    (y : Word94 k) (valid : rawMix94 hk d (rotate hk s (lift y)) = y) :
    let q0 := initial hk d s name base
    let fb := fun a => rotate hk t (lift a)
    let ofs := correction hk t lift q0 base c1
    xor (masked mask (output94 hk d fb ofs (add94 q0 y)))
        (masked mask (add94 (rotate hk h (add94 base (lift y))) c2)) =
      actual hk d s t h name c1 c2 mask (add94 base (lift y)) := by
  intro q0 fb ofs
  rw [←masked_add]
  unfold actual output94 middle94
  rw [initial_add, valid]
  have e : add94 (fb (add94 q0 y)) ofs = add94 (rotate hk t (add94 base (lift y))) c1 := by
    dsimp only [fb,ofs,correction]
    rw [hlift,rot_add,rot_add]
    funext i
    change ((rotate hk t (lift q0) i ^^ rotate hk t (lift y) i) ^^
      (rotate hk t (lift q0) i ^^ (rotate hk t base i ^^ c1 i))) =
      ((rotate hk t base i ^^ rotate hk t (lift y) i) ^^ c1 i)
    cases rotate hk t (lift q0) i <;> cases rotate hk t (lift y) i <;>
      cases rotate hk t base i <;> cases c1 i <;> decide
  rw [e]

theorem outer_add {k} (hk : 0<k) (h : ℕ) (mask c2 base u v : Word94 k) :
  masked mask (add94 (rotate hk h (add94 base (add94 u v))) c2) =
    xor (masked mask (add94 (rotate hk h (add94 base u)) c2)) (masked mask (rotate hk h v)) := by
  rw [←masked_add]
  congr 1
  funext i
  simp only [rotate, add94, Bool.xor_comm, Bool.xor_left_comm]

end PEqualNP.Outside.L_meta_25600_aux.Kernel25600

open PEqualNP.Outside.L_meta_25600_aux PEqualNP.Outside.L_meta_25594_aux

theorem PEqualNP.Outside.L_meta_25600 : (∀ (k d : ℕ) (hk : 0 < k), 0 < d → 4 * d + 4 < k →
  let W := Fin k → Bool
  let idx := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (i : Fin k) => xor (x i) (y i)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (idx (i.val + k - s % k))
  let mix := fun (x : W) (i : Fin k) =>
    xor (xor (x i) (x (idx (i.val + d)))) (x (idx (i.val + k - d)))
  let step := fun (x : W) (i : Fin k) =>
    xor (x i) (!(x (idx (i.val + 1))) && x (idx (i.val + 2)))
  let diff := fun (f : W → Bool) (v x : W) => xor (f x) (f (add x v))
  let g := Nat.gcd k d
  let lost := if (k / g) % 3 = 0 then 2 * g else 0
  ∀ (s t h : ℕ) (name c₁ c₂ mask : W),
    let observed := fun (key : W) =>
      let initial := mix (add (rot s key) name)
      let middle := add (step initial) (add (rot t key) c₁)
      let out := add (step (mix middle)) (add (rot h key) c₂)
      (List.ofFn (fun bit : Fin k => mask bit && out bit)).foldl xor false
    ∀ (c : ℕ) (query : W → Fin c → Bool),
      (∀ x y i, query (add x y) i = xor (query x i) (query y i)) →
      ∀ (base : W),
        (∀ (v : Fin 4 → W) (x : W), query x = query base →
          (∀ j i, query (v j) i = false) →
          (List.ofFn v).foldl diff observed x = false) →
        let stride := 4 * d + 5
        let weight := (Finset.univ.filter (fun pos : Fin k => mask pos = true)).card
        (∀ chosen : Finset (Fin k), (∀ i ∈ chosen, mask i = true) →
          (∀ i ∈ chosen, ∀ j ∈ chosen, i ≠ j →
            stride ≤ (j.val + k - i.val) % k) → chosen.card ≤ c + lost) ∧
        (k / stride) * weight ≤ k * (c + lost)) := by
  intro k d hk hd hw
  dsimp only
  intro s t h name c1 c2 mask c query hquery base hdrop
  let lost := if (k / k.gcd d) % 3 = 0 then 2 * k.gcd d else 0
  change (∀ S : Finset (Fin k), (∀ i ∈ S, mask i = true) →
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → 4 * d + 5 ≤ (j.val+k-i.val)%k) → S.card ≤ c+lost) ∧ _
  suffices chosen : ∀ S : Finset (Fin k), (∀ i ∈ S, mask i = true) →
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → 4*d+5 ≤ (j.val+k-i.val)%k) → S.card ≤ c+lost by
    exact ⟨chosen, Packing25600.average hk (by omega) mask chosen⟩
  intro S hm hs
  by_cases hp : 0 < S.card
  · obtain ⟨J,E,hJ,hsep,hE,hu⟩ := chosenEmbedding256 hk hd hw mask S hm hs
    obtain ⟨lift,test,hlift,htest,hsec⟩ := Kernel25600.mix_section hk d hd (by omega) s
    have hl (x y) : lift (add94 x y) = add94 (lift x) (lift y) := funext (hlift x y)
    let q0 := Kernel25600.initial hk d s name base
    let fb := fun a => Kernel25600.rotate hk t (lift a)
    let ofs := Kernel25600.correction hk t lift q0 base c1
    let A := fun x => add94 q0 (E x)
    have hA (x y) : A (radd x y) = add94 (A x) (E y) := by
      dsimp only [A]; rw [hE]; funext i; exact (Bool.xor_assoc ..).symm
    have hf (a b) : fb (add94 a b) = add94 (fb a) (fb b) := by
      dsimp only [fb]; rw [hl]; rfl
    let core := fun x => mo256 hk d fb ofs mask (A x)
    let aff := fun x => Kernel25600.masked mask (add94 (Kernel25600.rotate hk h (add94 base (lift (E x)))) c2)
    let lin := fun x => Kernel25600.masked mask (Kernel25600.rotate hk h (lift (E x)))
    refine blockBound hp (fun x => test (E x)) query (fun x => lift (E x)) base ?_ hquery ?_
      (Kernel25600.actual hk d s t h name c1 c2 mask) core aff lin ?_ ?_ ?_ hdrop
    · intro x y i; change test (E (radd x y)) i = _; rw [hE]; exact htest _ _ _
    · intro x y; change lift (E (radd x y)) = _; rw [hE,hl]
    · intro x hx
      exact Kernel25600.round_agrees hk d s t h name c1 c2 mask base lift hl (E x)
        (hsec (E x) (fun i => congrFun hx i))
    · intro x u
      change Kernel25600.masked mask (add94 (Kernel25600.rotate hk h (add94 base (lift (E (radd x u))))) c2) = _
      rw [hE,hl]
      exact Kernel25600.outer_add hk h mask c2 base _ _
    · intro v x
      have hh := restriction256 hk hd hw fb hf ofs mask J hJ hsep A E hA hu (v 0) (v 1) (v 2) (v 3) x
      exact hh
  · omega
