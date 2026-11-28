import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_900_aux

open Finset
open scoped BigOperators

abbrev F := ZMod 2
abbrev I (k : ℕ) := Fin k
abbrev W (k : ℕ) := I k → F

theorem casesF (x : F) : x = 0 ∨ x = 1 := by fin_cases x <;> first | left; rfl | right; rfl
theorem sqF (x : F) : x*x=x := by rcases casesF x with rfl|rfl <;> decide

variable {k m : ℕ} {X : Type*} [Fintype X]

def mon (v : I k → X → F) (s : Finset (I k)) : X → F := ∏ i ∈ s, v i

omit [Fintype X] in
theorem mulMon (v : I k → X → F) (s : Finset (I k)) (i : I k) :
    v i * mon v s = mon v (insert i s) := by
  classical
  by_cases h : i ∈ s
  · rw [Finset.insert_eq_of_mem h]
    conv_rhs => rw [← Finset.insert_erase h]
    conv_lhs => rw [← Finset.insert_erase h]
    simp only [mon, Finset.prod_insert, Finset.notMem_erase, not_false_eq_true, ← mul_assoc]
    congr 1
    exact funext fun x => sqF _
  · simp [mon, h]

def good (f : Finset (I k)) (a b : Fin m → I k) :=
  f.powerset.filter fun s => ∀ i, a i ≠ b i → ¬(a i ∈ s ∧ b i ∈ s)

theorem footprint (f : Finset (I k)) (a b : Fin m → I k) (v : I k → X → F)
    (sep : ∀ x y, (∀ j ∈ f, v j x = v j y) → x=y)
    (c : Fin m → F) (d : Fin m → I k → F)
    (eqn : ∀ i, a i ∈ f → b i ∈ f →
      v (a i) * v (b i) = Function.const X (c i) + ∑ j ∈ f, d i j • v j) :
    Fintype.card X ≤ (good f a b).card := by
  classical
  let P := Submodule.span F (Set.range (fun s : ↥(good f a b) => mon v s.val))
  have pos : ∀ n (s : Finset (I k)), s.card = n → s ⊆ f → mon v s ∈ P := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro s hn hs
      by_cases hg : s ∈ good f a b
      · exact Submodule.subset_span ⟨⟨s,hg⟩,rfl⟩
      simp only [good, mem_filter, mem_powerset, hs, true_and, not_forall, not_not] at hg
      obtain ⟨i,hi,ha,hb⟩ := hg
      let u := (s.erase (a i)).erase (b i)
      have hu : u ⊆ s := (erase_subset _ _).trans (erase_subset _ _)
      have hau : a i ∉ u := fun h => notMem_erase _ _ (mem_of_mem_erase h)
      have hbu : b i ∉ u := notMem_erase _ _
      have hb' : b i ∈ s.erase (a i) := mem_erase.mpr ⟨Ne.symm hi,hb⟩
      have hcard : u.card + 2 = n := by
        dsimp [u]
        have := card_erase_add_one ha
        have := card_erase_add_one hb'
        omega
      have rest := ih u.card (by omega) u rfl (hu.trans hs)
      have hins (j : I k) (hj : j ∈ f) : mon v (insert j u) ∈ P := by
        have := card_insert_le j u
        exact ih _ (by omega) _ rfl (insert_subset hj (hu.trans hs))
      have e : s = insert (a i) (insert (b i) u) := by simp [u, insert_erase hb', insert_erase ha]
      rw [e, ← mulMon, ← mulMon, ← mul_assoc, eqn i (hs ha) (hs hb), add_mul, Finset.sum_mul]
      refine P.add_mem ?_ (P.sum_mem fun j hj => ?_)
      · exact P.smul_mem (c i) rest
      · rw [smul_mul_assoc, mulMon]
        exact P.smul_mem _ (hins j hj)
  let Q := Submodule.span F (Set.range (fun s : ↥(f.powerset) => mon v s.val))
  have sub : Q ≤ P := Submodule.span_le.mpr (by
    rintro _ ⟨s,rfl⟩
    exact pos _ _ rfl (mem_powerset.mp s.property))
  have one : (1 : X → F) ∈ Q := by
    apply Submodule.subset_span
    exact ⟨⟨∅,mem_powerset.mpr (empty_subset _)⟩, by simp [mon]⟩
  have times (j) (hj : j ∈ f) (z : X → F) (hz : z ∈ Q) : v j*z ∈ Q := by
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨s,rfl⟩ := h
      rw [mulMon]
      exact Submodule.subset_span ⟨⟨_,mem_powerset.mpr (insert_subset hj (mem_powerset.mp s.property))⟩,rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa [mul_add] using Q.add_mem hx hy
    | smul r x _ hx => simpa [mul_smul_comm] using Q.smul_mem r hx
  have masks (x : X) (s : Finset (I k)) (hs : s ⊆ f) :
      (fun y => if ∀ j ∈ s, v j x = v j y then (1:F) else 0) ∈ Q := by
    induction s using Finset.induction_on with
    | empty => simpa using (show (fun _ : X => (1:F)) ∈ Q from one)
    | @insert j s hj ih =>
      let z : X → F := fun y => if ∀ l ∈ s, v l x = v l y then 1 else 0
      have hz : z ∈ Q := ih (subset_insert _ _ |>.trans hs)
      have ht := times j (hs (mem_insert_self _ _)) z hz
      rcases casesF (v j x) with hx|hx
      · convert Q.sub_mem hz ht using 1
        funext y
        rcases casesF (v j y) with hy|hy <;> simp [z,hx,hy]
      · convert ht using 1
        funext y
        rcases casesF (v j y) with hy|hy <;> simp [z,hx,hy]
  have allQ (w : X → F) : w ∈ Q := by
    have h (x : X) : (fun y => if x = y then (1:F) else 0) ∈ Q := by
      convert masks x f (Subset.rfl) using 1
      funext y
      simp only [show (∀ j ∈ f, v j x = v j y) ↔ x=y from ⟨sep x y,by rintro rfl; simp⟩]
    convert Q.sum_mem (t := univ) (fun x _ => Q.smul_mem (w x) (h x)) using 1
    funext y
    simp [Finset.sum_apply, mul_ite]
  have top : P = ⊤ := top_unique fun w _ => sub (allQ w)
  have dim := finrank_range_le_card (R := F) (fun s : ↥(good f a b) => mon v s.val)
  change Module.finrank F P ≤ _ at dim
  rw [top, finrank_top, Module.finrank_pi] at dim
  simpa using dim

variable {k : ℕ}

structure Chart (k : ℕ) where
  f : Finset (I k)
  u : W k
  l : I k → W k
  w : W k
  hu : ∀ j ∈ f, u j = 0
  hl : ∀ i ∈ f, ∀ j ∈ f, l i j = if i=j then 1 else 0

def val (C : Chart k) (z : W k) := C.u + ∑ j ∈ C.f, z j • C.l j
def box (C : Chart k) (x : W k) := ∀ i ∉ C.f, x i = C.w i
def face (C : Chart k) (x : W k) := x = val C x

theorem freeVal (C : Chart k) (z : W k) {j} (h : j ∈ C.f) : val C z j = z j := by
  classical
  simp [val, Finset.sum_apply, C.hu j h]
  rw [Finset.sum_eq_single_of_mem j h (fun i hi hij => by simp [C.hl i hi j h, hij])]
  simp [C.hl j h j h]

theorem sameVal (C : Chart k) {z z' : W k} (h : ∀ j ∈ C.f, z j = z' j) : val C z = val C z' := by
  unfold val
  congr 1
  exact sum_congr rfl fun j hj => by rw [h j hj]

def init (k : ℕ) : Chart k where
  f := univ
  u := 0
  w := 0
  l := fun i j => if i=j then 1 else 0
  hu := by simp
  hl := by simp

def bit (b : Bool) : F := if b then 1 else 0
theorem bit_test (v : F) (b : Bool) : decide (v ≠ 0) = b ↔ v = bit b := by
  rcases casesF v with rfl|rfl <;> cases b <;> decide

def shrink (C : Chart k) (q : W k →ₗ[F] F) (t r : F) (i : I k) (hi : i ∈ C.f) : Chart k where
  f := C.f.erase i
  u := C.u + (r - t - q C.u) • C.l i
  l := fun j => C.l j - q (C.l j) • C.l i
  w := Function.update C.w i r
  hu := by
    intro j hj
    obtain ⟨hne,hj⟩ := mem_erase.mp hj
    simp [C.hu j hj, C.hl i hi j hj, Ne.symm hne]
  hl := by
    intro n hn j hj
    obtain ⟨hne,hj⟩ := mem_erase.mp hj
    simp [C.hl n (mem_of_mem_erase hn) j hj, C.hl i hi j hj, Ne.symm hne]

def restV (C : Chart k) (i : I k) (z : W k) := C.u + ∑ j ∈ C.f.erase i, z j • C.l j

theorem decomp (C : Chart k) {i : I k} (hi : i ∈ C.f) (z : W k) :
    val C z = restV C i z + z i • C.l i := by
  unfold val restV
  rw [add_assoc, Finset.sum_erase_add _ _ hi]

theorem shrinkVal (C : Chart k) (q : W k →ₗ[F] F) (t r : F) (i : I k) (hi : i ∈ C.f) (z : W k) :
    val (shrink C q t r i hi) z = restV C i z + (r - t - q (restV C i z)) • C.l i := by
  simp only [val,shrink,restV,smul_sub,Finset.sum_sub_distrib, smul_smul, map_add,map_sum,map_smul,
    smul_eq_mul, sub_smul,add_smul,Finset.sum_smul]
  abel

theorem childFace (C : Chart k) (q : W k →ₗ[F] F) (t r : F) (i : I k) (hi : i ∈ C.f)
    (hp : q (C.l i) = 1) (x : W k) :
    face (shrink C q t r i hi) x ↔ face C x ∧ q x + t = r := by
  let B := restV C i x
  let s := r-t-q B
  have e : val (shrink C q t r i hi) x = B + s • C.l i := shrinkVal _ _ _ _ _ _ _
  have old : val C x = B + x i • C.l i := decomp C hi x
  have bi : B i = 0 := by
    dsimp [B,restV]
    simp [Finset.sum_apply, C.hu i hi]
    exact Finset.sum_eq_zero fun j hj => by simp [C.hl j (mem_of_mem_erase hj) i hi, (mem_erase.mp hj).1]
  unfold face
  rw [e,old]
  constructor
  · intro eq
    have xi := congrFun eq i
    simp [bi,C.hl i hi i hi] at xi
    refine ⟨by rwa [xi], ?_⟩
    conv_lhs => rw [eq]
    simp [s, hp]
  · rintro ⟨eq,h⟩
    have eq' : q x = q B + x i := by
      conv_lhs => rw [eq]
      simp [hp]
    rw [eq'] at h
    have xi : x i = s := by dsimp [s]; linear_combination h
    rwa [← xi]

theorem childBox (C : Chart k) (q : W k →ₗ[F] F) (t r : F) (i : I k) (hi : i ∈ C.f)
    (x : W k) : box (shrink C q t r i hi) x ↔ box C x ∧ x i = r := by
  unfold box shrink
  simp only
  constructor
  · intro h
    refine ⟨fun j hj => ?_, by simpa using h i (notMem_erase _ _)⟩
    have hji : j ≠ i := by rintro rfl; contradiction
    simpa [hji] using h j (fun hj' => hj (mem_of_mem_erase hj'))
  · rintro ⟨h,hi'⟩ j hj
    by_cases e : j=i
    · simpa [e] using hi'
    · simpa [e] using h j (fun hj' => hj (mem_erase.mpr ⟨e,hj'⟩))

theorem forced (C : Chart k) (q : W k →ₗ[F] F) (h : ¬ ∃ i ∈ C.f, q (C.l i) = 1)
    (x : W k) (hx : face C x) : q x = q C.u := by
  have zero (j) (hj : j ∈ C.f) : q (C.l j) = 0 :=
    (casesF _).resolve_right (fun e => h ⟨j,hj,e⟩)
  calc
    q x = q (val C x) := congrArg q hx
    _ = _ := by
      simp [val,map_sum]
      exact Finset.sum_eq_zero fun j hj => by simp [zero j hj]

abbrev Qry (k : ℕ) := W k →ₗ[F] F
abbrev St (k : ℕ) := Option (Chart k)
abbrev Path := List Bool

noncomputable def pickS (S : St k) (q : Qry k) : Option (I k) :=
  match S with
  | none => none
  | some C => if h : ∃ i ∈ C.f, q (C.l i) = 1 then some h.choose else none

def fixedS (S : St k) (q : Qry k) (t : F) : Bool :=
  match S with
  | none => false
  | some C => decide (q C.u + t ≠ 0)

noncomputable def nextS (S : St k) (q : Qry k) (t : F) (b : Bool) : St k :=
  match S with
  | none => none
  | some C =>
    if h : ∃ i ∈ C.f, q (C.l i) = 1 then some (shrink C q t (bit b) h.choose h.choose_spec.1)
    else if decide (q C.u + t ≠ 0) = b then some C else none

def actual (S : St k) (x : W k) : Prop := S.elim False (fun C => face C x)
def cube (S : St k) (x : W k) : Prop := S.elim False (fun C => box C x)

theorem actualNext (S : St k) (q : Qry k) (t : F) (b : Bool) (x : W k) :
    actual (nextS S q t b) x ↔ actual S x ∧ decide (q x + t ≠ 0) = b := by
  cases S with
  | none => simp [actual,nextS]
  | some C =>
    by_cases h : ∃ i ∈ C.f, q (C.l i) = 1
    · simp only [nextS,dite_eq_left h,actual,Option.elim_some, childFace C q t (bit b) h.choose h.choose_spec.1 h.choose_spec.2, bit_test]
    · by_cases e : decide (q C.u + t ≠ 0) = b
      · simp only [nextS,dite_eq_right h,ite_eq_left e,actual,Option.elim_some]
        refine ⟨?_,And.left⟩
        intro hx
        refine ⟨hx,?_⟩
        rwa [forced C q h x hx]
      · simp only [nextS,dite_eq_right h,ite_eq_right e,actual,Option.elim_some,Option.elim_none,false_iff,not_and]
        intro hx
        rwa [forced C q h x hx]

theorem cubeNext (S : St k) (q : Qry k) (t : F) (b : Bool) (x : W k) :
    cube (nextS S q t b) x ↔ cube S x ∧
      (pickS S q).elim (fixedS S q t) (fun i => decide (x i ≠ 0)) = b := by
  cases S with
  | none => simp [cube,nextS]
  | some C =>
    by_cases h : ∃ i ∈ C.f, q (C.l i) = 1
    · simp only [cube,nextS,pickS,dite_eq_left h,Option.elim_some,childBox,bit_test]
    · by_cases e : decide (q C.u + t ≠ 0) = b <;> simp only [cube,nextS,pickS,fixedS,dite_eq_right h,Option.elim_none, Option.elim_some, ite_true, ite_false, e, and_true,and_false]

noncomputable def state (q : Path → Qry k) (t : Path → F) (p : Path) : St k :=
  List.reverseRecOn (motive := fun _ => St k) p (some (init k))
    (fun l b s => nextS s (q l) (t l) b)

def reaches (ask : Path → W k → Bool) (p : Path) (x : W k) :=
  ∀ (j : ℕ) (hj : j < p.length), ask (p.take j) x = p[j]

theorem reachesSnoc (ask : Path → W k → Bool) (p : Path) (b : Bool) (x : W k) :
    reaches ask (p ++ [b]) x ↔ reaches ask p x ∧ ask p x = b := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have g := h j (by simp; omega)
      rw [List.take_append_of_le_length (Nat.le_of_lt hj), List.getElem_append_left hj] at g
      exact g
    · simpa using h p.length (by simp)
  · rintro ⟨h,e⟩ j hj
    by_cases s : j < p.length
    · simpa [List.take_append_of_le_length (Nat.le_of_lt s), List.getElem_append_left s] using h j s
    · have : j = p.length := by simp at hj; omega
      subst j
      simpa using e

def live (ask : Path → W k → Bool) (p : Path) :=
  (univ : Finset (W k)).filter fun x =>
    (List.finRange p.length).all (fun j => ask (p.take j.val) x == p.get j) = true

theorem memLive (ask : Path → W k → Bool) (p : Path) (x : W k) :
    x ∈ live ask p ↔ reaches ask p x := by
  simp only [live,mem_filter,mem_univ,true_and,List.all_eq_true,List.mem_finRange,forall_const,
    beq_iff_eq,List.get_eq_getElem]
  constructor
  · exact fun h j hj => h ⟨j,hj⟩
  · exact fun h j => h j.val j.isLt

def askT (q : Path → Qry k) (t : Path → F) (p : Path) (x : W k) := decide (q p x + t p ≠ 0)
noncomputable def coordT (q : Path → Qry k) (t : Path → F) (p : Path) (x : W k) :=
  (pickS (state q t p) (q p)).elim (fixedS (state q t p) (q p) (t p)) (fun i => decide (x i ≠ 0))

theorem paths (q : Path → Qry k) (t : Path → F) (p : Path) (x : W k) :
    (reaches (askT q t) p x ↔ actual (state q t p) x) ∧
    (reaches (coordT q t) p x ↔ cube (state q t p) x) := by
  induction p using List.reverseRecOn with
  | nil =>
    have h : val (init k) x = x := funext fun j => freeVal _ _ (mem_univ j)
    simp [reaches,state,actual,cube,face,box,init]
    exact h.symm
  | append_singleton p b ih =>
    simp only [reachesSnoc,state,List.reverseRecOn_concat,actualNext,cubeNext] at *
    exact ⟨and_congr ih.1 Iff.rfl,and_congr ih.2 Iff.rfl⟩

def fill (C : Chart k) (z : W k) : W k := fun i => if i ∈ C.f then z i else C.w i

theorem pathCard (q : Path → Qry k) (t : Path → F) (p : Path) :
    (live (askT q t) p).card = (live (coordT q t) p).card := by
  have ha (x : W k) := (memLive (askT q t) p x).trans (paths q t p x).1
  have hc (x : W k) := (memLive (coordT q t) p x).trans (paths q t p x).2
  cases e : state q t p with
  | none =>
    simp [e,actual,cube] at ha hc
    rw [eq_empty_of_forall_notMem ha, eq_empty_of_forall_notMem hc]
  | some C =>
    simp only [e,actual,cube,Option.elim_some] at ha hc
    apply card_bij' (fun x _ => fill C x) (fun y _ => val C y)
    · exact fun x _ => (hc _).mpr (fun i hi => by simp [fill,hi])
    · exact fun x _ => (ha _).mpr (sameVal C fun j hj => (freeVal C x hj).symm)
    · intro x hx
      exact (sameVal C fun j hj => by simp [fill,hj]).trans ((ha x).mp hx).symm
    · intro y hy
      funext j
      by_cases hj : j ∈ C.f
      · simp [fill,hj,freeVal C y hj]
      · simp [fill,hj,((hc y).mp hy j hj)]

variable {m : ℕ}

def prodT (a b : Fin m → I k) (x : W k) : W m := fun i => x (a i)*x (b i)
def linD (C : Chart k) (a b : Fin m → I k) : W k →ₗ[F] W m :=
  LinearMap.pi fun i =>
    if a i = b i then LinearMap.proj (a i)
    else if a i ∉ C.f then C.w (a i) • LinearMap.proj (b i)
    else if b i ∉ C.f then C.w (b i) • LinearMap.proj (a i)
    else 0

def code (C : Chart k) (s : Finset (I k)) := fill C (fun i => if i ∈ s then 1 else 0)
theorem codeBox (C : Chart k) (s : Finset (I k)) : box C (code C s) :=
  fun i hi => by simp [code,fill,hi]

theorem codeFit (C : Chart k) (a b : Fin m → I k) (s : Finset (I k)) (hs : s ∈ good C.f a b) :
    prodT a b (code C s) = linD C a b (code C s) := by
  have hg := (mem_filter.mp hs).2
  funext i
  change code C s (a i) * code C s (b i) = _
  by_cases eq : a i = b i
  · simp [linD,eq,sqF]
  by_cases ha : a i ∈ C.f
  · by_cases hb : b i ∈ C.f
    · have hh := hg i eq
      by_cases h : a i ∈ s
      · have h' : b i ∉ s := fun u => hh ⟨h,u⟩
        simp [linD,code,fill,eq,ha,hb,h']
      · simp [linD,code,fill,eq,ha,hb,h]
    · simp [linD,eq,ha,hb,code,fill,mul_comm]
  · simp [linD,eq,ha,code,fill]

theorem codeInj (C : Chart k) (a b : Fin m → I k) :
    Set.InjOn (code C) (↑(good C.f a b) : Set _) := by
  intro s hs t ht he
  have hs' := mem_powerset.mp (mem_filter.mp hs).1
  have ht' := mem_powerset.mp (mem_filter.mp ht).1
  ext i
  by_cases h : i ∈ C.f
  · have hh := congrFun he i
    by_cases e : i ∈ s <;> by_cases e' : i ∈ t <;> simp_all [code,fill]
  · exact ⟨fun hi => False.elim (h (hs' hi)),fun hi => False.elim (h (ht' hi))⟩

theorem bound (C : Chart k) (q : Path → Qry k) (t : Path → F) (p : Path) (hC : state q t p = some C)
    (a b : Fin m → I k) (A : W k →ₗ[F] W m) (c : W m) :
    ((live (askT q t) p).filter fun x => prodT a b x = A x + c).card ≤
    ((live (coordT q t) p).filter fun x => prodT a b x = linD C a b x + 0).card := by
  classical
  let S := (live (askT q t) p).filter fun x => prodT a b x = A x + c
  let v : I k → ↥S → F := fun j x => x.val j
  have fx (x : ↥S) : face C x.val := by
    have h := ((memLive _ _ _).trans (paths q t p x.val).1).mp (mem_filter.mp x.property).1
    simpa [hC,actual] using h
  have sep (x y : ↥S) (h : ∀ j ∈ C.f, v j x = v j y) : x=y := by
    apply Subtype.ext
    exact (fx x).trans ((sameVal C h).trans (fx y).symm)
  have eqn (i : Fin m) (_ : a i ∈ C.f) (_ : b i ∈ C.f) :
      v (a i)*v (b i) = Function.const (↥S) ((A C.u) i + c i) +
        ∑ j ∈ C.f, (A (C.l j)) i • v j := by
    funext x
    have e := congrFun (mem_filter.mp x.property).2 i
    change x.val (a i)*x.val (b i) = (A x.val) i + c i at e
    change x.val (a i)*x.val (b i) = _
    rw [e]
    have ev : A x.val = A (val C x.val) := congrArg A (fx x)
    rw [ev]
    simp [val,map_sum, Finset.sum_apply, v, Function.const, mul_comm,add_assoc,add_comm]
  have ub := footprint C.f a b v sep _ _ eqn
  change S.card ≤ _
  apply le_trans (by simpa using ub : S.card ≤ (good C.f a b).card)
  apply card_le_card_of_injOn (code C) _ (codeInj C a b)
  intro s hs
  apply mem_filter.mpr
  refine ⟨(memLive _ _ _).mpr ((paths q t p _).2.mpr ?_), by simpa using codeFit C a b s hs⟩
  simpa [hC,cube] using codeBox C s
end PEqualNP.Outside.L_lib_900_aux
open PEqualNP.Outside.L_lib_900_aux
theorem PEqualNP.Outside.L_lib_900 : (∀ (k : Nat),
  let F := ZMod 2
  let W := Fin k → F
  let passes := fun (ask : List Bool → W → Bool) (p : List Bool) (x : W) =>
    (List.finRange p.length).all (fun j => ask (p.take j.val) x == p.get j)
  let reach := fun (ask : List Bool → W → Bool) (p : List Bool) =>
    (Finset.univ : Finset W).filter (fun x => passes ask p x = true)
  ∀ (q : List Bool → W →ₗ[F] F) (t : List Bool → F),
    let ask := fun (p : List Bool) (x : W) => decide (q p x + t p ≠ 0)
    ∃ (pick : List Bool → Option (Fin k)) (fixed : List Bool → Bool),
      let coord := fun (p : List Bool) (x : W) =>
        (pick p).elim (fixed p) (fun i => decide (x i ≠ 0))
      (∀ p, (reach ask p).card = (reach coord p).card) ∧
      ∀ (m : Nat) (a b : Fin m → Fin k),
        let Z := Fin m → F
        let prod := fun (x : W) (i : Fin m) => x (a i) * x (b i)
        let hits := fun (test : List Bool → W → Bool) (A : List Bool → W →ₗ[F] Z)
            (c : List Bool → Z) (p : List Bool) =>
          ((reach test p).filter (fun x => prod x = A p x + c p)).card
        ∀ (A : List Bool → W →ₗ[F] Z) (c : List Bool → Z),
          ∃ (D : List Bool → W →ₗ[F] Z) (e : List Bool → Z),
            ∀ p, hits ask A c p ≤ hits coord D e p) := by
  intro k
  dsimp only
  intro q t
  refine ⟨fun p => pickS (state q t p) (q p), fun p => fixedS (state q t p) (q p) (t p),
    pathCard q t, ?_⟩
  intro m a b A c
  refine ⟨fun p => (state q t p).elim 0 (fun C => linD C a b), fun _ => 0, ?_⟩
  intro p
  change ((live (askT q t) p).filter fun x => prodT a b x = A p x + c p).card ≤
    ((live (coordT q t) p).filter fun x => prodT a b x =
      ((state q t p).elim 0 (fun C => linD C a b)) x + 0).card
  cases e : state q t p with
  | some C => exact bound C q t p e a b (A p) (c p)
  | none =>
    have h (x : W k) : x ∉ live (askT q t) p := by
      simp [memLive,(paths q t p x).1,e,actual]
    simp [Finset.eq_empty_of_forall_notMem h]
