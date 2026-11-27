import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_875

open scoped Classical

variable {X : Type*} [DecidableEq X]
variable (f : X → X) (S : Finset X)

def edge (x y : X) := x ∈ S ∧ y ∈ S ∧ (f x = y ∨ f y = x)

noncomputable def cc (x : X) := S.filter (Relation.ReflTransGen (edge f S) x)
noncomputable def pcs := S.image (cc f S)
def halo (C : Finset X) := C ∪ C.image f

omit [DecidableEq X] in
theorem selfMem {x : X} (hx : x ∈ S) : x ∈ cc f S x :=
  Finset.mem_filter.mpr ⟨hx,.refl⟩

omit [DecidableEq X] in
theorem same {x y : X} (h : Relation.ReflTransGen (edge f S) x y) :
    cc f S x = cc f S y := by
  let : Std.Symm (edge f S) := ⟨fun a b e => ⟨e.2.1,e.1,e.2.2.symm⟩⟩
  have back := Std.Symm.symm (r := Relation.ReflTransGen (edge f S)) _ _ h
  ext z
  simp only [cc, Finset.mem_filter]
  exact and_congr_right fun _ => ⟨fun p => back.trans p,fun p => h.trans p⟩

theorem center {C : Finset X} (hC : C ∈ pcs f S) {x : X} (hx : x ∈ C) :
    x ∈ S ∧ cc f S x = C := by
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨hx,p⟩ := Finset.mem_filter.mp hx
  exact ⟨hx,(same f S p).symm⟩

theorem populated {C : Finset X} (hC : C ∈ pcs f S) : C.Nonempty := by
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hC
  exact ⟨w,selfMem f S hw⟩

theorem joined {C D : Finset X} (hc : C ∈ pcs f S) (hd : D ∈ pcs f S)
    {x y : X} (hx : x ∈ C) (hy : y ∈ D) (h : x = y ∨ f x = y ∨ f y = x) : C = D := by
  obtain ⟨xs,xc⟩ := center f S hc hx
  obtain ⟨ys,yc⟩ := center f S hd hy
  rw [← xc, ← yc]
  rcases h with rfl | h
  · rfl
  exact same f S (.single ⟨xs,ys,h⟩)

theorem separate (inj : Function.Injective f) :
    (↑(pcs f S) : Set (Finset X)).PairwiseDisjoint (halo f) := by
  intro C hc D hd ne
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  simp only [halo,Finset.mem_union,Finset.mem_image] at hz hz'
  rcases hz with h | ⟨x,h,rfl⟩ <;> rcases hz' with h' | ⟨y,h',eq⟩
  · exact ne (joined f S hc hd h h' (Or.inl rfl))
  · exact ne (joined f S hc hd h h' (Or.inr (Or.inr eq)))
  · exact ne (joined f S hc hd h h' (Or.inr (Or.inl rfl)))
  · exact ne (joined f S hc hd h h' (Or.inl (inj eq).symm))

theorem soloOrEdge {C : Finset X} (hc : C ∈ pcs f S) :
    (∃ x, C = {x}) ∨ ∃ x ∈ C, f x ∈ C := by
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hc
  by_cases eq : cc f S w = {w}
  · exact Or.inl ⟨w,eq⟩
  right
  have ex : ∃ z ∈ cc f S w, z ≠ w := by
    by_contra! h
    exact eq (Finset.Subset.antisymm (fun z hz => Finset.mem_singleton.mpr (h z hz))
      (Finset.singleton_subset_iff.mpr (selfMem f S hw)))
  obtain ⟨z,hz,ne⟩ := ex
  rcases (Finset.mem_filter.mp hz).2.cases_tail with eq | ⟨a,ha,e⟩
  · exact (ne eq).elim
  have ac : a ∈ cc f S w := Finset.mem_filter.mpr ⟨e.1,ha⟩
  rcases e.2.2 with p | p
  · exact ⟨a,ac,p ▸ hz⟩
  · exact ⟨z,hz,p ▸ ac⟩

variable {t : ℕ} (ht : 0 < t)

def nxt (i : Fin (3*t)) : Fin (3*t) := ⟨(i.val+1) % (3*t),Nat.mod_lt _ (by omega)⟩

theorem nval (i : Fin (3*t)) : (nxt ht i).val = if i.val+1 < 3*t then i.val+1 else 0 := by
  unfold nxt
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have e : i.val+1 = 3*t := by omega
    simp [e]

theorem ninj : Function.Injective (nxt ht) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [nval] at this
  apply Fin.ext
  split_ifs at this <;> omega

theorem nmod (i : Fin (3*t)) : (nxt ht i).val % 3 = (i.val+1) % 3 := by
  rw [nval]; split_ifs <;> omega

theorem boundary {C : Finset (Fin (3*t))} (ne : C.Nonempty) (pr : C ≠ Finset.univ) :
    ∃ x ∈ C, nxt ht x ∉ C := by
  by_contra! h
  apply pr
  obtain ⟨w,hw⟩ := ne
  have go (k : ℕ) : ∃ x ∈ C, x.val = (w.val+k) % (3*t) := by
    induction k with
    | zero => exact ⟨w,hw,by simp [Nat.mod_eq_of_lt w.isLt]⟩
    | succ k ih =>
      obtain ⟨x,hx,ex⟩ := ih
      refine ⟨_,h x hx,?_⟩
      change (x.val+1) % (3*t) = _
      rw [ex,Nat.mod_add_mod]
      rfl
  apply Finset.eq_univ_of_forall
  intro y
  obtain ⟨x,hx,ex⟩ := go (3*t-w.val+y.val)
  rw [show w.val+(3*t-w.val+y.val) = y.val+3*t by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt y.isLt] at ex
  exact Fin.ext ex ▸ hx

abbrev Vec (m : ℕ) := Fin m → ZMod 2

def col {m : ℕ} (u v : Vec m) (r : ℕ) := if r % 3=0 then u else if r % 3=1 then v else u+v

def column {m : ℕ} (u v : Vec m) (i : Fin (3*t)) := col u v i.val

noncomputable def space {m : ℕ} (u v : Vec m) (S : Finset (Fin (3*t))) :=
  Submodule.span (ZMod 2) (↑((pcs (nxt ht) S).image (fun C => ∑ i ∈ C, column u v i)) : Set (Vec m))

theorem componentSum {m : ℕ} (u v : Vec m) {S : Finset (Fin (3*t))} {C}
    (hc : C ∈ pcs (nxt ht) S) : (∑ i ∈ C, column u v i) ∈ space ht u v S :=
  Submodule.subset_span (Finset.mem_image.mpr ⟨C,hc,rfl⟩)

theorem cancelPair {m : ℕ} {a b : Vec m} (h : a+b = 0) : a = b :=
  funext fun i => CharTwo.add_eq_zero.mp (congrFun h i)

theorem colors {m : ℕ} {u v : Vec m} (hi : LinearIndependent (ZMod 2) ![u,v]) :
    u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ u+v ≠ 0 ∧ u ≠ u+v ∧ v ≠ u+v := by
  have hu : u ≠ 0 := hi.ne_zero 0
  have hv : v ≠ 0 := hi.ne_zero 1
  have huv : u ≠ v := fun h => (by decide : (0 : Fin 2) ≠ 1) (hi.injective (show ![u,v] 0 = ![u,v] 1 from h))
  exact ⟨hu,hv,huv,fun h => huv (cancelPair h),by simpa using hv,by simpa using hu⟩

theorem upperZero {m : ℕ} {u v : Vec m} (hi : LinearIndependent (ZMod 2) ![u,v])
    {S : Finset (Fin (3*t))} (pr : S ≠ Finset.univ) (rk : Module.finrank (ZMod 2) (space ht u v S) = 0) :
    (pcs (nxt ht) S).card ≤ 3*t/4 := by
  obtain ⟨hu,hv,huv,hs,h1,h2⟩ := colors hi
  have four (C) (hc : C ∈ pcs (nxt ht) S) : 4 ≤ (halo (nxt ht) C).card := by
    have z : (∑ i ∈ C, column u v i) = 0 := congrArg Subtype.val
      ((finrank_zero_iff_forall_zero.mp rk) ⟨_,componentSum ht u v hc⟩)
    have three : 3 ≤ C.card := by
      rcases soloOrEdge (nxt ht) S hc with ⟨x,rfl⟩ | ⟨x,hx,hy⟩
      · simp only [Finset.sum_singleton, column,col] at z
        split_ifs at z <;> contradiction
      · by_contra! small
        have nm := nmod ht x
        have ne : x ≠ nxt ht x := by
          intro eq
          rw [← eq] at nm
          omega
        have sub : {x,nxt ht x} ⊆ C := Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
        have eq := Finset.eq_of_subset_of_card_le sub (by simp [ne]; omega)
        rw [← eq,Finset.sum_pair ne] at z
        have e := cancelPair z
        simp only [column,col] at e
        split_ifs at e <;> first | contradiction | exact huv e.symm | exact h1 e.symm | exact h2 e.symm | omega
    have cpr : C ≠ Finset.univ := by
      intro eq
      apply pr
      apply Finset.eq_univ_of_forall
      intro x
      exact (center _ _ hc (show x ∈ C by simp [eq])).1
    obtain ⟨x,hx,hy⟩ := boundary ht (populated _ _ hc) cpr
    have sub : insert (nxt ht x) C ⊆ halo (nxt ht) C := by
      apply Finset.insert_subset
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)
      · exact Finset.subset_union_left
    have := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem hy] at this
    omega
  have total := Finset.sum_le_sum four
  rw [← Finset.card_biUnion (separate (nxt ht) S (ninj ht))] at total
  have lim := Finset.card_le_univ ((pcs (nxt ht) S).biUnion (halo (nxt ht)))
  simp at total lim
  omega

theorem upperOne {m : ℕ} {u v : Vec m} (hi : LinearIndependent (ZMod 2) ![u,v])
    {S : Finset (Fin (3*t))} (rk : Module.finrank (ZMod 2) (space ht u v S) = 1) :
    (pcs (nxt ht) S).card ≤ t := by
  let W := space ht u v S
  have miss : u ∉ W ∨ v ∉ W := by
    by_contra! h
    have sub : Submodule.span (ZMod 2) (Set.range ![u,v]) ≤ W := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      fin_cases i <;> simp [h.1,h.2]
    have d := Submodule.finrank_mono sub
    rw [finrank_span_eq_card hi] at d
    change 2 ≤ Module.finrank (ZMod 2) (space ht u v S) at d
    omega
  obtain ⟨r,hr,hm⟩ : ∃ r : ℕ, r < 3 ∧ col u v r ∉ W := by
    rcases miss with h | h
    · exact ⟨0,by decide,by simpa [col] using h⟩
    · exact ⟨1,by decide,by simpa [col] using h⟩
  let P := pcs (nxt ht) S
  have hit (C : ↥P) : ∃ z ∈ halo (nxt ht) C.val, z.val % 3 = (r+2) % 3 := by
    rcases soloOrEdge (nxt ht) S C.property with ⟨x,hx⟩ | ⟨x,hx,hy⟩
    · have hsum := componentSum ht u v C.property
      rw [hx,Finset.sum_singleton] at hsum
      have neq : x.val % 3 ≠ r := by
        intro e
        apply hm
        simpa [column,col,e,Nat.mod_eq_of_lt hr,W] using hsum
      have xc : x ∈ C.val := by simp [hx]
      by_cases ex : x.val % 3 = (r+2) % 3
      · exact ⟨x,Finset.mem_union_left _ xc,ex⟩
      · exact ⟨_,Finset.mem_union_right _ (Finset.mem_image_of_mem _ xc),by rw [nmod]; omega⟩
    · have n1 := nmod ht x
      have n2 := nmod ht (nxt ht x)
      by_cases e : x.val % 3 = (r+2) % 3
      · exact ⟨x,Finset.mem_union_left _ hx,e⟩
      by_cases e' : (nxt ht x).val % 3 = (r+2) % 3
      · exact ⟨_,Finset.mem_union_left _ hy,e'⟩
      exact ⟨_,Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy),by omega⟩
  choose z hz he using hit
  let slot (C : ↥P) : Fin t := ⟨(z C).val/3,by have := (z C).isLt; omega⟩
  have inj : Function.Injective slot := by
    intro C D eq
    have q : (z C).val/3 = (z D).val/3 := congrArg Fin.val eq
    have sameZ : z C = z D := Fin.ext (by have := he C; have := he D; omega)
    by_contra ne
    have dis := separate (nxt ht) S (ninj ht) C.property D.property (fun e => ne (Subtype.ext e))
    exact Finset.disjoint_left.mp dis (hz C) (sameZ.symm ▸ hz D)
  simpa [P] using Fintype.card_le_of_injective slot inj

def supp (t p w : ℕ) : Finset (Fin (3*t)) :=
  Finset.univ.filter fun i => i.val / p < 3*t/p ∧ i.val % p < w

def block (t p w : ℕ) (j : Fin (3*t/p)) : Finset (Fin (3*t)) :=
  Finset.univ.filter fun i => i.val / p = j.val ∧ i.val % p < w

theorem insupp {p w : ℕ} {i : Fin (3*t)} : i ∈ supp t p w ↔ i.val/p < 3*t/p ∧ i.val % p < w := by
  simp [supp]

theorem inblock {p w : ℕ} {j : Fin (3*t/p)} {i : Fin (3*t)} :
    i ∈ block t p w j ↔ i.val/p = j.val ∧ i.val % p < w := by simp [block]

def site {p : ℕ} (hp : p=3 ∨ p=4) (j : Fin (3*t/p)) (a : ℕ) (ha : a<p) : Fin (3*t) :=
  ⟨j.val*p+a,by have := j.isLt; rcases hp with rfl|rfl <;> omega⟩

theorem blockComp {p w : ℕ} (hp : p=3 ∨ p=4) (hw : 0<w) (hw' : w<p) (j : Fin (3*t/p)) :
    cc (nxt ht) (supp t p w) (site hp j 0 (by omega)) = block t p w j := by
  let b := site hp j 0 (by omega : 0<p)
  have bs : b ∈ supp t p w := by
    rw [insupp]; dsimp [b,site]; have := j.isLt; rcases hp with rfl|rfl <;> omega
  have key {x y : Fin (3*t)} (xs : x ∈ supp t p w) (ys : y ∈ supp t p w)
      (h : nxt ht x = y) : x.val/p = y.val/p := by
    have e := congrArg Fin.val h
    rw [nval] at e
    obtain ⟨xa,xb⟩ := insupp.mp xs
    obtain ⟨ya,yb⟩ := insupp.mp ys
    split_ifs at e <;> rcases hp with rfl|rfl <;> omega
  ext x
  constructor
  · intro xc
    obtain ⟨xs,path⟩ := Finset.mem_filter.mp xc
    apply inblock.mpr
    refine ⟨?_,(insupp.mp xs).2⟩
    clear xs xc
    induction path with
    | refl => dsimp [site]; rcases hp with rfl|rfl <;> omega
    | tail path e ih =>
      rcases e.2.2 with fwd|rev
      · exact (key e.1 e.2.1 fwd).symm.trans ih
      · exact (key e.2.1 e.1 rev).trans ih
  · intro xb
    obtain ⟨xq,xr⟩ := inblock.mp xb
    have path (a : ℕ) (ha : a<w) :
        site hp j a (by omega) ∈ cc (nxt ht) (supp t p w) b := by
      induction a with
      | zero => exact selfMem _ _ bs
      | succ a ih =>
        obtain ⟨ps,pre⟩ := Finset.mem_filter.mp (ih (by omega))
        have ss : site hp j (a+1) (by omega) ∈ supp t p w := by
          rw [insupp]; dsimp [site]; have := j.isLt; rcases hp with rfl|rfl <;> omega
        apply Finset.mem_filter.mpr
        refine ⟨ss,pre.tail ⟨ps,ss,Or.inl ?_⟩⟩
        apply Fin.ext
        change (j.val*p+a+1) % (3*t) = j.val*p+(a+1)
        rw [Nat.mod_eq_of_lt (by have := j.isLt; rcases hp with rfl|rfl <;> omega)]
        omega
    have ex : site hp j (x.val % p) (by omega) = x := by
      apply Fin.ext
      dsimp [site]; rcases hp with rfl|rfl <;> omega
    exact ex ▸ path _ xr

theorem blocks {p w : ℕ} (hp : p=3 ∨ p=4) (hw : 0<w) (hw' : w<p) :
    pcs (nxt ht) (supp t p w) = Finset.univ.image (block t p w) := by
  ext C
  constructor
  · rintro hc
    obtain ⟨x,xs,rfl⟩ := Finset.mem_image.mp hc
    let j : Fin (3*t/p) := ⟨x.val/p,(insupp.mp xs).1⟩
    have xb : x ∈ block t p w j := inblock.mpr ⟨rfl,(insupp.mp xs).2⟩
    rw [← blockComp ht hp hw hw' j] at xb
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,(blockComp ht hp hw hw' j).symm.trans
      (same _ _ (Finset.mem_filter.mp xb).2)⟩
  · intro hc
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
    refine Finset.mem_image.mpr ⟨_,?_,blockComp ht hp hw hw' j⟩
    rw [insupp]; dsimp [site]; have := j.isLt; rcases hp with rfl|rfl <;> omega

theorem blockCount {p w : ℕ} (hp : p=3 ∨ p=4) (hw : 0<w) (hw' : w<p) :
    (pcs (nxt ht) (supp t p w)).card = 3*t/p := by
  rw [blocks ht hp hw hw', Finset.card_image_of_injective,Finset.card_univ,Fintype.card_fin]
  intro j k e
  let x := site hp j 0 (by omega : 0<p)
  have mem : x ∈ block t p w j := by
    rw [inblock]; dsimp [x,site]; rcases hp with rfl|rfl <;> omega
  exact Fin.ext ((inblock.mp mem).1.symm.trans (inblock.mp (e ▸ mem : x ∈ block t p w k)).1)

include ht in
theorem properSupp {p w : ℕ} (hp : p=3 ∨ p=4) (hw : w<p) :
    supp t p w ≠ Finset.univ := by
  intro e
  let x : Fin (3*t) := ⟨3*t-1,by omega⟩
  have hx : x ∈ supp t p w := e.symm ▸ Finset.mem_univ x
  obtain ⟨a,b⟩ := insupp.mp hx
  dsimp [x] at a b
  rcases hp with rfl|rfl <;> omega

theorem singleBlock (j : Fin (3*t/3)) : block t 3 1 j = {site (Or.inl rfl) j 0 (by decide)} := by
  ext x
  rw [inblock,Finset.mem_singleton,Fin.ext_iff]
  dsimp [site]; omega

theorem tripleBlock (j : Fin (3*t/4)) :
    block t 4 3 j = {site (Or.inr rfl) j 0 (by decide),site (Or.inr rfl) j 1 (by decide),
                     site (Or.inr rfl) j 2 (by decide)} := by
  ext x
  simp only [inblock,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,site]
  omega

theorem tripleSum {m : ℕ} (u v : Vec m) (j : Fin (3*t/4)) :
    (∑ i ∈ block t 4 3 j, column u v i) = 0 := by
  rw [tripleBlock]
  rw [Finset.sum_insert (by simp [Fin.ext_iff,site]),Finset.sum_pair (by simp [Fin.ext_iff,site])]
  change col u v (j.val*4) + (col u v (j.val*4+1) + col u v (j.val*4+2)) = 0
  generalize j.val*4 = k
  unfold col
  split_ifs <;> first | omega | (funext i; simp only [Pi.add_apply,Pi.zero_apply]; ring_nf; simp [CharTwo.two_eq_zero])

theorem attainedZero {m : ℕ} (u v : Vec m) :
    Module.finrank (ZMod 2) (space ht u v (supp t 4 3)) = 0 := by
  have eq : space ht u v (supp t 4 3) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨C,hc,rfl⟩ := Finset.mem_image.mp hx
    rw [blocks ht (Or.inr rfl) (by decide) (by decide)] at hc
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
    rw [tripleSum]
    exact Submodule.zero_mem _
  simp [eq]

theorem attainedOne {m : ℕ} {u v : Vec m} (hu : u ≠ 0) :
    Module.finrank (ZMod 2) (space ht u v (supp t 3 1)) = 1 := by
  have single (j : Fin (3*t/3)) : (∑ i ∈ block t 3 1 j, column u v i) = u := by
    rw [singleBlock,Finset.sum_singleton]
    simp [column,col,site]
  have eq : space ht u v (supp t 3 1) = Submodule.span (ZMod 2) {u} := by
    unfold space
    congr 1
    ext x
    simp only [Finset.mem_coe, Finset.mem_image,Set.mem_singleton_iff,
      blocks ht (p:=3) (w:=1) (Or.inl rfl) (by decide) (by decide)]
    constructor
    · rintro ⟨_,⟨j,_,rfl⟩,rfl⟩
      exact single j
    · rintro rfl
      let j : Fin (3*t/3) := ⟨0,by omega⟩
      exact ⟨_,⟨j,Finset.mem_univ _,rfl⟩,single j⟩
  rw [eq,finrank_span_singleton hu]

noncomputable def best {m : ℕ} (u v : Vec m) (k : ℕ) :=
  (Finset.univ.filter fun S => S ≠ Finset.univ ∧ Module.finrank (ZMod 2) (space ht u v S) = k).sup
    (fun S => (pcs (nxt ht) S).card)

theorem sharp {m : ℕ} {u v : Vec m} (hi : LinearIndependent (ZMod 2) ![u,v]) :
    best ht u v 0 = 3*t/4 ∧ best ht u v 1 = t := by
  constructor <;> apply Nat.le_antisymm
  · apply Finset.sup_le
    intro S h
    exact upperZero ht hi (Finset.mem_filter.mp h).2.1 (Finset.mem_filter.mp h).2.2
  · apply Finset.le_sup_of_le (b := supp t 4 3)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,properSupp ht (Or.inr rfl) (by decide),attainedZero ht u v⟩
    · exact (blockCount ht (Or.inr rfl) (by decide : 0<3) (by decide)).ge
  · apply Finset.sup_le
    intro S h
    exact upperOne ht hi (Finset.mem_filter.mp h).2.2
  · apply Finset.le_sup_of_le (b := supp t 3 1)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,properSupp ht (Or.inl rfl) (by decide),attainedOne ht (colors hi).1⟩
    · rw [blockCount ht (Or.inl rfl) (by decide) (by decide)]
      omega

end PEqualNP.Outside.L_lib_875

theorem PEqualNP.Outside.L_lib_875 : (∀ (t m : ℕ) (ht : 0 < t),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  ∀ u v : A, LinearIndependent F ![u,v] →
    let n := 3*t
    let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin n)
    let next := fun i : Fin n => ix (i.val+1)
    let h := fun i : Fin n => if i.val % 3 = 0 then u else if i.val % 3 = 1 then v else u+v
    let parts := fun S : Finset (Fin n) =>
      let step := fun i j : Fin n => i ∈ S ∧ j ∈ S ∧ (next i = j ∨ next j = i)
      S.image (fun w => S.filter (fun z => Relation.ReflTransGen step w z))
    let rankOn := fun S : Finset (Fin n) =>
      Module.finrank F (Submodule.span F
        (↑((parts S).image (fun C => ∑ i ∈ C, h i)) : Set A))
    let most := fun k : ℕ =>
      ((Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => S ≠ Finset.univ ∧ rankOn S = k)).sup (fun S => (parts S).card)
    most 0 = n/4 ∧ most 1 = t) := by
  intro t m ht F A u v hi n ix next h parts rankOn most
  have ec : h = PEqualNP.Outside.L_lib_875.column u v := by
    funext i
    dsimp only [h,PEqualNP.Outside.L_lib_875.column,PEqualNP.Outside.L_lib_875.col]
    split_ifs <;> rfl
  have ep (S) : parts S = PEqualNP.Outside.L_lib_875.pcs (PEqualNP.Outside.L_lib_875.nxt ht) S := by
    dsimp only [parts,PEqualNP.Outside.L_lib_875.pcs,PEqualNP.Outside.L_lib_875.cc,PEqualNP.Outside.L_lib_875.edge]
    congr!
  have er (S) : rankOn S = Module.finrank (ZMod 2) (PEqualNP.Outside.L_lib_875.space ht u v S) := by
    dsimp only [rankOn,PEqualNP.Outside.L_lib_875.space]
    rw [ec,ep]
    apply congrArg (fun s : Finset A => Module.finrank F (Submodule.span F (s : Set A)))
    congr!
  have em (k) : most k = PEqualNP.Outside.L_lib_875.best ht u v k := by
    dsimp only [most,PEqualNP.Outside.L_lib_875.best]
    simp only [er,ep]
    congr!
  rw [em,em]
  exact PEqualNP.Outside.L_lib_875.sharp ht hi
