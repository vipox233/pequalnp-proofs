import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1417_aux

private theorem card_close_inter {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A \ B).card + (A ∩ B).card = A.card := by
  have h : A ∩ B ⊆ A := Finset.inter_subset_left
  have eq : A \ (A ∩ B) = A \ B := by
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  simpa only [eq] using Finset.card_sdiff_add_card_eq_card h

private theorem cut_of_monotone {d : Nat} (edge : Fin d → Nat)
    (mono : Monotone edge) (k : Nat) :
    ∃ q ≤ d, ∀ j : Fin d, edge j < k ↔ j.val < q := by
  let H := (Finset.univ : Finset (Fin d)).filter (fun i => edge i < k)
  refine ⟨H.card, by simpa [H] using Finset.card_le_card (Finset.filter_subset (fun i => edge i<k) Finset.univ), ?_⟩
  intro j
  constructor
  · intro yes
    have sub : Finset.Iic j ⊆ H := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mono (Finset.mem_Iic.mp hi)).trans_lt yes⟩
    have cmp := Finset.card_le_card sub
    rw [Fin.card_Iic] at cmp
    omega
  · intro yes
    by_contra no
    have sub : H ⊆ Finset.Iio j := by
      intro i hi
      apply Finset.mem_Iio.mpr
      apply lt_of_not_ge
      intro bad
      exact no ((mono bad).trans_lt (Finset.mem_filter.mp hi).2)
    have cmp := Finset.card_le_card sub
    rw [Fin.card_Iio] at cmp
    omega

def front {T : Nat} (k : Nat) (S : Finset (Fin T)) : Finset (Fin T) :=
  S.filter (fun t => t.val<k)

theorem front_inter {T : Nat} (k : Nat) (A B : Finset (Fin T)) :
    front k (A ∩ B) = front k A ∩ front k B := by
  ext x
  simp only [front,Finset.mem_filter,Finset.mem_inter]
  tauto

theorem front_union {T : Nat} (k : Nat) (A B : Finset (Fin T)) :
    front k (A ∪ B) = front k A ∪ front k B := by
  ext x
  simp only [front,Finset.mem_filter,Finset.mem_union]
  tauto

theorem front_diff {T : Nat} (k : Nat) (A B : Finset (Fin T)) :
    front k (A \ B) = front k A \ front k B := by
  ext x
  simp only [front,Finset.mem_filter,Finset.mem_sdiff]
  tauto

theorem front_univ {T : Nat} (k : Nat) :
    (front k (Finset.univ : Finset (Fin T))).card = min T k := Fin.card_filter_val_lt

theorem front_subset {T : Nat} (k : Nat) {A B : Finset (Fin T)} (h : A⊆B) :
    front k A ⊆ front k B := fun _ hx =>
  Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩

theorem first_members {T : Nat} (S : Finset (Fin T)) (d : Nat) :
    ∃ P ⊆ S, ∀ k, (front k P).card = min d (front k S).card := by
  let ord := S.orderIsoOfFin (rfl : S.card=S.card)
  let entry (i : Fin S.card) : Fin T := (ord i).val
  have entry_inj : Function.Injective entry := fun _ _ h => ord.injective (Subtype.ext h)
  let P := (front d Finset.univ).image entry
  refine ⟨P,?_ ,?_⟩
  · intro t ht
    obtain ⟨i,_,ei⟩ := Finset.mem_image.mp ht
    exact ei ▸ (ord i).property
  · intro k
    have mono : Monotone (fun i => (entry i).val) := fun _ _ h => ord.monotone h
    obtain ⟨q,hq,cut⟩ := cut_of_monotone _ mono k
    have entry_before (i : Fin S.card) : (entry i).val < k ↔ i.val<q := cut i
    have sub_card (l : Nat) : (front l (Finset.univ : Finset (Fin S.card))).card = min S.card l := front_univ l
    have first : front k S = (front q Finset.univ).image entry := by
      ext t
      constructor
      · intro ht
        obtain ⟨inS,hk⟩ := Finset.mem_filter.mp ht
        let i := ord.symm ⟨t,inS⟩
        have r : entry i=t := congrArg Subtype.val (ord.apply_symm_apply ⟨t,inS⟩)
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (entry_before i).mp (r.symm ▸ hk)⟩,r⟩
      · intro ht
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_filter.mpr ⟨(ord i).property,
          (entry_before i).mpr (Finset.mem_filter.mp hi).2⟩
    have adj : front k P = (front (min d q) Finset.univ).image entry := by
      ext t
      constructor
      · intro ht
        obtain ⟨inP,hk⟩ := Finset.mem_filter.mp ht
        obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp inP
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_min ((Finset.mem_filter.mp hi).2) ((entry_before i).mp (eq.symm ▸ hk))⟩,eq⟩
      · intro ht
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
        have both := lt_min_iff.mp (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,both.1⟩,rfl⟩,(entry_before i).mpr both.2⟩
    rw [first,adj,Finset.card_image_of_injective _ entry_inj,
      Finset.card_image_of_injective _ entry_inj,sub_card,sub_card,min_eq_right hq,
      min_eq_right ((min_le_right _ _).trans hq)]

theorem total_of_front {T : Nat} (S : Finset (Fin T)) : front T S=S := by
  ext i
  simp [front,i.isLt]

theorem track_step {T : Nat} (S : Finset (Fin T)) (up down : Nat)
    (dn : down ≤ S.card) (un : up ≤ T-S.card) :
    ∃ P : Finset (Fin T), (S \ P).card=down ∧ (P \ S).card=up ∧
      ∀ k≤T, (front k (S \ P)).card=min down (front k S).card ∧
        (front k (P \ S)).card=min up (k-(front k S).card) := by
  obtain ⟨D,dS,dF⟩ := first_members S down
  obtain ⟨U,uS,uF⟩ := first_members (Finset.univ \ S) up
  let P := (S \ D) ∪ U
  have loss : S \ P = D := by
    ext t
    have ds : t∈D → t∈S := fun ht => dS ht
    have us : t∈U → t∉S := fun ht => (Finset.mem_sdiff.mp (uS ht)).2
    simp only [P,Finset.mem_sdiff,Finset.mem_union]
    tauto
  have raise : P \ S = U := by
    ext t
    have us : t∈U → t∉S := fun ht => (Finset.mem_sdiff.mp (uS ht)).2
    simp only [P,Finset.mem_sdiff,Finset.mem_union]
    tauto
  refine ⟨P, ?_,?_,?_⟩
  · rw [loss,←total_of_front D,dF,total_of_front,min_eq_left dn]
  · rw [raise,←total_of_front U,uF,total_of_front,Finset.card_sdiff_of_subset (Finset.subset_univ S),
      Finset.card_univ,Fintype.card_fin,min_eq_left un]
  · intro k hk
    rw [loss,raise,dF,uF,front_diff,Finset.card_sdiff_of_subset (front_subset _ (Finset.subset_univ S)),
      front_univ,min_eq_right hk]
    exact ⟨rfl,rfl⟩

theorem card_next {α : Type*} [DecidableEq α] (P Q : Finset α) :
    Q.card=P.card-(P \ Q).card+(Q \ P).card := by
  have p := card_close_inter P Q
  have q := card_close_inter Q P
  rw [Finset.inter_comm Q P] at q
  omega

def budgetAt {n : Nat} (up down : Fin n → Nat) (k c0 : Nat) (j : Fin (n+1)) : Nat × Nat :=
  ((List.finRange n).take j.val).foldl
    (fun a i => (min (a.1+down i) a.2,min (a.2+up i) (a.1+k)))
    (0,min k c0)

theorem budgetAt_zero {n : Nat} (up down : Fin n → Nat) (k c0 : Nat) :
    budgetAt up down k c0 0 = (0,min k c0) := rfl

theorem budgetAt_succ {n : Nat} (up down : Fin n → Nat) (k c0 : Nat) (i : Fin n) :
    let a := budgetAt up down k c0 i.castSucc
    budgetAt up down k c0 i.succ = (min (a.1+down i) a.2,min (a.2+up i) (a.1+k)) := by
  intro a
  have hi : i.val < (List.finRange n).length := by simpa using i.isLt
  simp only [budgetAt,Fin.val_succ,Fin.val_castSucc,a]
  rw [List.take_succ_eq_append_getElem hi,List.foldl_append]
  simp

def lost {T n : Nat} (S : Fin (n+1) → Finset (Fin T)) (k : Nat) (i : Fin n) :=
  (front k (S i.castSucc \ S i.succ)).card

def gained {T n : Nat} (S : Fin (n+1) → Finset (Fin T)) (k : Nat) (i : Fin n) :=
  (front k (S i.succ \ S i.castSucc)).card

def loaded {T n : Nat} (S : Fin (n+1) → Finset (Fin T)) (k : Nat) (j : Fin (n+1)) :=
  (front k (S j)).card

def spent {T n : Nat} (S : Fin (n+1) → Finset (Fin T)) (k : Nat) (j : Fin (n+1)) :=
  (front j.val Finset.univ).sum (lost S k)

theorem spent_succ {T n : Nat} (S : Fin (n+1) → Finset (Fin T)) (k : Nat) (i : Fin n) :
    spent S k i.succ = spent S k i.castSucc+lost S k i := by
  have sub : front i.succ.val (Finset.univ : Finset (Fin n)) = insert i (front i.castSucc.val Finset.univ) := by
    ext j
    simp only [front,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Fin.val_castSucc,Fin.val_succ]
    constructor
    · intro h
      by_cases e : j.val=i.val
      · exact Or.inl (Fin.ext e)
      · exact Or.inr (by omega)
    · rintro (rfl | h) <;> omega
  unfold spent
  rw [sub,Finset.sum_insert (by simp [front]),Nat.add_comm]

theorem account {T n : Nat} (S : Fin (n+1) → Finset (Fin T)) (k : Nat) (i : Fin n) :
    spent S k i.succ+loaded S k i.succ =
      spent S k i.castSucc+loaded S k i.castSucc+gained S k i := by
  have counts := card_next (front k (S i.castSucc)) (front k (S i.succ))
  rw [← front_diff,← front_diff] at counts
  change loaded S k i.succ = loaded S k i.castSucc-lost S k i+gained S k i at counts
  have hd : lost S k i ≤ loaded S k i.castSucc :=
    Finset.card_le_card (front_subset k Finset.sdiff_subset)
  rw [spent_succ]
  omega

theorem budget_bound {T n : Nat} (up down : Fin n → Nat) (c0 k : Nat)
    (S : Fin (n+1) → Finset (Fin T)) (start : (S 0).card=c0)
    (right : ∀ i, (S i.castSucc \ S i.succ).card=down i ∧ (S i.succ \ S i.castSucc).card=up i)
    (kT : k≤T) (j : Fin (n+1)) :
    spent S k j ≤ (budgetAt up down k c0 j).1 ∧
      spent S k j+loaded S k j ≤ (budgetAt up down k c0 j).2 := by
  induction j using Fin.induction with
  | zero =>
    have hk : loaded S k 0 ≤ k := by
      have h := Finset.card_le_card (front_subset k (Finset.subset_univ (S 0)))
      rwa [front_univ,min_eq_right kT] at h
    have hs : loaded S k 0 ≤ c0 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq start
    simpa [spent,front,budgetAt] using le_min hk hs
  | succ i ih =>
    have hdl : lost S k i ≤ loaded S k i.castSucc :=
      Finset.card_le_card (front_subset k Finset.sdiff_subset)
    have hdb : lost S k i ≤ down i :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (right i).1
    have hul : gained S k i ≤ k-loaded S k i.castSucc := by
      have sub : S i.succ \ S i.castSucc ⊆ Finset.univ \ S i.castSucc :=
        Finset.sdiff_subset_sdiff (Finset.subset_univ _) (le_refl _)
      have h := Finset.card_le_card (front_subset k sub)
      simpa only [front_diff, Finset.card_sdiff_of_subset (front_subset k (Finset.subset_univ (S i.castSucc))),
        front_univ,min_eq_right kT,loaded,gained] using h
    have hub : gained S k i ≤ up i :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (right i).2
    rw [account,spent_succ,budgetAt_succ]
    constructor
    · exact le_min (Nat.add_le_add ih.1 hdb) ((Nat.add_le_add_left hdl _).trans ih.2)
    · have load_bound : loaded S k i.castSucc ≤ k := by
        have h := Finset.card_le_card (front_subset k (Finset.subset_univ (S i.castSucc)))
        rwa [front_univ,min_eq_right kT] at h
      exact le_min (Nat.add_le_add ih.2 hub) (by omega)

theorem budget_exact {T n : Nat} (up down : Fin n → Nat) (c0 k : Nat)
    (S : Fin (n+1) → Finset (Fin T)) (start : loaded S k 0=min k c0)
    (step : ∀ i, lost S k i=min (down i) (loaded S k i.castSucc) ∧
      gained S k i=min (up i) (k-loaded S k i.castSucc)) (j : Fin (n+1)) :
    (spent S k j,spent S k j+loaded S k j) = budgetAt up down k c0 j := by
  induction j using Fin.induction with
  | zero => simp [spent,front,budgetAt,start]
  | succ i ih =>
    have hfirst := congrArg Prod.fst ih
    have hsecond := congrArg Prod.snd ih
    simp only [Prod.fst,Prod.snd] at hfirst hsecond
    rw [account,spent_succ,budgetAt_succ,←hfirst,←hsecond,(step i).1,(step i).2]
    apply Prod.ext
    · dsimp only
      omega
    · dsimp only
      have lk : loaded S k i.castSucc≤k := by
        have h := Finset.card_le_card (front_subset k (Finset.subset_univ (S i.castSucc)))
        rw [front_univ] at h
        exact h.trans (min_le_right _ _)
      omega

theorem priority_timeline {T n : Nat} (c : Fin (n+1) → Nat)
    (up down : Fin n → Nat) (cap : ∀ j, c j≤T)
    (ok : ∀ i, down i ≤ c i.castSucc ∧ up i ≤ T-c i.castSucc ∧
      c i.succ=c i.castSucc-down i+up i) :
    ∃ S : Fin (n+1) → Finset (Fin T), (∀ j, (S j).card=c j) ∧
      (∀ i, (S i.castSucc \ S i.succ).card=down i ∧ (S i.succ \ S i.castSucc).card=up i) ∧
      ∀ k≤T, ∀ j, (spent S k j,spent S k j+loaded S k j)=budgetAt up down k (c 0) j := by
  classical
  let advance (i : Fin n) (A : Finset (Fin T)) :=
    if valid : down i ≤ A.card ∧ up i ≤ T-A.card then
      Classical.choose (track_step A (up i) (down i) valid.1 valid.2)
    else A
  let S : Fin (n+1) → Finset (Fin T) := Fin.induction (front (c 0) Finset.univ) advance
  have base : S 0=front (c 0) Finset.univ := by simp [S]
  have hop (i : Fin n) : S i.succ = advance i (S i.castSucc) := by simp [S]
  have chosen (i : Fin n) (valid : down i ≤ (S i.castSucc).card ∧ up i ≤ T-(S i.castSucc).card) :
      (S i.castSucc \ S i.succ).card=down i ∧ (S i.succ \ S i.castSucc).card=up i ∧
      ∀ k≤T, lost S k i=min (down i) (loaded S k i.castSucc) ∧
        gained S k i=min (up i) (k-loaded S k i.castSucc) := by
    have h := Classical.choose_spec (track_step (S i.castSucc) (up i) (down i) valid.1 valid.2)
    refine ⟨?_,?_,?_⟩
    · rw [hop]; simpa only [advance,dite_eq_left valid] using h.1
    · rw [hop]; simpa only [advance,dite_eq_left valid] using h.2.1
    · intro k hk
      simpa only [lost,gained,loaded,hop i,advance,dif_pos valid] using h.2.2 k hk
  have cards (j : Fin (n+1)) : (S j).card=c j := by
    induction j using Fin.induction with
    | zero => rw [base,front_univ,min_eq_right (cap 0)]
    | succ i ih =>
      have facts := chosen i (by rw [ih]; exact ⟨(ok i).1,(ok i).2.1⟩)
      rw [card_next (S i.castSucc) (S i.succ),facts.1,facts.2.1,ih,←(ok i).2.2]
  have valid (i : Fin n) : down i ≤ (S i.castSucc).card ∧ up i ≤ T-(S i.castSucc).card := by
    rw [cards]
    exact ⟨(ok i).1,(ok i).2.1⟩
  refine ⟨S,cards,fun i => ⟨(chosen i (valid i)).1,(chosen i (valid i)).2.1⟩,?_⟩
  intro k hk j
  apply budget_exact up down (c 0) k S ?_ (fun i => (chosen i (valid i)).2.2 k hk)
  have eq : front k (front (c 0) (Finset.univ : Finset (Fin T))) = front (min k (c 0)) Finset.univ := by
    ext i
    simp only [front,Finset.mem_filter,Finset.mem_univ,true_and,lt_min_iff]
    tauto
  rw [loaded,base,eq,front_univ,min_eq_right ((min_le_left _ _).trans hk)]

def drop (a b : Bool) : Int := if a = true ∧ b = false then 1 else 0

def diff (a b c d : Bool) : Int := drop b d - drop a c

theorem diff_unit (a b c d : Bool) : diff a b c d ≤ 1 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem diff_first (a b c d : Bool) (cd : c ≠ d) : diff a b c d ≤ (c.toNat : Int) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [diff,drop,Bool.toNat]

theorem diff_middle (a b c d : Bool) (ab : a ≠ b) (cd : c ≠ d) :
    diff a b c d = (c.toNat : Int)-(a.toNat : Int) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [diff,drop,Bool.toNat]

theorem diff_end (a b c : Bool) : diff a b c c ≤ 1-(a.toNat : Int) := by
  cases a <;> cases b <;> cases c <;> decide

def delta (a b : Nat → Bool) (k : Nat) : Int :=
  (Finset.range k).sum (fun i => diff (a i) (b i) (a (i+1)) (b (i+1)))

theorem delta_step (a b : Nat → Bool) (k : Nat) :
    delta a b (k+1) = delta a b k + diff (a k) (b k) (a (k+1)) (b (k+1)) :=
  Finset.sum_range_succ _ _

theorem across (a b : Nat → Bool) {p q : Nat} (pq : p<q)
    (end_same : a q=b q) (middle : ∀ k, p<k → k<q → a k≠b k) :
    delta a b q ≤ delta a b p + 1 := by
  by_cases next : q=p+1
  · rw [next,delta_step]
    exact add_le_add_right (diff_unit ..) _
  have below (k : Nat) (pk : p<k) (kq : k<q) :
      delta a b k ≤ delta a b p + (a k).toNat := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      by_cases first : k=p+1
      · subst k
        rw [delta_step]
        exact add_le_add_right (diff_first _ _ _ _ (middle _ pk kq)) _
      · have back : k-1+1=k := by omega
        have bound := ih (k-1) (by omega) (by omega) (by omega)
        have update := delta_step a b (k-1)
        rw [back] at update
        have shift := diff_middle (a (k-1)) (b (k-1)) (a k) (b k)
          (middle (k-1) (by omega) (by omega)) (middle k pk kq)
        rw [update,shift]
        omega
  have back : q-1+1=q := by omega
  have bound := below (q-1) (by omega) (by omega)
  have update := delta_step a b (q-1)
  rw [back,← end_same] at update
  have shift := diff_end (a (q-1)) (b (q-1)) (a q)
  omega

theorem hit_delta (a b : Nat → Bool) (m : Nat) (end_same : a m=b m) (v : Int)
    (nonneg : 0 ≤ v) (full : v ≤ delta a b m) :
    ∃ k ≤ m, (k=0 ∨ a k=b k) ∧ delta a b k=v := by
  classical
  by_cases zero : v=0
  · exact ⟨0,Nat.zero_le _,Or.inl rfl,by simp [delta,zero]⟩
  let ok (k : Nat) := k=0 ∨ a k=b k
  have ex : ∃ k, k≤m ∧ ok k ∧ v≤delta a b k := ⟨m,le_rfl,Or.inr end_same,full⟩
  let q := Nat.find ex
  obtain ⟨qm, hq, vq⟩ : q≤m ∧ ok q ∧ v≤delta a b q := Nat.find_spec ex
  have qpos : 0<q := by
    by_contra bad
    have h : q=0 := by omega
    rw [h] at vq
    simp [delta] at vq
    omega
  have eq : a q=b q := hq.resolve_left (by omega)
  let S := (Finset.range q).filter ok
  have nonempty : S.Nonempty := ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr qpos,Or.inl rfl⟩⟩
  let p := S.max' nonempty
  have p_yes := Finset.mem_filter.mp (S.max'_mem nonempty)
  have pq : p<q := Finset.mem_range.mp p_yes.1
  have prev : delta a b p < v := by
    apply lt_of_not_ge
    intro v_p
    exact Nat.find_min ex (show p<Nat.find ex from pq) ⟨pq.le.trans qm,p_yes.2,v_p⟩
  have middle (k : Nat) (pk : p<k) (kq : k<q) : a k≠b k := by
    intro h
    have inS : k∈S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr kq,Or.inr h⟩
    exact (not_lt_of_ge (S.le_max' k inS)) pk
  have gap := across a b pq eq middle
  exact ⟨q,qm,hq,by omega⟩

def extTrack {n : Nat} (w : Fin (n+1) → Bool) (t : Nat) : Bool :=
  if h : t<n+1 then w ⟨t,h⟩ else true

theorem at_cast {n : Nat} (w : Fin (n+1) → Bool) (i : Fin n) :
    extTrack w i.val = w i.castSucc := by
  simp only [extTrack,dite_eq_left (i.isLt.trans (Nat.lt_succ_self _))]
  congr 1

theorem at_succ {n : Nat} (w : Fin (n+1) → Bool) (i : Fin n) :
    extTrack w (i.val+1) = w i.succ := by
  simp only [extTrack,dite_eq_left (Nat.succ_lt_succ i.isLt)]
  congr 1

theorem padded_delta {n : Nat} (a b : Fin (n+1) → Bool) (k : Nat) (bound : k≤n+1) :
    delta (extTrack a) (extTrack b) k =
      ∑ i : Fin n, if i.val<k then diff (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) else 0 := by
  let term (i : Nat) := diff (extTrack a i) (extTrack b i) (extTrack a (i+1)) (extTrack b (i+1))
  have eq : (Finset.range n).filter (fun i => i<k) = Finset.range (min n k) := by
    ext i
    simp [lt_min_iff]
  calc
    _ = (Finset.range (min n k)).sum term := by
      by_cases kn : k≤n
      · simp [delta,term,min_eq_right kn]
      · have h : k=n+1 := by omega
        rw [h,min_eq_left (Nat.le_succ _),delta_step]
        simp [delta,term,extTrack,diff,drop]
    _ = ∑ i ∈ Finset.range n, if i<k then term i else 0 := by rw [←eq,Finset.sum_filter]
    _ = _ := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp [term,at_cast,at_succ]

def rawFalls {n : Nat} (w : Fin (n+1) → Bool) : Nat :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => w i.castSucc = true ∧ w i.succ = false)).card

theorem sum_falls {n : Nat} (w : Fin (n+1) → Bool) :
    (rawFalls w : Int) = ∑ i : Fin n, drop (w i.castSucc) (w i.succ) := by
  rw [rawFalls, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold drop
  split_ifs <;> norm_num

theorem swap_counts {n : Nat} (a b : Fin (n+1) → Bool) (k : Nat)
    (ok : k=0 ∨ extTrack a k=extTrack b k) :
    let x := fun i : Fin (n+1) => if i.val<k then b i else a i
    let y := fun i : Fin (n+1) => if i.val<k then a i else b i
    ((rawFalls x : Int) = rawFalls a +
      ∑ i : Fin n, if i.val<k then diff (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) else 0) ∧
    rawFalls y + rawFalls x = rawFalls a + rawFalls b ∧
    ∀ i : Fin n,
      ((x i.castSucc, x i.succ) = (a i.castSucc, a i.succ) ∧
       (y i.castSucc, y i.succ) = (b i.castSucc, b i.succ)) ∨
      ((x i.castSucc, x i.succ) = (b i.castSucc, b i.succ) ∧
       (y i.castSucc, y i.succ) = (a i.castSucc, a i.succ)) := by
  intro x y
  have retain (i : Fin n) (ge : ¬ i.val<k) :
      x i.castSucc=a i.castSucc ∧ x i.succ=a i.succ ∧
      y i.castSucc=b i.castSucc ∧ y i.succ=b i.succ := by
    have ge' : ¬i.val+1<k := by omega
    simp [x,y,ge,ge']
  have swap (i : Fin n) (lt : i.val<k) :
      x i.castSucc=b i.castSucc ∧ x i.succ=b i.succ ∧
      y i.castSucc=a i.castSucc ∧ y i.succ=a i.succ := by
    by_cases lt' : i.val+1<k
    · simp [x,y,lt,lt']
    · have cut : k=i.val+1 := by omega
      have same := ok.resolve_left (by omega)
      simp only [cut,at_succ] at same
      simp [x,y,lt,lt',same]
  have counts (i : Fin n) :
      drop (x i.castSucc) (x i.succ) =
        drop (a i.castSucc) (a i.succ) +
        (if i.val<k then diff (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) else 0) := by
    by_cases h : i.val<k
    · obtain ⟨e₁,e₂,_,_⟩ := swap i h
      simp [e₁,e₂,h,diff]
    · obtain ⟨e₁,e₂,_,_⟩ := retain i h
      simp [e₁,e₂,h]
  have total (i : Fin n) :
      drop (y i.castSucc) (y i.succ) + drop (x i.castSucc) (x i.succ) =
        drop (a i.castSucc) (a i.succ) + drop (b i.castSucc) (b i.succ) := by
    by_cases h : i.val<k
    · obtain ⟨e₁,e₂,e₃,e₄⟩ := swap i h
      simp [e₁,e₂,e₃,e₄]
    · obtain ⟨e₁,e₂,e₃,e₄⟩ := retain i h
      simp [e₁,e₂,e₃,e₄,add_comm]
  refine ⟨?_,?_,?_⟩
  · rw [sum_falls,sum_falls,←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => counts i)
  · apply Int.ofNat_inj.mp
    push_cast
    rw [sum_falls,sum_falls,sum_falls,sum_falls,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => total i)
  · intro i
    by_cases h : i.val<k
    · obtain ⟨a,b,c,d⟩ := swap i h
      exact Or.inr ⟨Prod.ext a b,Prod.ext c d⟩
    · obtain ⟨a,b,c,d⟩ := retain i h
      exact Or.inl ⟨Prod.ext a b,Prod.ext c d⟩

theorem prefix_exchange :
  ∀ (n : Nat) (a b : Fin (n+1) → Bool),
    let falls := fun (w : Fin (n+1) → Bool) =>
      ((Finset.univ : Finset (Fin n)).filter (fun i => w i.castSucc = true ∧ w i.succ = false)).card
    ∀ k : Nat, falls a ≤ k → k ≤ falls b →
      ∃ cut : Nat, cut ≤ n+1 ∧ (∀ i : Fin (n+1), i.val = cut → a i = b i ∨ cut = 0) ∧
        let x := fun i : Fin (n+1) => if i.val < cut then b i else a i
        let y := fun i : Fin (n+1) => if i.val < cut then a i else b i
        falls x = k ∧ falls y + k = falls a + falls b ∧
        ∀ i : Fin n,
          ((x i.castSucc, x i.succ) = (a i.castSucc, a i.succ) ∧
           (y i.castSucc, y i.succ) = (b i.castSucc, b i.succ)) ∨
          ((x i.castSucc, x i.succ) = (b i.castSucc, b i.succ) ∧
           (y i.castSucc, y i.succ) = (a i.castSucc, a i.succ)) := by
  classical
  intro n a b falls k a_le le_b
  change rawFalls a ≤ k at a_le
  change k ≤ rawFalls b at le_b
  have full : delta (extTrack a) (extTrack b) (n+1) =
      (rawFalls b : Int) - (rawFalls a : Int) := by
    rw [padded_delta a b _ le_rfl,sum_falls,sum_falls,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [if_pos (show i.val<n+1 from i.isLt.trans (Nat.lt_succ_self _))]
    rfl
  obtain ⟨cut,bound,valid,amount⟩ :=
    hit_delta (extTrack a) (extTrack b) (n+1) (by simp [extTrack]) ((k : Int)-rawFalls a)
      (by omega) (by omega)
  refine ⟨cut,bound,?_,?_⟩
  · intro i hi
    rcases valid with zero | eq
    · exact Or.inr zero
    · left
      rw [← hi] at eq
      simpa [extTrack,i.isLt] using eq
  intro x y
  obtain ⟨size,total,pairs⟩ := swap_counts a b cut valid
  rw [padded_delta a b cut bound] at amount
  have equal : rawFalls x=k := by change (rawFalls x : Int) = _ at size; omega
  refine ⟨equal, ?_, pairs⟩
  change rawFalls y+k = rawFalls a+rawFalls b
  rwa [← equal]

def trailFalls {n : Nat} (w : Fin (n+1) → Bool) : Nat :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => w i.castSucc=true ∧ w i.succ=false)).card

def countOn {T n : Nat} (w : Fin T → Fin (n+1) → Bool) (j : Fin (n+1)) :=
  (Finset.univ.filter (fun t => w t j=true)).card

def countEdges {T n : Nat} (w : Fin T → Fin (n+1) → Bool) (i : Fin n) (a b : Bool) :=
  (Finset.univ.filter (fun t => w t i.castSucc=a ∧ w t i.succ=b)).card

def later {T : Nat} (k : Nat) := (Finset.univ : Finset (Fin T)).filter (fun t => k≤t.val)

theorem sum_pair_exchange {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (S : Finset α) (a b : α) (ab : a ≠ b) (ha : a∈S) (hb : b∈S)
    (x y : α → β) (same : ∀ t, t≠a → t≠b → y t=x t)
    (balance : y a+y b = x a+x b) :
    S.sum y = S.sum x := by
  have hb' : b ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm ab,hb⟩
  have rest : ((S.erase a).erase b).sum y = ((S.erase a).erase b).sum x := by
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨nb,ht⟩ := Finset.mem_erase.mp ht
    exact same t (Finset.mem_erase.mp ht).1 nb
  have ys := (Finset.sum_erase_add S y ha).symm
  rw [← Finset.sum_erase_add (S.erase a) y hb'] at ys
  have xs := (Finset.sum_erase_add S x ha).symm
  rw [← Finset.sum_erase_add (S.erase a) x hb'] at xs
  rw [ys,xs,rest]
  calc
    _ = ((S.erase a).erase b).sum x+(y a+y b) := by ac_rfl
    _ = ((S.erase a).erase b).sum x+(x a+x b) := by rw [balance]
    _ = _ := by ac_rfl

theorem sum_single_exchange {α : Type*} [DecidableEq α] (S : Finset α) (a : α) (ha : a∈S)
    (x y : α → Nat) (same : ∀ t, t≠a → y t=x t) (less : y a<x a) :
    S.sum y < S.sum x := by
  have rest : (S.erase a).sum y = (S.erase a).sum x := by
    apply Finset.sum_congr rfl
    intro t ht
    exact same t (Finset.mem_erase.mp ht).1
  rw [← Finset.sum_erase_add S y ha,← Finset.sum_erase_add S x ha,rest]
  exact Nat.add_lt_add_left less _

private theorem preserve_counts {T n : Nat} (w z : Fin T → Fin (n+1) → Bool) (a b : Fin T)
    (ne : a≠b) (same : ∀ t, t≠a → t≠b → z t=w t)
    (rows : ∀ j, (z a j=w a j ∧ z b j=w b j) ∨ (z a j=w b j ∧ z b j=w a j))
    (pairs : ∀ i : Fin n,
      ((z a i.castSucc,z a i.succ)=(w a i.castSucc,w a i.succ) ∧
        (z b i.castSucc,z b i.succ)=(w b i.castSucc,w b i.succ)) ∨
      ((z a i.castSucc,z a i.succ)=(w b i.castSucc,w b i.succ) ∧
        (z b i.castSucc,z b i.succ)=(w a i.castSucc,w a i.succ))) :
    (∀ j, countOn z j=countOn w j) ∧ (∀ i x y, countEdges z i x y=countEdges w i x y) := by
  constructor
  · intro j
    unfold countOn
    rw [Finset.card_filter,Finset.card_filter]
    apply sum_pair_exchange Finset.univ a b ne (Finset.mem_univ _) (Finset.mem_univ _)
    · intro t ha hb
      rw [same t ha hb]
    · rcases rows j with ⟨p,q⟩ | ⟨p,q⟩
      · rw [p,q]
      · rw [p,q,Nat.add_comm]
  · intro i x y
    unfold countEdges
    rw [Finset.card_filter,Finset.card_filter]
    apply sum_pair_exchange Finset.univ a b ne (Finset.mem_univ _) (Finset.mem_univ _)
    · intro t ha hb
      rw [same t ha hb]
    · rcases pairs i with ⟨p,q⟩ | ⟨p,q⟩ <;> simp only [Prod.mk.injEq] at p q
      · rw [p.1,p.2,q.1,q.2]
      · rw [p.1,p.2,q.1,q.2,Nat.add_comm]

theorem redistribute {T n : Nat} (want : Fin T → Nat) (antitone : Antitone want)
    (initial : Fin T → Fin (n+1) → Bool)
    (tail : ∀ k, (later k).sum (fun t => trailFalls (initial t)) ≤ (later k).sum want) :
    ∃ w : Fin T → Fin (n+1) → Bool, (∀ t, trailFalls (w t) ≤ want t) ∧
      (∀ j, countOn w j=countOn initial j) ∧
      (∀ i x y, countEdges w i x y=countEdges initial i x y) := by
  classical
  let coeff (w : Fin T → Fin (n+1) → Bool) (t : Fin T) := trailFalls (w t)
  let penalty (w : Fin T → Fin (n+1) → Bool) := ∑ t, (coeff w t-want t)
  let stable (w : Fin T → Fin (n+1) → Bool) :=
    (∀ k, (later k).sum (coeff w) ≤ (later k).sum want) ∧
    (∀ j, countOn w j=countOn initial j) ∧
    (∀ i x y, countEdges w i x y=countEdges initial i x y)
  have ex : ∃ p, ∃ w, stable w ∧ penalty w=p := ⟨penalty initial,initial,⟨tail,by simp,by simp⟩,rfl⟩
  let p := Nat.find ex
  obtain ⟨w,good,least⟩ : ∃ w, stable w ∧ penalty w=p := Nat.find_spec ex
  refine ⟨w,?_,good.2.1,good.2.2⟩
  intro t
  by_contra! over
  let U := (Finset.univ : Finset (Fin T)).filter (fun s => want s<coeff w s)
  have un : U.Nonempty := ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,over⟩⟩
  let a := U.max' un
  have excess : want a<coeff w a := (Finset.mem_filter.mp (U.max'_mem un)).2
  have within (s : Fin T) (h : a<s) : coeff w s≤want s := by
    by_contra! no
    exact (not_lt_of_ge (U.le_max' s (Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩))) h
  have recipient : ∃ b : Fin T, a<b ∧ coeff w b<want b := by
    by_contra! no
    have lt : (later a.val).sum want < (later a.val).sum (coeff w) := by
      apply Finset.sum_lt_sum
      · intro s hs
        have le : a≤s := (Finset.mem_filter.mp hs).2
        rcases lt_or_eq_of_le le with h | e
        · exact no s h
        · rw [←e]
          exact excess.le
      · exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_rfl⟩,excess⟩
    exact (not_lt_of_ge (good.1 a.val)) lt
  obtain ⟨b,ab,slack⟩ := recipient
  have order := antitone ab.le
  have needed : coeff w b+1≤coeff w a := by omega
  have low : trailFalls (w b)≤coeff w b+1 := Nat.le_succ _
  obtain ⟨cut,_,_,rules⟩ := prefix_exchange n (w b) (w a) (coeff w b+1) low needed
  let x (i : Fin (n+1)) := if i.val<cut then w a i else w b i
  let y (i : Fin (n+1)) := if i.val<cut then w b i else w a i
  let z (s : Fin T) := if s=a then y else if s=b then x else w s
  have at_a : z a=y := by simp [z]
  have at_b : z b=x := by simp [z,ab.ne.symm]
  have other (s : Fin T) (na : s≠a) (nb : s≠b) : z s=w s := by simp [z,na,nb]
  have nb : coeff z b=coeff w b+1 := by
    change trailFalls (z b)=coeff w b+1
    rw [at_b]
    exact rules.1
  have na : coeff z a+coeff z b=coeff w a+coeff w b := by
    rw [nb]
    change trailFalls (z a)+(coeff w b+1)=coeff w a+coeff w b
    rw [at_a,Nat.add_comm (coeff w a) (coeff w b)]
    exact rules.2.1
  have same (s : Fin T) (sa : s≠a) (sb : s≠b) : coeff z s=coeff w s := by
    dsimp [coeff]
    rw [other s sa sb]
  have inv := preserve_counts w z a b ab.ne other
    (fun i => by rw [at_a,at_b]; by_cases h : i.val<cut <;> simp [x,y,h])
    (fun i => by
      rw [at_a,at_b]
      rcases rules.2.2 i with h | h
      · exact Or.inl ⟨h.2,h.1⟩
      · exact Or.inr ⟨h.2,h.1⟩)
  have tz : ∀ k, (later k).sum (coeff z) ≤ (later k).sum want := by
    intro k
    by_cases ka : k≤a.val
    · have al : a∈later k := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ka⟩
      have bl : b∈later k := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ka.trans ab.le⟩
      rw [sum_pair_exchange (later k) a b ab.ne al bl _ _ same na]
      exact good.1 k
    · apply Finset.sum_le_sum
      intro s hs
      change coeff z s≤want s
      have as : a<s := by
        have ht := (Finset.mem_filter.mp hs).2
        show a.val<s.val
        omega
      by_cases sb : s=b
      · rw [sb,nb]
        omega
      · rw [same s as.ne.symm sb]
        exact within s as
  have stable_z : stable z := ⟨tz,fun j => (inv.1 j).trans (good.2.1 j),
    fun i x y => (inv.2 i x y).trans (good.2.2 i x y)⟩
  have shorter : penalty z < p := by
    rw [←least]
    dsimp only [penalty]
    apply sum_single_exchange Finset.univ a (Finset.mem_univ _)
    · intro s ne
      change coeff z s-want s=coeff w s-want s
      by_cases sb : s=b
      · rw [sb,nb]
        omega
      · rw [same s ne sb]
    · omega
  exact Nat.find_min ex (show penalty z<Nat.find ex from shorter) ⟨z,stable_z,rfl⟩

def asSets {T n : Nat} (w : Fin T → Fin (n+1) → Bool) (j : Fin (n+1)) :=
  Finset.univ.filter (fun t => w t j=true)

def asBits {T n : Nat} (S : Fin (n+1) → Finset (Fin T)) (t : Fin T) (j : Fin (n+1)) :=
  decide (t∈S j)

theorem by_columns {T n : Nat} (S : Fin (n+1) → Finset (Fin T)) :
    asSets (asBits S)=S := by
  funext j
  ext t
  simp [asSets,asBits]

theorem asSets_drop {T n : Nat} (w : Fin T → Fin (n+1) → Bool) (i : Fin n) :
    asSets w i.castSucc \ asSets w i.succ =
      Finset.univ.filter (fun t => w t i.castSucc=true ∧ w t i.succ=false) := by
  classical
  ext t
  simp [asSets]

theorem asSets_rise {T n : Nat} (w : Fin T → Fin (n+1) → Bool) (i : Fin n) :
    asSets w i.succ \ asSets w i.castSucc =
      Finset.univ.filter (fun t => w t i.castSucc=false ∧ w t i.succ=true) := by
  classical
  ext t
  simp [asSets,and_comm]

private theorem indicator_card {α : Type*} (A : Finset α) (P : α → Prop) [DecidablePred P] :
    (A.filter P).card = ∑ t ∈ A, if P t then (1 : Nat) else 0 := by
  rw [←Finset.sum_filter]
  simp

theorem exchanges_sum {T n : Nat} (w : Fin T → Fin (n+1) → Bool) (k : Nat) :
    spent (asSets w) k (Fin.last n) =
      (front k Finset.univ).sum (fun t => trailFalls (w t)) := by
  classical
  have final : front (Fin.last n).val (Finset.univ : Finset (Fin n)) = Finset.univ := by
    exact total_of_front _
  have lost_eq (i : Fin n) :
      front k (asSets w i.castSucc \ asSets w i.succ) =
        (front k Finset.univ).filter (fun t => w t i.castSucc=true ∧ w t i.succ=false) := by
    rw [asSets_drop]
    ext t
    simp [front,and_comm]
  simp only [spent,final,trailFalls,indicator_card]
  calc
    _ = ∑ i : Fin n, ∑ t ∈ front k Finset.univ,
        if w t i.castSucc=true ∧ w t i.succ=false then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lost,lost_eq,indicator_card]
    _ = _ := Finset.sum_comm

theorem exchanges_total {T n : Nat} (w : Fin T → Fin (n+1) → Bool) :
    (∑ t, trailFalls (w t))=∑ i, countEdges w i true false := by
  classical
  simp only [countEdges,trailFalls,indicator_card]
  rw [Finset.sum_comm]

theorem partition_budget {T : Nat} (f : Fin T → Nat) (k : Nat) :
    (front k Finset.univ).sum f+(later k).sum f=∑ t, f t := by
  have joined : front k (Finset.univ : Finset (Fin T)) ∪ later k = Finset.univ := by
    ext t
    simp [front,later,le_or_gt,or_comm]
  have dis : Disjoint (front k Finset.univ : Finset (Fin T)) (later k) := by
    apply Finset.disjoint_left.mpr
    intro t h1 h2
    exact (Nat.not_lt_of_ge (Finset.mem_filter.mp h2).2) (Finset.mem_filter.mp h1).2
  rw [←Finset.sum_union dis,joined]

end PEqualNP.Outside.L_lib_1417_aux

open PEqualNP.Outside.L_lib_1417_aux

theorem PEqualNP.Outside.L_lib_1417 :
  ∀ (T n : Nat) (c : Fin (n+1) → Nat) (up down : Fin n → Nat) (want : Fin T → Nat),
    Antitone want → (∀ j, c j ≤ T) →
    (∀ i, down i ≤ c i.castSucc ∧ up i ≤ T - c i.castSucc ∧
      c i.succ = c i.castSucc - down i + up i) →
    let limit := fun (k : Nat) => ((List.finRange n).foldl
      (fun (s : Nat × Nat) (i : Fin n) =>
        (min (s.1 + down i) s.2, min (s.2 + up i) (s.1 + k)))
      (0, min k (c 0))).1
    (∃ w : Fin T → Fin (n+1) → Bool,
      (∀ j, ((Finset.univ : Finset (Fin T)).filter (fun t => w t j = true)).card = c j) ∧
      (∀ i : Fin n,
        ((Finset.univ : Finset (Fin T)).filter
          (fun t => w t i.castSucc = false ∧ w t i.succ = true)).card = up i ∧
        ((Finset.univ : Finset (Fin T)).filter
          (fun t => w t i.castSucc = true ∧ w t i.succ = false)).card = down i) ∧
      (∀ t, ((Finset.univ : Finset (Fin n)).filter
        (fun i => w t i.castSucc = true ∧ w t i.succ = false)).card = want t)) ↔
    (Finset.univ : Finset (Fin T)).sum want = (Finset.univ : Finset (Fin n)).sum down ∧
      ∀ k ≤ T, ((Finset.univ : Finset (Fin T)).filter (fun t => t.val < k)).sum want ≤ limit k := by
  classical
  intro T n c up down want anti cap rule limit
  have final (k : Nat) : (budgetAt up down k (c 0) (Fin.last n)).1=limit k := by
    simp only [budgetAt,limit,Fin.val_last]
    rw [List.take_of_length_le (by simp)]
  constructor
  · rintro ⟨w,rows,edges,falls⟩
    have good (i : Fin n) :
        (asSets w i.castSucc \ asSets w i.succ).card=down i ∧
        (asSets w i.succ \ asSets w i.castSucc).card=up i := by
      rw [asSets_drop,asSets_rise]
      exact ⟨(edges i).2,(edges i).1⟩
    refine ⟨?_,?_⟩
    · calc
        ∑ t, want t = ∑ t, trailFalls (w t) := Finset.sum_congr rfl (fun t _ => (falls t).symm)
        _ = ∑ i, countEdges w i true false := exchanges_total w
        _ = ∑ i, down i := Finset.sum_congr rfl (fun i _ => (edges i).2)
    · intro k hk
      have load := (budget_bound up down (c 0) k (asSets w) (rows 0) good hk (Fin.last n)).1
      rw [exchanges_sum,final] at load
      simpa only [trailFalls, falls,front] using load
  · rintro ⟨total,cuts⟩
    obtain ⟨S,cards,step,bounds⟩ := priority_timeline c up down cap rule
    let initial := asBits S
    have from_bits : asSets initial=S := by simp [initial,by_columns]
    have counts (j : Fin (n+1)) : countOn initial j=c j := by
      change (asSets initial j).card=c j
      rw [from_bits]
      exact cards j
    have events (i : Fin n) :
        countEdges initial i false true=up i ∧ countEdges initial i true false=down i := by
      unfold countEdges
      rw [←asSets_rise,←asSets_drop,from_bits]
      exact ⟨(step i).2,(step i).1⟩
    have total_init : (∑ t, trailFalls (initial t)) = ∑ t, want t := by
      rw [exchanges_total,total]
      exact Finset.sum_congr rfl (fun i _ => (events i).2)
    have suffix (k : Nat) : (later k).sum (fun t => trailFalls (initial t)) ≤ (later k).sum want := by
      by_cases hk : k≤T
      · have earlier : (front k Finset.univ).sum want ≤
            (front k Finset.univ).sum (fun t => trailFalls (initial t)) := by
          rw [←exchanges_sum,from_bits]
          have eq := congrArg Prod.fst (bounds k hk (Fin.last n))
          change spent S k (Fin.last n)=(budgetAt up down k (c 0) (Fin.last n)).1 at eq
          rw [eq,final]
          exact cuts k hk
        have A := partition_budget (fun t => trailFalls (initial t)) k
        have B := partition_budget want k
        omega
      · have empty : (later k : Finset (Fin T))=∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact hk ((Finset.mem_filter.mp ht).2.trans t.isLt.le)
        simp [empty]
    obtain ⟨w,fit,rows,edges⟩ := redistribute want anti initial suffix
    have fixed_events (i : Fin n) :
        countEdges w i false true=up i ∧ countEdges w i true false=down i :=
      ⟨(edges i false true).trans (events i).1,(edges i true false).trans (events i).2⟩
    refine ⟨w,fun j => (rows j).trans (counts j),fixed_events,?_⟩
    intro t
    change trailFalls (w t)=want t
    apply le_antisymm (fit t)
    by_contra! bad
    have mismatch : (∑ t, trailFalls (w t)) < ∑ t, want t :=
      Finset.sum_lt_sum (fun s _ => fit s) ⟨t,Finset.mem_univ _,bad⟩
    rw [exchanges_total,total] at mismatch
    have exactSum : (∑ i, countEdges w i true false)=∑ i, down i :=
      Finset.sum_congr rfl (fun i _ => (fixed_events i).2)
    exact (lt_irrefl _) (exactSum ▸ mismatch)
