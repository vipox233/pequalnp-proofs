import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38593

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276677352 * 2 ^ 32 + 4008241384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x0002283140c51450#64 ++ 0x90002283140c5145#64 ++ 0xf00679f3d1cf3cff#64 ++ 0xef00679f3d1cf3cf#64 : BitVec 256),
   (0x0018928486124925#64 ++ 0x2001892848612492#64 ++ 0xfc399e8cee33cf3f#64 ++ 0xdfc399e8cee33cf3#64 : BitVec 256),
   (0x01c1450a3028a288#64 ++ 0x001c1450a3028a28#64 ++ 0xf3c1e70f303cf3cb#64 ++ 0xbf3c1e70f303cf3c#64 : BitVec 256),
   (0x06ec07d03b40fc01#64 ++ 0xc06ec07d03b40fc0#64 ++ 0x8ffe07f03fc0fc0f#64 ++ 0x78ffe07f03fc0fc0#64 : BitVec 256),
   (0x2b77f8003dbf000e#64 ++ 0x02b77f8003dbf000#64 ++ 0xaffff8003fff0006#64 ++ 0xfaffff8003fff000#64 : BitVec 256),
   (0x4bbfffefc0000000#64 ++ 0x04bbfffefc000000#64 ++ 0xcbffffffc0000001#64 ++ 0xfcbffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [6, 10]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0002282140000000 0x0000228214000000 0xc00679f3c0000001 0xec00679f3c000000

def z1 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xf00679f3d1cf3cff 0xef00679f3d1cf3cf

def z2 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc399e8cee33cf3f 0xdfc399e8cee33cf3

def z3 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c1e70f303cf3cb 0xbf3c1e70f303cf3c

def z4 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe07f03fc0fc0f 0x78ffe07f03fc0fc0

def z5 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xaffff8003fff0006 0xfaffff8003fff000

def z6 : W := mkw 0x4bbdd7ce80000000 0x04bbdd7ce8000000 0x0bf9860c00000000 0x10bf9860c0000000

def z7 : W := mkw 0x408807ffc0401450 0x9408807ffc040145 0x500007ffc0003cf9 0x0500007ffc0003cf

def z8 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbffffffc0000001 0xfcbffffffc000000

def z9 : W := mkw 0x205090003dbf000e 0x0205090003dbf000 0xac3998003fff0006 0xdac3998003fff000

def z10 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x03c6617300000000 0x203c661730000000

def z11 : W := mkw 0x418947efc0000000 0x0418947efc000000 0xc3c1e7ffc0000001 0xbc3c1e7ffc000000

def z12 : W := mkw 0x0002280000000000 0x0000228000000000 0x8006780000000000 0xe800678000000000

def z13 : W := mkw 0x0264001039401400 0x8026400103940140 0x8ffe01f03fc03c0f 0x78ffe01f03fc03c0

def z14 : W := mkw 0x0bb7fd0a00000000 0x00bb7fd0a0000000 0xcbffff0f00000001 0xfcbffff0f0000000

def z15 : W := mkw 0x2fe76d5039edb40a 0xc2fe76d5039edb40 0x03c6617011cc3000 0x203c6617011cc300

def z16 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x8bfe07f000000001 0x78bfe07f00000000

def z17 : W := mkw 0x06e405403900a000 0x406e405403900a00 0x03c0000000000000 0x003c000000000000

def z18 : W := mkw 0x2b67680039ad000a 0x02b67680039ad000 0x03c6600011cc0000 0x203c6600011cc000

def z19 : W := mkw 0x01d9d78eb63aebad 0x201d9d78eb63aeba 0xfff9ff8ffe3fffff 0xffff9ff8ffe3ffff

def z20 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x000007f00000fc09 0x0000007f00000fc0

def z21 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x70067973d1cf30f0 0xa70067973d1cf30f

def z22 : W := mkw 0x2be76d0a39ada28a 0x02be76d0a39ada28 0xf3c7e70f31fcf3cb 0xbf3c7e70f31fcf3c

def z23 : W := mkw 0x0141400030280008 0x0014140003028000 0xa3c1e000303c0002 0xba3c1e000303c000

def z24 : W := mkw 0x0264000039000000 0x0026400003900000 0x8ffe00003fc00006 0x78ffe00003fc0000

def z25 : W := mkw 0x06ac07d00b405c01 0xc06ac07d00b405c0 0x8ffe07f00fc00c05 0x78ffe07f00fc00c0

def z26 : W := mkw 0x6bffffeffdbf000e 0x06bffffeffdbf000 0xefffffffffff0007 0xfefffffffffff000

def z27 : W := mkw 0x4bbfffffc0c51450 0x94bbfffffc0c5145 0xcbffffffd1cc30c1 0xfcbffffffd1cc30c

def z28 : W := mkw 0x0018928486124925 0x2001892848612492 0x0c381880ce030c34 0x40c381880ce030c3

def z29 : W := mkw 0x4bffffeff9000000 0x04bffffeff900000 0xcfffffffffc00007 0xfcfffffffffc0000

def z30 : W := mkw 0x2bffff8ebfbfebaf 0x22bffff8ebfbfeba 0xffffff8fffffffff 0xfffffff8ffffffff

def z31 : W := mkw 0x2bf7fd0a3dbf000e 0x02bf7fd0a3dbf000 0xefffff0f3fff0007 0xfefffff0f3fff000

def z32 : W := mkw 0x001abab5c6d75d75 0xb001abab5c6d75d7 0xfc3fffffffffffff 0xffc3ffffffffffff

def z33 : W := mkw 0x0010900004120004 0x0001090000412000 0xac3998002e330006 0xdac3998002e33000

def z34 : W := mkw 0x062c02d00b405c01 0xc062c02d00b405c0 0x0c3e00f00fc00c04 0x40c3e00f00fc00c0

def z35 : W := mkw 0x06fc97d4bf52fd25 0xe06fc97d4bf52fd2 0xffff9ffcfff3ff3f 0xfffff9ffcfff3ff3

def z36 : W := mkw 0x06ac07d00b40fc01 0xc06ac07d00b40fc0 0x0c3e07f00fc0fc0d 0x40c3e07f00fc0fc0

def z37 : W := mkw 0x0080050a0000a280 0x00080050a0000a28 0x5000070f0000f3c9 0x05000070f0000f3c

def z38 : W := mkw 0x6bffffeffd3a000e 0x06bffffeffd3a000 0xcfffffffee300001 0xfcfffffffee30000

def z39 : W := mkw 0x0008028002004801 0x0000802800200480 0xfc39868c2e30cf0f 0xdfc39868c2e30cf0

def z40 : W := mkw 0x06ec07c03b00e801 0x406ec07c03b00e80 0x8ffe06003fc0c006 0x78ffe06003fc0c00

def z41 : W := mkw 0x06ee2ff17b40fc01 0xc06ee2ff17b40fc0 0xcffe7ff3ffc0fc0f 0xfcffe7ff3ffc0fc0

def z42 : W := mkw 0x06ec07da3b40fe81 0xc06ec07da3b40fe8 0xdffe07ff3fc0ffcf 0x7dffe07ff3fc0ffc

def z43 : W := mkw 0x2953f8003dbf000e 0x02953f8003dbf000 0x2401f8003fff0006 0x82401f8003fff000

def z44 : W := mkw 0x2f77f8103ffffc0f 0xc2f77f8103ffffc0 0xaffff8003ffffc0e 0xfaffff8003ffffc0

def z45 : W := mkw 0x000000000000a280 0x0000000000000a28 0x100000000000f3c8 0x0100000000000f3c

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000008000000c0f 0x48000008000000c0

def z47 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x0fff98002ff30004 0x50fff98002ff3000

def z48 : W := mkw 0x0010900004120004 0x0001090000412000 0x0c3818000e030004 0x40c3818000e03000

def z49 : W := mkw 0x4bb7fd6fc0000000 0x04bb7fd6fc000000 0x43c7f97fc0000000 0xa43c7f97fc000000

def z50 : W := mkw 0x2a36b8000d970006 0x02a36b8000d97000 0x0c3e18000fc30004 0x40c3e18000fc3000

def z51 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xffffffffee33cf3f 0xfffffffffee33cf3

def z52 : W := mkw 0x04589294bf52fd25 0xe04589294bf52fd2 0xfc399e8cfff3ff3f 0xdfc399e8cfff3ff3

def z53 : W := mkw 0x2b77f80a3dbf028e 0x02b77f80a3dbf028 0xfffff80f3fff03c6 0xffffff80f3fff03c

def z54 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xfffe67f33fccfccf 0xffffe67f33fccfcc

def z55 : W := mkw 0x0000001000c51450 0x90000001000c5145 0x3000000011cf3cfe 0x03000000011cf3cf

def z56 : W := mkw 0x4baf6fefc0000000 0x04baf6fefc000000 0x43c667ffc0000001 0x243c667ffc000000

def z57 : W := mkw 0x4080056b40000000 0x04080056b4000000 0x0000017300000000 0x0000001730000000

def z58 : W := mkw 0x0010900484120124 0x2001090048412012 0xfc39980cee330336 0xdfc39980cee33033

def z59 : W := mkw 0x01c36d2b70ada2d8 0x101c36d2b70ada2d 0xf3c1ff0ff03ff3fb 0xbf3c1ff0ff03ff3f

def z60 : W := mkw 0x2b77f8317dff145e 0x92b77f8317dff145 0xfffff9f3ffff3cff 0xffffff9f3ffff3cf

def z61 : W := mkw 0x01c1451a30edb6d8 0x901c1451a30edb6d 0xf3c1e70f31ffffff 0xbf3c1e70f31fffff

def z62 : W := mkw 0x6bffffefffbf492f 0x26bffffefffbf492 0xffffffffffffcf3f 0xfffffffffffffcf3

def z63 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x040000003fc0fc0e 0x0040000003fc0fc0

def z64 : W := mkw 0x408807efc0000000 0x0408807efc000000 0x400007ffc0000001 0x0400007ffc000000

def z65 : W := mkw 0x02bc97c480000000 0x002bc97c48000000 0xcbff9ffcc0000001 0xfcbff9ffcc000000

def z66 : W := mkw 0x2bf7fd0a3dbfa28e 0x02bf7fd0a3dbfa28 0xaffff9033fff30c6 0xfaffff9033fff30c

def z67 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xfbffffffc0030c3f 0xffbffffffc0030c3

def z68 : W := mkw 0x0002282140850050 0x1000228214085005 0x70007803c00f00f0 0x870007803c00f00f

def z69 : W := mkw 0x4bbfffefc0850050 0x14bbfffefc085005 0xfbffffffc00f00f1 0xffbffffffc00f00f

def z70 : W := mkw 0x2b75d0003d3a000e 0x02b75d0003d3a000 0xaff998002e330006 0xdaff998002e33000

def z71 : W := mkw 0x2b7ffa84bfbf492f 0x22b7ffa84bfbf492 0xfffffe8cffffcf3f 0xffffffe8cffffcf3

def z72 : W := mkw 0x2b7dd284bf3a492f 0x22b7dd284bf3a492 0x0ff9860c2e30c300 0x10ff9860c2e30c30

def z73 : W := mkw 0x00c005003000a000 0x000c005003000a00 0x83c007003000f00b 0x383c007003000f00

def z74 : W := mkw 0x0b77f80030280008 0x00b77f8003028000 0xabfff800303c0002 0xfabfff800303c000

def z75 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x000618f0c1c30c34 0x4000618f0c1c30c3

def z76 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x53c1870f2030f3c9 0x153c1870f2030f3c

def z77 : W := mkw 0x2913f80004bf000e 0x02913f80004bf000 0x2001f800003f0000 0x82001f800003f000

def z78 : W := mkw 0x0b37f80000000000 0x00b37f8000000000 0x8bfff80000000000 0xf8bfff8000000000

def z79 : W := mkw 0x4bffffeff028a288 0x04bffffeff028a28 0xfbfffffff03cf3cb 0xffbfffffff03cf3c

def z80 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z81 : W := mkw 0x0181450a0028a288 0x00181450a0028a28 0x7001e70f003cf3c9 0x87001e70f003cf3c

def z82 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x03c0000000000000 0x003c000000000000

def z83 : W := mkw 0x4911d00e80000000 0x04911d00e8000000 0x0001800c00000000 0x00001800c0000000

def z84 : W := mkw 0x2b75d0003d3a000e 0x02b75d0003d3a000 0x0ff980002e300000 0x10ff980002e30000

def z85 : W := mkw 0x2bf7fd0a3dbfa28e 0x02bf7fd0a3dbfa28 0xffffff0f3ffff3cf 0xfffffff0f3ffff3c

def z86 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x3006617311cf3cfe 0x23006617311cf3cf

def z87 : W := mkw 0x0018928480000000 0x0001892848000000 0x0839860c00000000 0x10839860c0000000

def z88 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xf006617311cc30cb 0xaf006617311cc30c

def z89 : W := mkw 0x4bbfffefc2004801 0x04bbfffefc200480 0xcfffffffee00cc0f 0xfcfffffffee00cc0

def z90 : W := mkw 0x0008028002004801 0x0000802800200480 0x8c3806802e00cc0f 0x58c3806802e00cc0

def z91 : W := mkw 0x0b77f80039000000 0x00b77f8003900000 0x8ffff8003fc00006 0xf8ffff8003fc0000

def z92 : W := mkw 0x4ffffffffb40fc01 0xc4ffffffffb40fc0 0xcfffffffffc0fc0f 0xfcfffffffffc0fc0

def z93 : W := mkw 0x06ec07c03b00e801 0x406ec07c03b00e80 0x0ff806002e00c000 0x10ff806002e00c00

def z94 : W := mkw 0x07ed47da3b68fe89 0xc07ed47da3b68fe8 0xffffe7ff3ffcffcf 0xfffffe7ff3ffcffc

def z95 : W := mkw 0x0000000002004801 0x0000000000200480 0x040000002e00cc0e 0x0040000002e00cc0

def z96 : W := mkw 0x0018928480000000 0x0001892848000000 0xc8399e8cc0000001 0xdc8399e8cc000000

def z97 : W := mkw 0x06ee2ff17bc5fc51 0xd06ee2ff17bc5fc5 0x8ffe67f33fccfccf 0x78ffe67f33fccfcc

def z98 : W := mkw 0x06ec07d4bb40fd21 0xe06ec07d4bb40fd2 0xdffe07fcffc0ff3f 0x7dffe07fcffc0ff3

def z99 : W := mkw 0x02ac07c002004801 0x002ac07c00200480 0x8ffe07f02e00cc0f 0x78ffe07f02e00cc0

def z100 : W := mkw 0x0101400a00280288 0x00101400a0028028 0x7001e00f003c03c0 0x87001e00f003c03c

def z101 : W := mkw 0x4abebfe5c0000000 0x04abebfe5c000000 0x8bfe1ff0c0000001 0x78bfe1ff0c000000

def z102 : W := mkw 0x2bffffc03dbf000e 0x02bffffc03dbf000 0xaffffff03fff0007 0xfaffffff03fff000

def z103 : W := mkw 0x0224000000000000 0x0022400000000000 0x8bfe000000000000 0x78bfe00000000000

def z104 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xfffff9033fff30cf 0xffffff9033fff30c

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000610300000001 0xac00061030000000

def z106 : W := mkw 0x0103683b40ed16d8 0x90103683b40ed16d 0xf007f9ffd1ff3fff 0xef007f9ffd1ff3ff

def z107 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xc00679f3c1c30c35 0xec00679f3c1c30c3

def z108 : W := mkw 0x0008028000000000 0x0000802800000000 0x8838068000000001 0x5883806800000000

def z109 : W := mkw 0x2fffffd03ffffc0f 0xc2fffffd03ffffc0 0xaffffff03ffffc0f 0xfaffffff03ffffc0

def z110 : W := mkw 0x0008028482004921 0x2000802848200492 0xdc38068cee00cf3f 0x5dc38068cee00cf3

def z111 : W := mkw 0x0018928486124925 0x2001892848612492 0x3c39860c2e33cf3e 0x13c39860c2e33cf3

def z112 : W := mkw 0x26ec07d03ffffc0f 0xc26ec07d03ffffc0 0xaffe07f03ffffc0f 0x7affe07f03ffffc0

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0001880c0030c3f 0xcf0001880c0030c3

def z114 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x0fffe0003ffc0000 0x30fffe0003ffc000

def z115 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001860c2030c300 0x10001860c2030c30

def z116 : W := mkw 0x06fc97d4bf52fd25 0xe06fc97d4bf52fd2 0x8ffe1ff0ffc3fc3f 0x78ffe1ff0ffc3fc3

def z117 : W := mkw 0x01d1d50a343aa28c 0x001d1d50a343aa28 0xfff9ff0f3e3ff3cf 0xffff9ff0f3e3ff3c

def z118 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xfffe1ff0ffc3fc3f 0xffffe1ff0ffc3fc3

def z119 : W := mkw 0x02bc97c486124925 0x202bc97c48612492 0xffff9ffcee33cf3f 0xfffff9ffcee33cf3

def z120 : W := mkw 0x0bf7fd0a3028a288 0x00bf7fd0a3028a28 0xfbffff0f303cf3cb 0xffbffff0f303cf3c

def z121 : W := mkw 0x01c36d3b70edb6d8 0x901c36d3b70edb6d 0xf3c7fffff1ffffff 0xff3c7fffff1fffff

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0xf001860c2030c30b 0x9f001860c2030c30

def z123 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xfffffe0c3fffc30f 0xffffffe0c3fffc30

def z124 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xfbffffffd00c30cb 0xffbffffffd00c30c

def z125 : W := mkw 0x06ec07d03b68fe89 0xc06ec07d03b68fe8 0xbffe07f03ffcffcf 0x7bffe07f03ffcffc

def z126 : W := mkw 0x0000003140401450 0x9000000314040145 0x500001f3c0003cf9 0x0500001f3c0003cf

def z127 : W := mkw 0x204228003dbf000e 0x0204228003dbf000 0xa40678003fff0006 0xea40678003fff000

def z128 : W := mkw 0x0008028482004921 0x2000802848200492 0x5000068cc000cf39 0x05000068cc000cf3

def z129 : W := mkw 0x4bb7fd6b40000000 0x04bb7fd6b4000000 0x8bfff97300000000 0xf8bfff9730000000

def z130 : W := mkw 0x06fc97d4bf52fd25 0xe06fc97d4bf52fd2 0x8fff87fc3ff0ff0f 0x78fff87fc3ff0ff0

def z131 : W := mkw 0x4bbfffffc0c51450 0x94bbfffffc0c5145 0xfbffffffd1cf3cff 0xffbffffffd1cf3cf

def z132 : W := mkw 0x0181450a00000000 0x00181450a0000000 0xc3c1e70f00000001 0xbc3c1e70f0000000

def z133 : W := mkw 0x2b77f8217dbf005e 0x12b77f8217dbf005 0xfffff803ffff00f6 0xffffff803ffff00f

def z134 : W := mkw 0x204000003dbf000e 0x0204000003dbf000 0x240000003fff0006 0x0240000003fff000

def z135 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xffff87fc3ff0ff0f 0xfffff87fc3ff0ff0

def z136 : W := mkw 0x4a3ebae5c6124925 0x24a3ebae5c612492 0x0c3e18f0ce030c34 0x40c3e18f0ce030c3

def z137 : W := mkw 0x2a76b8003d970006 0x02a76b8003d97000 0x8ffe18003fc30006 0x78ffe18003fc3000

def z138 : W := mkw 0x0008028006124925 0x2000802800612492 0xbc3806802e33cf3f 0x5bc3806802e33cf3

def z139 : W := mkw 0x0040001030edb6d8 0x90040001030edb6d 0x3000000031fffffe 0x03000000031fffff

def z140 : W := mkw 0x4bbdd7ce80000000 0x04bbdd7ce8000000 0xcbf9e70f00000001 0xbcbf9e70f0000000

def z141 : W := mkw 0x0000001000401400 0x8000000100040140 0x800601f011c03c0f 0x6800601f011c03c0

def z142 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe01f01fc03c04 0x60ffe01f01fc03c0

def z143 : W := mkw 0x0000000006124925 0x2000000000612492 0x340000002e33cf3e 0x0340000002e33cf3

def z144 : W := mkw 0x0143683170ed1458 0x90143683170ed145 0xf3c7f9f3f1ff3cff 0xff3c7f9f3f1ff3cf

def z145 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0006103100c30cb 0xaf0006103100c30c

def z146 : W := mkw 0x4bfffffff0edb6d8 0x94bfffffff0edb6d 0xfbfffffff1ffffff 0xffbfffffff1fffff

def z147 : W := mkw 0x0018928480000000 0x0001892848000000 0xf8399e8ce030c30b 0xdf8399e8ce030c30

def z148 : W := mkw 0x408807efc000a280 0x0408807efc000a28 0x500007ffc000f3c9 0x0500007ffc000f3c

def z149 : W := mkw 0x04c807d03b40fc01 0xc04c807d03b40fc0 0x040007f03fc0fc0f 0x0040007f03fc0fc0

def z150 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x0006617311cc30c0 0x20006617311cc30c

def z151 : W := mkw 0x4bbfffffc0401400 0x84bbfffffc040140 0xcbffffffd1c03c0f 0xfcbffffffd1c03c0

def z152 : W := mkw 0x4bffffeff63aebad 0x24bffffeff63aeba 0xfffffffffe3fffff 0xffffffffffe3ffff

def z153 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x53c0670f100cf3c9 0x253c0670f100cf3c

def z154 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c3800002e000006 0x58c3800002e00000

def z155 : W := mkw 0x0224000009000000 0x0022400000900000 0x0c3e00000fc00004 0x40c3e00000fc0000

def z156 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x03c06103100c30c0 0x203c06103100c30c

def z157 : W := mkw 0x0266280039850000 0x0026628003985000 0xaffe78003fcf0006 0xfaffe78003fcf000

def z158 : W := mkw 0x4bbfffffc0401450 0x94bbfffffc040145 0xdbffffffc0003cf9 0xfdbffffffc0003cf

def z159 : W := mkw 0x004000003028a288 0x0004000003028a28 0x30000000303cf3ca 0x030000000303cf3c

def z160 : W := mkw 0x06ac07d00240fc01 0xc06ac07d00240fc0 0x8bfe07f00000fc09 0x78bfe07f00000fc0

def z161 : W := mkw 0x0002282140850050 0x1000228214085005 0x00001800c0030030 0x000001800c003003

def z162 : W := mkw 0x0010900484120124 0x2001090048412012 0x7001980cc0330330 0x87001980cc033033

def z163 : W := mkw 0x4bbfffefc4120124 0x24bbfffefc412012 0xfbffffffc0330331 0xffbffffffc033033

def z164 : W := mkw 0x06fc97d03f52fc05 0xc06fc97d03f52fc0 0xafff9ff03ff3fc0f 0xfafff9ff03ff3fc0

def z165 : W := mkw 0x0141400a30280288 0x00141400a3028028 0xf3c1e00f303c03c2 0xbf3c1e00f303c03c

def z166 : W := mkw 0x6bbfffefc4bf000e 0x06bbfffefc4bf000 0xebffffffc03f0001 0xfebffffffc03f000

def z167 : W := mkw 0x06e405503940b400 0xc06e405503940b40 0x03c6017011c03000 0x203c6017011c0300

def z168 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xc00679f3d1cc30c1 0xec00679f3d1cc30c

def z169 : W := mkw 0x4a26286140000000 0x04a2628614000000 0x0006007000000000 0x0000600700000000

def z170 : W := mkw 0x0000003140401450 0x9000000314040145 0x000000f0c0000c30 0x0000000f0c0000c3

def z171 : W := mkw 0x4bbdd7efc0000000 0x04bbdd7efc000000 0x4bf987ffc0000001 0x14bf987ffc000000

def z172 : W := mkw 0x0101400a00000000 0x00101400a0000000 0x4001e00f00000000 0x84001e00f0000000

def z173 : W := mkw 0x0141400a3028a288 0x00141400a3028a28 0x7001e00f303cf3ca 0x87001e00f303cf3c

def z174 : W := mkw 0x0018928486124925 0x2001892848612492 0x5c39868cee30cf39 0x15c39868cee30cf3

def z175 : W := mkw 0x049897d48652fd25 0xe049897d48652fd2 0xfc399ffcee33ff3f 0xdfc399ffcee33ff3

def z176 : W := mkw 0x4ba5454a00000000 0x04ba5454a0000000 0x03c0000000000000 0x003c000000000000

def z177 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc39ff8ffe3fffff 0xffc39ff8ffe3ffff

def z178 : W := mkw 0x0018928486124925 0x2001892848612492 0x8c381e80ee03cc3f 0x58c381e80ee03cc3

def z179 : W := mkw 0x244000103ffffc0f 0xc244000103ffffc0 0x240000003ffffc0e 0x0240000003ffffc0

def z180 : W := mkw 0x01d9d78eb63aebad 0x201d9d78eb63aeba 0x0ff9860c2e30c300 0x10ff9860c2e30c30

def z181 : W := mkw 0x4be76d6b7028a288 0x04be76d6b7028a28 0x03c66173100c30c0 0x203c66173100c30c

def z182 : W := mkw 0x408807ce80000000 0x0408807ce8000000 0x0000060c00000000 0x00000060c0000000

def z183 : W := mkw 0x6bbfffefcd970006 0x06bbfffefcd97000 0xcfffffffcfc30005 0xfcfffffffcfc3000

def z184 : W := mkw 0x226400003dbf000e 0x0226400003dbf000 0xaffe00003fff0006 0x7affe00003fff000

def z185 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c1ff8ff03fffff 0xff3c1ff8ff03ffff

def z186 : W := mkw 0x0000000000000000 0x0000000000000000 0x8006000011c00006 0x68006000011c0000

def z187 : W := mkw 0x2b75d0003d3a000e 0x02b75d0003d3a000 0x8fff80003ff00006 0x78fff80003ff0000

def z188 : W := mkw 0x2a36b8314dd71456 0x92a36b8314dd7145 0x0c3e18f0cfc30c34 0x40c3e18f0cfc30c3

def z189 : W := mkw 0x03e5450a3928a288 0x003e5450a3928a28 0xffffe70f3ffcf3cf 0xfffffe70f3ffcf3c

def z190 : W := mkw 0x014140003028a288 0x0014140003028a28 0xb3c1e000303cf3ca 0xbb3c1e000303cf3c

def z191 : W := mkw 0x0002280000850000 0x0000228000085000 0xa006780011cf0006 0xea006780011cf000

def z192 : W := mkw 0x048807d48240fd21 0xe048807d48240fd2 0x500007fcc000ff39 0x0500007fcc000ff3

def z193 : W := mkw 0x2812b80004970006 0x02812b8000497000 0x0000180000030000 0x0000018000003000

def z194 : W := mkw 0x0018928486124925 0x2001892848612492 0x0c399e8cee33cf34 0x50c399e8cee33cf3

def z195 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe07703fc0f000 0x30ffe07703fc0f00

def z196 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x0bf8060000000000 0x10bf806000000000

def z197 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x03c1e70f303cf3c0 0x303c1e70f303cf3c

def z198 : W := mkw 0x01d1d50eb43aa3ac 0x201d1d50eb43aa3a 0xf3c1ff0ff03ff3fb 0xbf3c1ff0ff03ff3f

def z199 : W := mkw 0x4ba76d7b40c51450 0x94ba76d7b40c5145 0xf3c679f3d1cf3cff 0xef3c679f3d1cf3cf

def z200 : W := mkw 0x42ac07efc0000000 0x042ac07efc000000 0xcbfe07ffc0000001 0x7cbfe07ffc000000

def z201 : W := mkw 0x0018928486124925 0x2001892848612492 0x0c39860c2e30c300 0x10c39860c2e30c30

def z202 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x0bff9efcc0000000 0x50bff9efcc000000

def z203 : W := mkw 0x4913f82fc4120124 0x24913f82fc412012 0x7001f80fc0330330 0x87001f80fc033033

def z204 : W := mkw 0x214140003dbf000e 0x0214140003dbf000 0xa7c1e0003fff0006 0xba7c1e0003fff000

def z205 : W := mkw 0x204000103dff145e 0x9204000103dff145 0x340000003fff3cfe 0x0340000003fff3cf

def z206 : W := mkw 0x4efebff5fb40fc01 0xc4efebff5fb40fc0 0x8ffe1ff0ffc0fc0f 0x78ffe1ff0ffc0fc0

def z207 : W := mkw 0x0000001000401400 0x8000000100040140 0x000001f000003c09 0x0000001f000003c0

def z208 : W := mkw 0x06ee2ff17bc5fc51 0xd06ee2ff17bc5fc5 0xfffe7ff3ffcffcff 0xffffe7ff3ffcffcf

def z209 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x800661f311cc3ccf 0x6800661f311cc3cc

def z210 : W := mkw 0x048807c00200e801 0x4048807c00200e80 0x000006000000c000 0x0000006000000c00

def z211 : W := mkw 0x0000001000c51450 0x90000001000c5145 0x0000000011cc30c0 0x00000000011cc30c

def z212 : W := mkw 0x408807efc2004921 0x2408807efc200492 0x500007ffc000cf39 0x0500007ffc000cf3

def z213 : W := mkw 0x044000103bc5fc51 0xd044000103bc5fc5 0x340000003fcffcfe 0x0340000003fcffcf

def z214 : W := mkw 0x4913f82fc0000000 0x04913f82fc000000 0xc007f9ffc0000001 0xec007f9ffc000000

def z215 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x33c1860c303cf3ca 0x133c1860c303cf3c

def z216 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xc3c1e70f2030c301 0xbc3c1e70f2030c30

def z217 : W := mkw 0x2b67680039ad000a 0x02b67680039ad000 0xa3c7e00031fc0002 0xba3c7e00031fc000

def z218 : W := mkw 0x4913f82fc0000000 0x04913f82fc000000 0x4001f80fc0000000 0x84001f80fc000000

def z219 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c06103100c30cb 0xaf3c06103100c30c

def z220 : W := mkw 0x2b75d0003d3a000e 0x02b75d0003d3a000 0xaff9e0003e3c0002 0xbaff9e0003e3c000

def z221 : W := mkw 0x0018928480000000 0x0001892848000000 0xf8399e8cc0030c3f 0xdf8399e8cc0030c3

def z222 : W := mkw 0x027490003d120004 0x0027490003d12000 0xafff98003ff30006 0xfafff98003ff3000

def z223 : W := mkw 0x0018928482004801 0x0001892848200480 0xcc399e8cee00cc0f 0xdcc399e8cee00cc0

def z224 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c1860c2030c30b 0x9f3c1860c2030c30

def z225 : W := mkw 0x0010900480000000 0x0001090048000000 0x4001980cc0000000 0x84001980cc000000

def z226 : W := mkw 0x03ad47ca00000000 0x003ad47ca0000000 0xcbffe7ff00000001 0xfcbffe7ff0000000

def z227 : W := mkw 0x2b75d0003dbf000e 0x02b75d0003dbf000 0x2ff980003fff0006 0x12ff980003fff000

def z228 : W := mkw 0x4baf6feb40000000 0x04baf6feb4000000 0x8bfe67f300000001 0x78bfe67f30000000

def z229 : W := mkw 0x0040000030000000 0x0004000003000000 0x83c0000030000002 0x383c000003000000

def z230 : W := mkw 0x0018928482004921 0x2001892848200492 0xd8399e8cc000cf39 0xdd8399e8cc000cf3

def z231 : W := mkw 0x21c1450a3dbfa28e 0x021c1450a3dbfa28 0xf7c1e70f3ffff3cf 0xbf7c1e70f3ffff3c

def z232 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x03c1860c2030c300 0x103c1860c2030c30

def z233 : W := mkw 0x06ec07c03b00e801 0x406ec07c03b00e80 0x8ffe07f02e00c001 0x78ffe07f02e00c00

def z234 : W := mkw 0x0018928486124925 0x2001892848612492 0x0c3800000e000000 0x00c3800000e00000

def z235 : W := mkw 0x6b77f82ffdbf000e 0x06b77f82ffdbf000 0xeffff80fffff0006 0xfeffff80fffff000

def z236 : W := mkw 0x6be76d6b79ad000a 0x06be76d6b79ad000 0x03c6617311cc0000 0x203c6617311cc000

def z237 : W := mkw 0x2bf7fd3b7dffb6de 0x92bf7fd3b7dffb6d 0xffffffffffffffff 0xffffffffffffffff

def z238 : W := mkw 0x0101400a00280288 0x00101400a0028028 0x00006003000c00c0 0x000006003000c00c

def z239 : W := mkw 0x04c807d03240fc01 0xc04c807d03240fc0 0x83c007f03000fc0b 0x383c007f03000fc0

def z240 : W := mkw 0x4bbdd7ce86124925 0x24bbdd7ce8612492 0x0ff9860c2e30c300 0x10ff9860c2e30c30

def z241 : W := mkw 0x0012b835c4d71574 0xb0012b835c4d7157 0xf007f9ffd1ff3fff 0xef007f9ffd1ff3ff

def z242 : W := mkw 0x06ec07d03940b400 0xc06ec07d03940b40 0x8bfe07f011c03001 0x78bfe07f011c0300

def z243 : W := mkw 0x0018928006124805 0x0001892800612480 0xac399e802e33cc0f 0xdac399e802e33cc0

def z244 : W := mkw 0x2913f80004bf000e 0x02913f80004bf000 0xa007f80011ff0006 0xea007f80011ff000

def z245 : W := mkw 0x0010900004120004 0x0001090000412000 0x2001980000330000 0x8200198000033000

def z246 : W := mkw 0x06e405503b40fc01 0xc06e405503b40fc0 0x07c601703fc0fc0e 0x207c601703fc0fc0

def z247 : W := mkw 0x2b67680039ad000a 0x02b67680039ad000 0xa3c6780011cf0006 0xea3c6780011cf000

def z248 : W := mkw 0x0010900486124925 0x2001090048612492 0x7401980cee33cf3e 0x87401980cee33cf3

def z249 : W := mkw 0x409897efc0000000 0x0409897efc000000 0xc8399fffc0000001 0xdc8399fffc000000

def z250 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x0bffe77f00000000 0x30bffe77f0000000

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0019e8ce033cf3f 0xdf0019e8ce033cf3

def z252 : W := mkw 0x2913f80004bf000e 0x02913f80004bf000 0xac39f8002e3f0006 0xdac39f8002e3f000

def z253 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xa3c1e103303c30c2 0xba3c1e103303c30c

def z254 : W := mkw 0x6bffffeff9ad000a 0x06bffffeff9ad000 0xcbffffffd1cc0001 0xfcbffffffd1cc000

def z255 : W := mkw 0x004000003028a288 0x0004000003028a28 0xf0006103303cf3cb 0xaf0006103303cf3c

def z256 : W := mkw 0x2b77f8003dbfa28e 0x02b77f8003dbfa28 0xbffff8003ffff3ce 0xfbffff8003ffff3c

def z257 : W := mkw 0x0b37f80004120004 0x00b37f8000412000 0xaffff8002e330006 0xfaffff8002e33000

def z258 : W := mkw 0x204000003d3a000e 0x0204000003d3a000 0x040000002e300000 0x0040000002e30000

def z259 : W := mkw 0x0008029002405c01 0x80008029002405c0 0x8c3e07f03fc0fc0f 0x78c3e07f03fc0fc0

def z260 : W := mkw 0x001abab5c6d75d75 0xb001abab5c6d75d7 0xfc3e79f3dfcf3cff 0xefc3e79f3dfcf3cf

def z261 : W := mkw 0x004000003028a288 0x0004000003028a28 0x000000002030c300 0x0000000002030c30

def z262 : W := mkw 0x048807f14240fc51 0xd048807f14240fc5 0x500007f3c000fcf9 0x0500007f3c000fcf

def z263 : W := mkw 0x01d9d78eb028a288 0x001d9d78eb028a28 0xfbf9ff8ff03cf3cb 0xffbf9ff8ff03cf3c

def z264 : W := mkw 0x4b3ffae5c0000000 0x04b3ffae5c000000 0x8bfff8f0c0000000 0xf8bfff8f0c000000

def z265 : W := mkw 0x02ac07d000401400 0x802ac07d00040140 0x8bfe07f011c03c0f 0x78bfe07f011c03c0

def z266 : W := mkw 0x001abab5c6d75d75 0xb001abab5c6d75d7 0xfc3f9efceff3cf3f 0xdfc3f9efceff3cf3

def z267 : W := mkw 0x0000003140401450 0x9000000314040145 0xd00601f3d1c03cff 0x6d00601f3d1c03cf

def z268 : W := mkw 0x001abab5c6d75d75 0xb001abab5c6d75d7 0x0c3e18f0cfc30c34 0x40c3e18f0cfc30c3

def z269 : W := mkw 0x0040000039000000 0x0004000003900000 0x040000003fc00006 0x0040000003fc0000

def z270 : W := mkw 0x044000103b68fe89 0xc044000103b68fe8 0x340000003ffcffce 0x0340000003ffcffc

def z271 : W := mkw 0x4bbfffefc000a280 0x04bbfffefc000a28 0xdbffffffc000f3c9 0xfdbffffffc000f3c

def z272 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x000679f3d1cf3cf4 0x6000679f3d1cf3cf

def z273 : W := mkw 0x0002283140401450 0x9000228314040145 0xd00679f3c0003cf9 0xed00679f3c0003cf

def z274 : W := mkw 0x4bbdd7ce80000000 0x04bbdd7ce8000000 0x8bff87fc00000001 0x78bff87fc0000000

def z275 : W := mkw 0x408a2fefc0000000 0x0408a2fefc000000 0xc0067fffc0000001 0xec0067fffc000000

def z276 : W := mkw 0x02a4054000000000 0x002a405400000000 0x03c6017000000000 0x203c601700000000

def z277 : W := mkw 0x6bfffffffdff145e 0x96bfffffffdff145 0xffffffffffff3cff 0xfffffffffffff3cf

def z278 : W := mkw 0x0000001000c51450 0x90000001000c5145 0xb00601f011cf3cff 0x6b00601f011cf3cf

def z279 : W := mkw 0x0000000000000000 0x0000000000000000 0x00006103100c30c0 0x200006103100c30c

def z280 : W := mkw 0x0008028002004801 0x0000802800200480 0x000006800000cc09 0x0000006800000cc0

def z281 : W := mkw 0x00589284b63aebad 0x200589284b63aeba 0xfc399e8cfe3fffff 0xdfc399e8cfe3ffff

def z282 : W := mkw 0x004000003000a000 0x0004000003000a00 0x000000003000f00a 0x0000000003000f00

def z283 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0007983d00f3cff 0xef0007983d00f3cf

def z284 : W := mkw 0x044802903b40fc01 0xc044802903b40fc0 0x8c3806803fc0fc0f 0x58c3806803fc0fc0

def z285 : W := mkw 0x6913f82fc4bf000e 0x06913f82fc4bf000 0x6001f80fc03f0000 0x86001f80fc03f000

def z286 : W := mkw 0x01c36d0a30ada288 0x001c36d0a30ada28 0xf3c7ff0f31fff3cf 0xff3c7ff0f31fff3c

def z287 : W := mkw 0x0008028482004921 0x2000802848200492 0xf001868ce030cf3b 0x9f001868ce030cf3

def z288 : W := mkw 0x4ffdd7cebb00e801 0x44ffdd7cebb00e80 0x0ff9860c2e00c000 0x10ff9860c2e00c00

def z289 : W := mkw 0x0018929486525d25 0xa0018929486525d2 0xfc3f9ffcfff3ff3f 0xffc3f9ffcfff3ff3

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0x5000060c0000c309 0x05000060c0000c30

def z291 : W := mkw 0x00c005003000a000 0x000c005003000a00 0x03c0010010003000 0x203c001001000300

def z292 : W := mkw 0x2fffffda3ffffe8f 0xc2fffffda3ffffe8 0xffffffff3fffffcf 0xfffffffff3fffffc

def z293 : W := mkw 0x0bbfffc000000000 0x00bbfffc00000000 0x8bfffff000000001 0xf8bfffff00000000

def z294 : W := mkw 0x41c947eff028a288 0x041c947eff028a28 0xf3c1e7fff03cf3cb 0xbf3c1e7fff03cf3c

def z295 : W := mkw 0x2913f82144bf005e 0x12913f82144bf005 0x7001f803c03f00f0 0x87001f803c03f00f

def z296 : W := mkw 0x0010900484120124 0x2001090048412012 0x00001800c0030030 0x000001800c003003

def z297 : W := mkw 0x026c02803b004801 0x0026c02803b00480 0x8ffe06803fc0cc0f 0x78ffe06803fc0cc0

def z298 : W := mkw 0x4903682b40000000 0x04903682b4000000 0x0000600300000000 0x0000060030000000

def z299 : W := mkw 0x0000001000401400 0x8000000100040140 0x0006017011c03000 0x20006017011c0300

def z300 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x0bfe79f3c0000000 0x60bfe79f3c000000

def z301 : W := mkw 0x01c1450a3000a000 0x001c1450a3000a00 0xc3c1e70f3000f00b 0xbc3c1e70f3000f00

def z302 : W := mkw 0x0624005009401400 0xc062400500940140 0x0006007001c00000 0x00006007001c0000

def z303 : W := mkw 0x2040000039ad000a 0x02040000039ad000 0x0000000011cc0000 0x00000000011cc000

def z304 : W := mkw 0x0365400039280008 0x0036540003928000 0xafffe0003ffc0006 0xfafffe0003ffc000

def z305 : W := mkw 0x4fbfffffcb405c01 0xc4fbfffffcb405c0 0xcfffffffcfc00c05 0xfcfffffffcfc00c0

def z306 : W := mkw 0x0018928486124925 0x2001892848612492 0x8c39868c2e30cf0f 0x58c39868c2e30cf0

def z307 : W := mkw 0x2b37f8000dbf000e 0x02b37f8000dbf000 0x2c3ff8000fff0004 0xc2c3ff8000fff000

def z308 : W := mkw 0x4a3ebae5c0000000 0x04a3ebae5c000000 0x083e18f0c0000000 0x4083e18f0c000000

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0006000100c0002 0xaa0006000100c000

def z310 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xa00678f0d1cf0c36 0xea00678f0d1cf0c3

def z311 : W := mkw 0x06ee2fd03bc5fc01 0xc06ee2fd03bc5fc0 0xaffe7ff03fcffc0f 0xfaffe7ff03fcffc0

def z312 : W := mkw 0x4bffffeff028a288 0x04bffffeff028a28 0xcbffffffd00c30c1 0xfcbffffffd00c30c

def z313 : W := mkw 0x062c02d00b405c01 0xc062c02d00b405c0 0x8c3e01f01fc03c0f 0x68c3e01f01fc03c0

def z314 : W := mkw 0x0098978e8612eba5 0x20098978e8612eba 0xfc399f8fee33ffff 0xdfc399f8fee33fff

def z315 : W := mkw 0x0fffffd03b40fc01 0xc0fffffd03b40fc0 0x8ffffff03fc0fc0f 0xf8ffffff03fc0fc0

def z316 : W := mkw 0x4bbfffefc0280288 0x04bbfffefc028028 0xfbffffffc03c03c1 0xffbffffffc03c03c

def z317 : W := mkw 0x0000003140401450 0x9000000314040145 0x00000173000030c0 0x000000173000030c

def z318 : W := mkw 0x4a3ebae5c0000000 0x04a3ebae5c000000 0xc83f9efcc0000001 0xdc83f9efcc000000

def z319 : W := mkw 0x4fffffffff52fd25 0xe4fffffffff52fd2 0xfffffffffff3ff3f 0xffffffffffff3ff3

def z320 : W := mkw 0x204000003fbf492f 0x2204000003fbf492 0x340000003fffcf3e 0x0340000003fffcf3

def z321 : W := mkw 0x0181450a00280288 0x00181450a0028028 0xf3c1e70f003c03c1 0xbf3c1e70f003c03c

def z322 : W := mkw 0x0000001000c51450 0x90000001000c5145 0x0000000001c30c34 0x00000000001c30c3

def z323 : W := mkw 0x49d3fd2ff028a288 0x049d3fd2ff028a28 0xf3c1ff0ff03cf3cb 0xbf3c1ff0ff03cf3c

def z324 : W := mkw 0x01836d2b40000000 0x001836d2b4000000 0xc3c7ffffc0000001 0xfc3c7ffffc000000

def z325 : W := mkw 0x2b77f8217dbf000e 0x02b77f8217dbf000 0xeffff9f3ffff0007 0xfeffff9f3ffff000

def z326 : W := mkw 0x06e405503940b400 0xc06e405503940b40 0x8ffe01703fc03006 0x78ffe01703fc0300

def z327 : W := mkw 0x2b7ffa84bdbf000e 0x02b7ffa84bdbf000 0xeffffe8cffff0007 0xfeffffe8cffff000

def z328 : W := mkw 0x4bbdd7ce80000000 0x04bbdd7ce8000000 0xcbf99e8cc0000001 0xdcbf99e8cc000000

def z329 : W := mkw 0x0159d284b63a492d 0x20159d284b63a492 0xfff9fe8cfe3fcf3f 0xffff9fe8cfe3fcf3

def z330 : W := mkw 0x2b67680039ad000a 0x02b67680039ad000 0x8ffe60003fcc0006 0x78ffe60003fcc000

def z331 : W := mkw 0x0000000006124925 0x2000000000612492 0x040000002e30c300 0x0040000002e30c30

def z332 : W := mkw 0x022c02c000000000 0x0022c02c00000000 0x083e00f000000000 0x4083e00f00000000

def z333 : W := mkw 0x0000000006124925 0x2000000000612492 0xf4001880ee33cf3f 0xcf4001880ee33cf3

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x800006002000c00b 0x1800006002000c00

def z335 : W := mkw 0x0012b83144d71454 0x90012b83144d7145 0xfc3ff9f3ffff3cff 0xffc3ff9f3ffff3cf

def z336 : W := mkw 0x0266283179c51450 0x90266283179c5145 0xfffe79f3ffcf3cff 0xffffe79f3ffcf3cf

def z337 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc381880ce030c3f 0xcfc381880ce030c3

def z338 : W := mkw 0x2b77f804bdbf012e 0x22b77f804bdbf012 0xfffff80cffff0336 0xffffff80cffff033

def z339 : W := mkw 0x0b37f80000850000 0x00b37f8000085000 0xabfff80011cf0006 0xfabfff80011cf000

def z340 : W := mkw 0x2bf7fd0a3dbfa28e 0x02bf7fd0a3dbfa28 0xaffffe0c3fffc306 0xfaffffe0c3fffc30

def z341 : W := mkw 0x0018928486124925 0x2001892848612492 0x7c399e0cee33c330 0x97c399e0cee33c33

def z342 : W := mkw 0x0002281000c51400 0x80002281000c5140 0xa00679f011cf3c0f 0xea00679f011cf3c0

def z343 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe06f02fc0cc04 0x50ffe06f02fc0cc0

def z344 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000180000030006 0xca00018000003000

def z345 : W := mkw 0x0101400a00280288 0x00101400a0028028 0xf001e60f203cc3cb 0x9f001e60f203cc3c

def z346 : W := mkw 0x2913f80484bf012e 0x22913f80484bf012 0x7001f80cc03f0330 0x87001f80cc03f033

def z347 : W := mkw 0x4a3ebaf5c0c51450 0x94a3ebaf5c0c5145 0x083e18f0c1c30c34 0x4083e18f0c1c30c3

def z348 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0xc3c679f3c0000001 0xec3c679f3c000000

def z349 : W := mkw 0x00822d3b40c5b6d0 0x900822d3b40c5b6d 0xf0067fffd1cfffff 0xef0067fffd1cffff

def z350 : W := mkw 0x2000000004bf000e 0x02000000004bf000 0x20000000003f0000 0x020000000003f000

def z351 : W := mkw 0x000802b5c2405d71 0xb000802b5c2405d7 0x500007ffc000fff9 0x0500007ffc000fff

def z352 : W := mkw 0x01d9d78eb63aebad 0x201d9d78eb63aeba 0xfff9e70f3e3cf3cb 0xbfff9e70f3e3cf3c

def z353 : W := mkw 0x00c005103040b400 0x800c005103040b40 0x83c607f031c0fc0f 0x783c607f031c0fc0

def z354 : W := mkw 0x0101400000000000 0x0010140000000000 0x83c1e00000000000 0xb83c1e0000000000

def z355 : W := mkw 0x03ed47ca3028a288 0x003ed47ca3028a28 0xfbffe7ff303cf3cb 0xffbffe7ff303cf3c

def z356 : W := mkw 0x2911d000043a000e 0x02911d000043a000 0x0001800000300000 0x0000180000030000

def z357 : W := mkw 0x2b6540003928000a 0x02b6540003928000 0x03c0000000000000 0x003c000000000000

def z358 : W := mkw 0x0008028002004801 0x0000802800200480 0x0c3800800e000c04 0x40c3800800e000c0

def z359 : W := mkw 0x2a36b8000d970006 0x02a36b8000d97000 0xac3f98002ff30006 0xdac3f98002ff3000

def z360 : W := mkw 0x06ec07c03b00e801 0x406ec07c03b00e80 0x8ff807003e00f00b 0x38ff807003e00f00

def z361 : W := mkw 0x400802e5c0000000 0x0400802e5c000000 0x000000f0c0000000 0x0000000f0c000000

def z362 : W := mkw 0x2e3ebad00fd75c07 0xc2e3ebad00fd75c0 0x0c3e18f00fc30c04 0x40c3e18f00fc30c0

def z363 : W := mkw 0x4fef6ffb7b40fc01 0xc4fef6ffb7b40fc0 0x8ffe67f33fc0fc0f 0x78ffe67f33fc0fc0

def z364 : W := mkw 0x0199d78e86124925 0x20199d78e8612492 0xfff9ff8fee33cf3f 0xffff9ff8fee33cf3

def z365 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x83c06703300cf0cb 0x383c06703300cf0c

def z366 : W := mkw 0x063c92d48f525d25 0xe063c92d48f525d2 0xfc3f9efceff3cf3f 0xdfc3f9efceff3cf3

def z367 : W := mkw 0x0000000480000120 0x2000000048000012 0x5000000cc0000330 0x05000000cc000033

def z368 : W := mkw 0x2b7ffa803fbf480f 0x02b7ffa803fbf480 0xaffffe803fffcc0f 0xfaffffe803fffcc0

def z369 : W := mkw 0x0b27680000000000 0x00b2768000000000 0x03c6600000000000 0x203c660000000000

def z370 : W := mkw 0x00400000363aebad 0x200400000363aeba 0x340000003e3ffffe 0x0340000003e3ffff

def z371 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x840601f03fc0fc0f 0x6840601f03fc0fc0

def z372 : W := mkw 0x0111d00e843a03ac 0x20111d00e843a03a 0x7001f80fc03f03f0 0x87001f80fc03f03f

def z373 : W := mkw 0x00c22d3170c5b450 0x900c22d3170c5b45 0xf3c67ff3f1cffcff 0xff3c67ff3f1cffcf

def z374 : W := mkw 0x2b37f80004bf000e 0x02b37f80004bf000 0xabfff800003f0000 0xfabfff800003f000

def z375 : W := mkw 0x0002282140000000 0x0000228214000000 0x000618f0c0000000 0x4000618f0c000000

def z376 : W := mkw 0x0181450a00000000 0x00181450a0000000 0x03c1860c00000000 0x103c1860c0000000

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0x300000002030c30a 0x0300000002030c30

def z378 : W := mkw 0x204228317dff145e 0x9204228317dff145 0xf40679f3ffff3cff 0xef40679f3ffff3cf

def z379 : W := mkw 0x0002282140850050 0x1000228214085005 0xf0007903d00f30fb 0xaf0007903d00f30f

def z380 : W := mkw 0x01d9d78eb63aebad 0x201d9d78eb63aeba 0xfff99e8cee33cf3f 0xdfff99e8cee33cf3

def z381 : W := mkw 0x2a36b8000d970006 0x02a36b8000d97000 0xac3e78001fcf0006 0xeac3e78001fcf000

def z382 : W := mkw 0x4812b825c0000000 0x04812b825c000000 0x00001800c0000000 0x000001800c000000

def z383 : W := mkw 0x0000003140401450 0x9000000314040145 0xf00061f3d00c3cfb 0xaf00061f3d00c3cf

def z384 : W := mkw 0x2ffffff17ffffc5f 0xd2ffffff17ffffc5 0xfffffff3fffffcff 0xffffffff3fffffcf

def z385 : W := mkw 0x4bffffeff000a000 0x04bffffeff000a00 0xcbfffffff000f00b 0xfcbfffffff000f00

def z386 : W := mkw 0x4ffffffffb68fe89 0xc4ffffffffb68fe8 0xfffffffffffcffcf 0xffffffffffffcffc

def z387 : W := mkw 0x00c0050a3028a288 0x000c0050a3028a28 0x7000070f303cf3cb 0x07000070f303cf3c

def z388 : W := mkw 0x2b77f8003d3a000e 0x02b77f8003d3a000 0x8ffff8002e300000 0xf8ffff8002e30000

def z389 : W := mkw 0x0002282140850050 0x1000228214085005 0xf00679f3c00f00f1 0xef00679f3c00f00f

def z390 : W := mkw 0x2b7ffa84bfbf492f 0x22b7ffa84bfbf492 0xaffff880ffff0c36 0xfaffff880ffff0c3

def z391 : W := mkw 0x0264000039000000 0x0026400003900000 0x03c6000011c00000 0x203c6000011c0000

def z392 : W := mkw 0x00c005003000a000 0x000c005003000a00 0xf3c1870c3030f30b 0xbf3c1870c3030f30

def z393 : W := mkw 0x0264000039000000 0x0026400003900000 0x0ff800002e000000 0x10ff800002e00000

def z394 : W := mkw 0x0018928486124925 0x2001892848612492 0xac399880ee330c36 0xdac399880ee330c3

def z395 : W := mkw 0x0000001000401400 0x8000000100040140 0xf00619f0d1c33c3f 0xef00619f0d1c33c3

def z396 : W := mkw 0x0002282140000000 0x0000228214000000 0xf00679f3c0030c3f 0xef00679f3c0030c3

def z397 : W := mkw 0x2b77f8103dff145e 0x92b77f8103dff145 0xbffff8003fff3cfe 0xfbffff8003fff3cf

def z398 : W := mkw 0x0018929486d75d75 0xb0018929486d75d7 0xfc399e8cffffffff 0xdfc399e8cfffffff

def z399 : W := mkw 0x4bbfffffc6d75d75 0xb4bbfffffc6d75d7 0xffffffffffffffff 0xffffffffffffffff

def z400 : W := mkw 0x0010900484120124 0x2001090048412012 0x0001800c00300300 0x00001800c0030030

def z401 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xa3c1e60c303cc302 0xba3c1e60c303cc30

def z402 : W := mkw 0x027c9284bf124925 0x2027c9284bf12492 0xffff9e8cfff3cf3f 0xfffff9e8cfff3cf3

def z403 : W := mkw 0x4fffffeffb00e801 0x44fffffeffb00e80 0xcfffffffee00c001 0xfcfffffffee00c00

def z404 : W := mkw 0x4ba76d7b40c51450 0x94ba76d7b40c5145 0x03c6617311cc30c0 0x203c6617311cc30c

def z405 : W := mkw 0x0018928480000000 0x0001892848000000 0x08381880c0000000 0x408381880c000000

def z406 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x70007803d1cf3cfe 0x870007803d1cf3cf

def z407 : W := mkw 0x06e62d7179c5b450 0xd06e62d7179c5b45 0x03c6617311cc30c0 0x203c6617311cc30c

def z408 : W := mkw 0x0000002140000000 0x0000000214000000 0x400001f3c0000001 0x0400001f3c000000

def z409 : W := mkw 0x0000003140401450 0x9000000314040145 0xf00019f3c0033cff 0xcf00019f3c0033cf

def z410 : W := mkw 0x0002282140000000 0x0000228214000000 0x0006617300000000 0x2000661730000000

def z411 : W := mkw 0x07ed47ca3b28ea89 0x407ed47ca3b28ea8 0x0ff9860c2e30c300 0x10ff9860c2e30c30

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0x70006003000c00c0 0x870006003000c00c

def z413 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x700678f3c1cf0cf4 0xc700678f3c1cf0cf

def z414 : W := mkw 0x06e405503940b400 0xc06e405503940b40 0x83c601f011c03c0f 0x683c601f011c03c0

def z415 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0xc3c7e77f00000001 0xbc3c7e77f0000000

def z416 : W := mkw 0x2b77f8003fbf492f 0x22b77f8003fbf492 0xbffff8003fffcf3e 0xfbffff8003fffcf3

def z417 : W := mkw 0x499bffefc0000000 0x0499bffefc000000 0x4001ffffc0000001 0x84001ffffc000000

def z418 : W := mkw 0x2be76d0a39ada28a 0x02be76d0a39ada28 0x03c6610311cc30c0 0x203c6610311cc30c

def z419 : W := mkw 0x2b6768003dbf000e 0x02b6768003dbf000 0x27c660003fff0006 0x227c660003fff000

def z420 : W := mkw 0x000a2ab5c2c55d71 0xb000a2ab5c2c55d7 0xf0067fffd1cfffff 0xef0067fffd1cffff

def z421 : W := mkw 0x004000003028a288 0x0004000003028a28 0x00000000100c30c0 0x000000000100c30c

def z422 : W := mkw 0x0018928486124925 0x2001892848612492 0x3c381880ee33cf3e 0x43c381880ee33cf3

def z423 : W := mkw 0x4a3ebaf5c0c51450 0x94a3ebaf5c0c5145 0xf83e79f3d1cf3cff 0xef83e79f3d1cf3cf

def z424 : W := mkw 0x4fbfffffc240fc01 0xc4fbfffffc240fc0 0xcbffffffc000fc09 0xfcbffffffc000fc0

def z425 : W := mkw 0x2a76b8003dbf000e 0x02a76b8003dbf000 0x2c3e18003fff0006 0x42c3e18003fff000

def z426 : W := mkw 0x040000100b405c01 0xc040000100b405c0 0x040000000fc00c04 0x0040000000fc00c0

def z427 : W := mkw 0x0002283140401400 0x8000228314040140 0xc00679f3d1c03c0f 0xec00679f3d1c03c0

def z428 : W := mkw 0x4fe76d7b7940b400 0xc4fe76d7b7940b40 0x03c6617311c03000 0x203c6617311c0300

def z429 : W := mkw 0x02ec07c039000000 0x002ec07c03900000 0x8ffe07f03fc00007 0x78ffe07f03fc0000

def z430 : W := mkw 0x062e2af14bc55c51 0xd062e2af14bc55c5 0x0c3e18f0cfc30c34 0x40c3e18f0cfc30c3

def z431 : W := mkw 0x0000001000c51450 0x90000001000c5145 0xf0001880d1cf3cff 0xcf0001880d1cf3cf

def z432 : W := mkw 0x02e405003900a000 0x002e405003900a00 0x8ffe07003fc0f00f 0x78ffe07003fc0f00

def z433 : W := mkw 0x066c02d03b405c01 0xc066c02d03b405c0 0x8ffe00f03fc00c06 0x78ffe00f03fc00c0

def z434 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xa006797311cf30c6 0xea006797311cf30c

def z435 : W := mkw 0x2ffdd7d03f7afc0f 0xc2ffdd7d03f7afc0 0x8fff87f03ff0fc0f 0x78fff87f03ff0fc0

def z436 : W := mkw 0x0000001000401450 0x9000000100040145 0x1000000000003cf8 0x01000000000003cf

def z437 : W := mkw 0x4ffffffff940b400 0xc4ffffffff940b40 0xcbffffffd1c03001 0xfcbffffffd1c0300

def z438 : W := mkw 0x06ec07d03f52fd25 0xe06ec07d03f52fd2 0xbffe07f03ff3ff3f 0x7bffe07f03ff3ff3

def z439 : W := mkw 0x001892b5c6525d75 0xb001892b5c6525d7 0xfc399fffee33ffff 0xdfc399fffee33fff

def z440 : W := mkw 0x008005000000a000 0x0008005000000a00 0x000007000000f009 0x0000007000000f00

def z441 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ff806003fc0fc0e 0x10ff806003fc0fc0

def z442 : W := mkw 0x46ec07fffb40fc01 0xc46ec07fffb40fc0 0xcffe07ffffc0fc0f 0x7cffe07ffffc0fc0

def z443 : W := mkw 0x0000000000000000 0x0000000000000000 0xf001e70f303cf3cb 0xbf001e70f303cf3c

def z444 : W := mkw 0x0143680030ad0008 0x00143680030ad000 0xa3c7f80031ff0006 0xfa3c7f80031ff000

def z445 : W := mkw 0x0080053b4040b6d0 0x90080053b4040b6d 0x500007ffc000fff9 0x0500007ffc000fff

def z446 : W := mkw 0x6bffffeffdbfa28e 0x06bffffeffdbfa28 0xfffffffffffff3cf 0xffffffffffffff3c

def z447 : W := mkw 0x2b77f8103dff140e 0x82b77f8103dff140 0xaffff9f03fff3c0f 0xfaffff9f03fff3c0

def z448 : W := mkw 0x2b77f80039ad000a 0x02b77f80039ad000 0x8bfff80011cc0000 0xf8bfff80011cc000

def z449 : W := mkw 0x07ed47d03b68fc09 0xc07ed47d03b68fc0 0xafffe7f03ffcfc0f 0xfafffe7f03ffcfc0

def z450 : W := mkw 0x0181450a00000000 0x00181450a0000000 0xf3c1e70f100c30cb 0xbf3c1e70f100c30c

def z451 : W := mkw 0x2913f83144ff145e 0x92913f83144ff145 0xf007f9f3d1ff3cff 0xef007f9f3d1ff3cf

def z452 : W := mkw 0x2b67683179ed145a 0x92b67683179ed145 0xf3c679f3d1cf3cff 0xef3c679f3d1cf3cf

def z453 : W := mkw 0x2bf7fd003dbfa00e 0x02bf7fd003dbfa00 0xafffff003ffff00f 0xfafffff003ffff00

def z454 : W := mkw 0x2f7ffad03fff5c0f 0xc2f7ffad03fff5c0 0xaffff8f03fff0c06 0xfaffff8f03fff0c0

def z455 : W := mkw 0x0012b80004970004 0x00012b8000497000 0xac3ff8003fff0006 0xfac3ff8003fff000

def z456 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x4bf9fe0fc0000000 0x94bf9fe0fc000000

def z457 : W := mkw 0x0000000002004921 0x2000000000200492 0x100000000000cf38 0x0100000000000cf3

def z458 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xfbffffffe030c30b 0xffbffffffe030c30

def z459 : W := mkw 0x01c36d3b70edb6d8 0x901c36d3b70edb6d 0xf3c7e77f31fcf3cb 0xbf3c7e77f31fcf3c

def z460 : W := mkw 0x2fffffc03fbfe80f 0x42fffffc03fbfe80 0xaffffe003fffc006 0xfaffffe003fffc00

def z461 : W := mkw 0x4ffdd7debb40fc01 0xc4ffdd7debb40fc0 0x8fff87fc3fc0fc0f 0x78fff87fc3fc0fc0

def z462 : W := mkw 0x2903680000ad000a 0x02903680000ad000 0x00006000000c0000 0x000006000000c000

def z463 : W := mkw 0x01c1450a363aebad 0x201c1450a363aeba 0xf7c1e70f3e3fffff 0xbf7c1e70f3e3ffff

def z464 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x0ffe78001fcf0004 0x60ffe78001fcf000

def z465 : W := mkw 0x0a36b80000000000 0x00a36b8000000000 0x083e180000000000 0x4083e18000000000

def z466 : W := mkw 0x0000000000000000 0x0000000000000000 0xc001860c00000001 0x9c001860c0000000

def z467 : W := mkw 0x044000103940b400 0xc044000103940b40 0x0000000011c03000 0x00000000011c0300

def z468 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xcfffffffee30c301 0xfcfffffffee30c30

def z469 : W := mkw 0x06fc97c4bf12e925 0x606fc97c4bf12e92 0xfff99e8cee33cf3f 0xdfff99e8cee33cf3

def z470 : W := mkw 0x0010900004120004 0x0001090000412000 0x0c3980002e300000 0x10c3980002e30000

def z471 : W := mkw 0x01c9478eb228eba9 0x201c9478eb228eba 0xf3c1e78ff03cfffb 0xbf3c1e78ff03cfff

def z472 : W := mkw 0x0088078e8200eba1 0x20088078e8200eba 0x5000078fc000fff9 0x05000078fc000fff

def z473 : W := mkw 0x0010900484120124 0x2001090048412012 0xf001988cc0330f3f 0xcf001988cc0330f3

def z474 : W := mkw 0x4bbfffefc4120004 0x04bbfffefc412000 0xefffffffee330007 0xfefffffffee33000

def z475 : W := mkw 0x6bf7fd6b7dbf000e 0x06bf7fd6b7dbf000 0xaffff9733fff0006 0xfaffff9733fff000

def z476 : W := mkw 0x001abab5c0c51450 0x9001abab5c0c5145 0xf83fffffd1cf3cff 0xff83fffffd1cf3cf

def z477 : W := mkw 0x0913f80000000000 0x00913f8000000000 0x0001f80000000000 0x80001f8000000000

def z478 : W := mkw 0x0002280000850000 0x0000228000085000 0x0006180001c30004 0x40006180001c3000

def z479 : W := mkw 0x4000002fc0000000 0x04000002fc000000 0x4000000fc0000000 0x04000000fc000000

def z480 : W := mkw 0x2b7dd284bf3a492f 0x22b7dd284bf3a492 0xfff99e8cee33cf3f 0xdfff99e8cee33cf3

def z481 : W := mkw 0x048a2ff142c5fc51 0xd048a2ff142c5fc5 0xf0067ff3d1cffcff 0xef0067ff3d1cffcf

def z482 : W := mkw 0x000a2ab142c55c51 0x9000a2ab142c55c5 0xfc3e7ff3ffcffcff 0xffc3e7ff3ffcffcf

def z483 : W := mkw 0x2fef6fd03bedfc0b 0xc2fef6fd03bedfc0 0x8ffe67f03fccfc0f 0x78ffe67f03fccfc0

def z484 : W := mkw 0x0000001000c51450 0x90000001000c5145 0xf000610311cf3cff 0xaf000610311cf3cf

def z485 : W := mkw 0x05c1451a3b68fe89 0xc05c1451a3b68fe8 0xf7c1e70f3ffcffcf 0xbf7c1e70f3ffcffc

def z486 : W := mkw 0x063c92d48f525d25 0xe063c92d48f525d2 0x0c3e18f0cfc30c34 0x40c3e18f0cfc30c3

def z487 : W := mkw 0x048807da0240fe81 0xc048807da0240fe8 0x500007ff0000ffc9 0x0500007ff0000ffc

def z488 : W := mkw 0x07e5455a3968b688 0xc07e5455a3968b68 0xf3c7e77f31fcf3cb 0xbf3c7e77f31fcf3c

def z489 : W := mkw 0x2b77f8317dff145e 0x92b77f8317dff145 0xaffff8f0ffff0c36 0xfaffff8f0ffff0c3

def z490 : W := mkw 0x0151d000343a000c 0x00151d000343a000 0xaff9f8003e3f0006 0xfaff9f8003e3f000

def z491 : W := mkw 0x07e5455a3968b688 0xc07e5455a3968b68 0x03c6617311cc30c0 0x203c6617311cc30c

def z492 : W := mkw 0x0008028482004921 0x2000802848200492 0x00000080c0000c30 0x000000080c0000c3

def z493 : W := mkw 0x491bfaafc0000000 0x0491bfaafc000000 0xc839fe8fc0000001 0xdc839fe8fc000000

def z494 : W := mkw 0x06fc97d4bb40fc01 0xc06fc97d4bb40fc0 0xcfff9ffcffc0fc0f 0xfcfff9ffcffc0fc0

def z495 : W := mkw 0x2bf5d50a3d3aa28e 0x02bf5d50a3d3aa28 0x0ff9860c2e30c300 0x10ff9860c2e30c30

def z496 : W := mkw 0x07ef6ffb7bedfed9 0xd07ef6ffb7bedfed 0xffffffffffffffff 0xffffffffffffffff

def z497 : W := mkw 0x0b37f82140000000 0x00b37f8214000000 0xcbfff9f3c0000001 0xfcbfff9f3c000000

def z498 : W := mkw 0x4bbfffce80000000 0x04bbfffce8000000 0x8bfffe0c00000000 0xf8bfffe0c0000000

def z499 : W := mkw 0x0000000000000000 0x0000000000000000 0x7001800c00300300 0x87001800c0030030

def z500 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x700079f3c00f3cf9 0x8700079f3c00f3cf

def z501 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xfffff880ffff0c3f 0xffffff880ffff0c3

def z502 : W := mkw 0x01c36d3b70edb6d8 0x901c36d3b70edb6d 0x03c6617311cc30c0 0x203c6617311cc30c

def z503 : W := mkw 0x0b35d00000000000 0x00b35d0000000000 0x0bf9800000000000 0x10bf980000000000

def z504 : W := mkw 0x0000000a00000280 0x00000000a0000028 0x5000000f000003c0 0x05000000f000003c

def z505 : W := mkw 0x0080050a00000000 0x00080050a0000000 0x4000070f00000001 0x04000070f0000000

def z506 : W := mkw 0x0000001000401400 0x8000000100040140 0x0000000011c03c0e 0x00000000011c03c0

def z507 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x800607f011c0fc0f 0x6800607f011c0fc0

def z508 : W := mkw 0x4bbfffefc2004921 0x24bbfffefc200492 0xdbffffffc000cf39 0xfdbffffffc000cf3

def z509 : W := mkw 0x0042283170edb6d8 0x90042283170edb6d 0xf00679f3f1ffffff 0xef00679f3f1fffff

def z510 : W := mkw 0x4bbfffefc0850000 0x04bbfffefc085000 0xebffffffd1cf0007 0xfebffffffd1cf000

def z511 : W := mkw 0x0002282140850000 0x0000228214085000 0xe00679f3d1cf0007 0xee00679f3d1cf000

def z512 : W := mkw 0x0101400a00280288 0x00101400a0028028 0x0001800c00300300 0x00001800c0030030

def z513 : W := mkw 0x01c9478a3228ea89 0x001c9478a3228ea8 0xfff9e78f3e3cffcf 0xffff9e78f3e3cffc

def z514 : W := mkw 0x0010900000000000 0x0001090000000000 0x8839980000000000 0xd883998000000000

def z515 : W := mkw 0x06ec07f17b40fc51 0xd06ec07f17b40fc5 0xdffe07f3ffc0fcff 0x7dffe07f3ffc0fcf

def z516 : W := mkw 0x6bffffcebdbf000e 0x06bffffcebdbf000 0xaffffe0c3fff0006 0xfaffffe0c3fff000

def z517 : W := mkw 0x2b37f8000d970006 0x02b37f8000d97000 0x8ffff8000fc30004 0xf8ffff8000fc3000

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000080c0000c39 0x050000080c0000c3

def z519 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x73c1e60f203cc3c0 0x973c1e60f203cc3c

def z520 : W := mkw 0x00c005003028a288 0x000c005003028a28 0xb3c00700303cf3cb 0x3b3c00700303cf3c

def z521 : W := mkw 0x0b37f83140c51450 0x90b37f83140c5145 0xfbfff9f3d1cf3cff 0xffbfff9f3d1cf3cf

def z522 : W := mkw 0x2fffffd4bffffd2f 0xe2fffffd4bffffd2 0xfffffffcffffff3f 0xffffffffcffffff3

def z523 : W := mkw 0x044228317bc5fc51 0xd044228317bc5fc5 0xf40679f3ffcffcff 0xef40679f3ffcffcf

def z524 : W := mkw 0x0199d78e80000000 0x00199d78e8000000 0xcbf9ff8fc0000001 0xfcbf9ff8fc000000

def z525 : W := mkw 0x02ae2ff140c51450 0x902ae2ff140c5145 0xfbfe7ff3d1cf3cff 0xffbfe7ff3d1cf3cf

def z526 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xf007fffff1ffffff 0xff007fffff1fffff

def z527 : W := mkw 0x0018928486124925 0x2001892848612492 0x70019e8cc033cf39 0x870019e8cc033cf3

def z528 : W := mkw 0x0000000000850050 0x1000000000085005 0x30000000000f00f0 0x030000000000f00f

def z529 : W := mkw 0x0018928486124925 0x2001892848612492 0xac399e0c2e33c306 0xdac399e0c2e33c30

def z530 : W := mkw 0x008807c000000000 0x0008807c00000000 0x000007f000000001 0x0000007f00000000

def z531 : W := mkw 0x0010900006124925 0x2001090000612492 0xbc3998002e33cf3e 0xdbc3998002e33cf3

def z532 : W := mkw 0x0000000004120004 0x0000000000412000 0x240000002e330006 0x0240000002e33000

def z533 : W := mkw 0x0103682b40ad02d8 0x10103682b40ad02d 0x7001f80fc03f03f0 0x87001f80fc03f03f

def z534 : W := mkw 0x02ae2fe140000000 0x002ae2fe14000000 0xcbfe7ff3c0000001 0xfcbfe7ff3c000000

def z535 : W := mkw 0x06e405503940b400 0xc06e405503940b40 0x83c6077031c0f00b 0x383c6077031c0f00

def z536 : W := mkw 0x200000000d970006 0x0200000000d97000 0x040000000fc30004 0x0040000000fc3000

def z537 : W := mkw 0x0141400030280008 0x0014140003028000 0x03c1800020300000 0x103c180002030000

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0x800001001000300b 0x2800001001000300

def z539 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x800619f0d1c33c3f 0x6800619f0d1c33c3

def z540 : W := mkw 0x0002280000850000 0x0000228000085000 0x0006600011cc0000 0x20006600011cc000

def z541 : W := mkw 0x2ff7fd503dffb40e 0xc2ff7fd503dffb40 0xaffff9703fff3006 0xfaffff9703fff300

def z542 : W := mkw 0x0002281000c51450 0x90002281000c5145 0xb006780011cf3cfe 0xeb006780011cf3cf

def z543 : W := mkw 0x2a26280009850002 0x02a2628000985000 0x0006000001c00000 0x00006000001c0000

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x800601f000000001 0x6800601f00000000

def z545 : W := mkw 0x4ffffffffbc5fc51 0xd4ffffffffbc5fc5 0xffffffffffcffcff 0xfffffffffffcffcf

def z546 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x03c607f011c0fc09 0x203c607f011c0fc0

def z547 : W := mkw 0x0b3ffa8486124925 0x20b3ffa848612492 0xfffffe8cee33cf3f 0xffffffe8cee33cf3

def z548 : W := mkw 0x0018928484120004 0x0001892848412000 0xec399e8cee330007 0xdec399e8cee33000

def z549 : W := mkw 0x2a3490000d120006 0x02a3490000d12000 0x0c3800000e000000 0x00c3800000e00000

def z550 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ff807f02e00fc09 0x10ff807f02e00fc0

def z551 : W := mkw 0x6ffffffffffffc0f 0xc6ffffffffffffc0 0xeffffffffffffc0f 0xfeffffffffffffc0

def z552 : W := mkw 0x0010900004120004 0x0001090000412000 0xfc399880ee330c3f 0xdfc399880ee330c3

def z553 : W := mkw 0x0018928484120124 0x2001892848412012 0xf8399e8cc0330331 0xdf8399e8cc033033

def z554 : W := mkw 0x0181450a0000a280 0x00181450a0000a28 0xd3c1e70f0000f3c9 0xbd3c1e70f0000f3c

def z555 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x33c06103303cf3ca 0x233c06103303cf3c

def z556 : W := mkw 0x0008028482004921 0x2000802848200492 0x0000060c0000c300 0x00000060c0000c30

def z557 : W := mkw 0x0018928486124925 0x2001892848612492 0xcc399e8cee30c301 0xdcc399e8cee30c30

def z558 : W := mkw 0x07ed47da3b68fe89 0xc07ed47da3b68fe8 0x8fff87fc3ff0ff0f 0x78fff87fc3ff0ff0

def z559 : W := mkw 0x01c1453b7068b6d8 0x901c1453b7068b6d 0xf3c1e7fff03cfffb 0xbf3c1e7fff03cfff

def z560 : W := mkw 0x0002282140850050 0x1000228214085005 0x00006003000c00c0 0x000006003000c00c

def z561 : W := mkw 0x0002282140850050 0x1000228214085005 0xf0007883c00f0cff 0xcf0007883c00f0cf

def z562 : W := mkw 0x062e2af14bc55c51 0xd062e2af14bc55c5 0xfc3e79f3dfcf3cff 0xefc3e79f3dfcf3cf

def z563 : W := mkw 0x044000103f52fd25 0xe044000103f52fd2 0x340000003ff3ff3e 0x0340000003ff3ff3

def z564 : W := mkw 0x2a36b8314dd71456 0x92a36b8314dd7145 0xfc3e79f3dfcf3cff 0xefc3e79f3dfcf3cf

def z565 : W := mkw 0x4bfdd7ceb028a288 0x04bfdd7ceb028a28 0xfbf9e70f303cf3cb 0xbfbf9e70f303cf3c

def z566 : W := mkw 0x06e62d7179c5b450 0xd06e62d7179c5b45 0xf3c679f3d1cf3cff 0xef3c679f3d1cf3cf

def z567 : W := mkw 0x0181450a00000000 0x00181450a0000000 0xf3c1e70f2030c30b 0xbf3c1e70f2030c30

def z568 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x0006007001c00000 0x00006007001c0000

def z569 : W := mkw 0x4993fd2fc0000000 0x04993fd2fc000000 0xc3c1ff0fc0000001 0xbc3c1ff0fc000000

def z570 : W := mkw 0x2b7ffa84bfbf492f 0x22b7ffa84bfbf492 0xaffffe0c3fffc306 0xfaffffe0c3fffc30

def z571 : W := mkw 0x0000001000401400 0x8000000100040140 0x000600f001c00c04 0x4000600f001c00c0

def z572 : W := mkw 0x2bf5d50a3d3aa28e 0x02bf5d50a3d3aa28 0xfff9e70f3e3cf3cb 0xbfff9e70f3e3cf3c

def z573 : W := mkw 0x0008028480000000 0x0000802848000000 0x4000068cc0000001 0x04000068cc000000

def z574 : W := mkw 0x2b7ffab5ffff5d7f 0xb2b7ffab5ffff5d7 0xffffffffffffffff 0xffffffffffffffff

def z575 : W := mkw 0x2953f80034bf000e 0x02953f80034bf000 0xa3c1f800303f0002 0xba3c1f800303f000

def z576 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xc3c1e70f100c30c1 0xbc3c1e70f100c30c

def z577 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xcfffffffce030c35 0xfcfffffffce030c3

def z578 : W := mkw 0x4913f83fc0c51450 0x94913f83fc0c5145 0xf007f9ffd1cf3cff 0xef007f9ffd1cf3cf

def z579 : W := mkw 0x07fdd7debf7affad 0xe07fdd7debf7affa 0xffffffffffffffff 0xffffffffffffffff

def z580 : W := mkw 0x0181450a00000000 0x00181450a0000000 0x03c0610300000000 0x203c061030000000

def z581 : W := mkw 0x204000003dbfa28e 0x0204000003dbfa28 0x340000003ffff3ce 0x0340000003ffff3c

def z582 : W := mkw 0x2efebfd03fd7fc07 0xc2efebfd03fd7fc0 0x8ffe1ff03fc3fc0f 0x78ffe1ff03fc3fc0

def z583 : W := mkw 0x0119d28e863a4bad 0x20119d28e863a4ba 0xfc39fe8fee3fcfff 0xdfc39fe8fee3fcff

def z584 : W := mkw 0x0008028486124925 0x2000802848612492 0x7400068cee33cf3f 0x07400068cee33cf3

def z585 : W := mkw 0x448807ffc240fc01 0xc448807ffc240fc0 0x400007ffc000fc09 0x0400007ffc000fc0

def z586 : W := mkw 0x2b77f8317dff145e 0x92b77f8317dff145 0xaffff9733fff30c6 0xfaffff9733fff30c

def z587 : W := mkw 0x0101400a00280288 0x00101400a0028028 0xf001e10f103c33cb 0xaf001e10f103c33c

def z588 : W := mkw 0x20589284bfbf492f 0x220589284bfbf492 0xfc399e8cffffcf3f 0xdfc399e8cffffcf3

def z589 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x8c3807f02e00fc0f 0x58c3807f02e00fc0

def z590 : W := mkw 0x004000003028a288 0x0004000003028a28 0xf001860c303cf3cb 0x9f001860c303cf3c

def z591 : W := mkw 0x0010900004120004 0x0001090000412000 0xfc399e0c2e33c30f 0xdfc399e0c2e33c30

def z592 : W := mkw 0x0018928486124925 0x2001892848612492 0xcc399e8cce030c35 0xdcc399e8cce030c3

def z593 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x500661f3d1cc3cf9 0x2500661f3d1cc3cf

def z594 : W := mkw 0x001abaa5c6124925 0x2001abaa5c612492 0xfc3fffffee33cf3f 0xffc3fffffee33cf3

def z595 : W := mkw 0x4bfdd7ceb028a288 0x04bfdd7ceb028a28 0x0bf9860c2030c300 0x10bf9860c2030c30

def z596 : W := mkw 0x0000002140000050 0x1000000214000005 0x50000003c00000f0 0x050000003c00000f

def z597 : W := mkw 0x00c807803200e801 0x000c807803200e80 0x8ff807803e00fc0f 0x78ff807803e00fc0

def z598 : W := mkw 0x040802d002405c01 0xc040802d002405c0 0x000000f000000c00 0x0000000f000000c0

def z599 : W := mkw 0x066400103b40fc01 0xc066400103b40fc0 0x8ffe00003fc0fc0e 0x78ffe00003fc0fc0

def z600 : W := mkw 0x0012b825c4970174 0x30012b825c497017 0x7001f80fc03f03f0 0x87001f80fc03f03f

def z601 : W := mkw 0x0141400030280008 0x0014140003028000 0xf3c1e103303c30cb 0xbf3c1e103303c30c

def z602 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x83c1870c3030f30b 0x383c1870c3030f30

def z603 : W := mkw 0x0000000006124925 0x2000000000612492 0x040000000e030c34 0x0040000000e030c3

def z604 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x23c7f80011ff0000 0xa23c7f80011ff000

def z605 : W := mkw 0x4bffffeff0280008 0x04bffffeff028000 0xebfffffff03c0003 0xfebfffffff03c000

def z606 : W := mkw 0x2913f80a04bf028e 0x02913f80a04bf028 0x7001f80f003f03c0 0x87001f80f003f03c

def z607 : W := mkw 0x0101400000280008 0x0010140000028000 0x2001e000003c0000 0x82001e000003c000

def z608 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x2ff9f8002e3f0000 0x92ff9f8002e3f000

def z609 : W := mkw 0x2ffdd7c03f3ae80f 0x42ffdd7c03f3ae80 0x0ff986002e30c000 0x10ff986002e30c00

def z610 : W := mkw 0x05c947da3268fe89 0xc05c947da3268fe8 0xf3c1e7ff303cffcb 0xbf3c1e7ff303cffc

def z611 : W := mkw 0x0002282140000000 0x0000228214000000 0xf00679f3d00c30cb 0xef00679f3d00c30c

def z612 : W := mkw 0x0008028002004801 0x0000802800200480 0x0c3806002e00c000 0x10c3806002e00c00

def z613 : W := mkw 0x0002280000850000 0x0000228000085000 0xf0067880d1cf0c3f 0xef0067880d1cf0c3

def z614 : W := mkw 0x00d89784b612e925 0x200d89784b612e92 0xfff99f8cfe33ff3f 0xffff99f8cfe33ff3

def z615 : W := mkw 0x0000000000000000 0x0000000000000000 0xa001800020300002 0x9a00180002030000

def z616 : W := mkw 0x291bfa8486bf492f 0x2291bfa8486bf492 0xfc39fe8cee3fcf3f 0xdfc39fe8cee3fcf3

def z617 : W := mkw 0x408a2fffc0c51450 0x9408a2fffc0c5145 0xf0067fffd1cf3cff 0xef0067fffd1cf3cf

def z618 : W := mkw 0x0008028482004921 0x2000802848200492 0xf0001e8cc003cf3f 0xcf0001e8cc003cf3

def z619 : W := mkw 0x0018928486124925 0x2001892848612492 0x5c381e8cce03cf3d 0x45c381e8cce03cf3

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000103000030c9 0x050000103000030c

def z621 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x500619f3c1c33cfd 0x4500619f3c1c33cf

def z622 : W := mkw 0x040000100240fc01 0xc040000100240fc0 0x000000000000fc08 0x0000000000000fc0

def z623 : W := mkw 0x02ec07c03000a000 0x002ec07c03000a00 0x8bfe07f03000f00b 0x78bfe07f03000f00

def z624 : W := mkw 0x409897efc6124925 0x2409897efc612492 0xfc399fffee33cf3f 0xdfc399fffee33cf3

def z625 : W := mkw 0x01dbffbff6fffffd 0xb01dbffbff6fffff 0xffffffffffffffff 0xffffffffffffffff

def z626 : W := mkw 0x4b37f82fc0000000 0x04b37f82fc000000 0xcbfff80fc0000000 0xfcbfff80fc000000

def z627 : W := mkw 0x0080050a0000a280 0x00080050a0000a28 0x00000103000030c0 0x000000103000030c

def z628 : W := mkw 0x0000001006d75d75 0xb0000001006d75d7 0x340000003ffffffe 0x0340000003ffffff

def z629 : W := mkw 0x0b3ffa8480000000 0x00b3ffa848000000 0xcbfffe8cc0000001 0xfcbfffe8cc000000

def z630 : W := mkw 0x0080050000000000 0x0008005000000000 0x83c0070000000001 0x383c007000000000

def z631 : W := mkw 0x001aba8486974925 0x2001aba848697492 0xfc3ffe8cffffcf3f 0xffc3ffe8cffffcf3

def z632 : W := mkw 0x6a3ebae5cd970006 0x06a3ebae5cd97000 0x0c3e18f0cfc30004 0x40c3e18f0cfc3000

def z633 : W := mkw 0x0141400030280008 0x0014140003028000 0xf3c1e60c303cc30b 0xbf3c1e60c303cc30

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000000030c3e 0x03000000000030c3

def z635 : W := mkw 0x0141400030280008 0x0014140003028000 0x03c06000100c0000 0x203c06000100c000

def z636 : W := mkw 0x0000000000000000 0x0000000000000000 0xf00000000000000b 0x8f00000000000000

def z637 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xf00618f0c1c30c3f 0xcf00618f0c1c30c3

def z638 : W := mkw 0x0002282140000000 0x0000228214000000 0x40007803c0000000 0x840007803c000000

def z639 : W := mkw 0x0000000000850000 0x0000000000085000 0x2000000011cf0006 0x02000000011cf000

def z640 : W := mkw 0x4a3c92c480000000 0x04a3c92c48000000 0x0838000000000000 0x0083800000000000

def z641 : W := mkw 0x06ec07c03b00e801 0x406ec07c03b00e80 0x8ff806802e00cc0f 0x58ff806802e00cc0

def z642 : W := mkw 0x0002280000850000 0x0000228000085000 0x20007800000f0000 0x820007800000f000

def z643 : W := mkw 0x066c02d03b40fc01 0xc066c02d03b40fc0 0x0c3e00f03fc0fc0e 0x40c3e00f03fc0fc0

def z644 : W := mkw 0x4e3ebaf5cb405c01 0xc4e3ebaf5cb405c0 0x0c3e18f0cfc00c04 0x40c3e18f0cfc00c0

def z645 : W := mkw 0x00c0050a3000a280 0x000c0050a3000a28 0xd3c0070f3000f3cb 0x3d3c0070f3000f3c

def z646 : W := mkw 0x06ee2ff17bc5fc51 0xd06ee2ff17bc5fc5 0x8ffe1ff0ffc3fc3f 0x78ffe1ff0ffc3fc3

def z647 : W := mkw 0x2b67683179ed145a 0x92b67683179ed145 0x03c6617311cc30c0 0x203c6617311cc30c

def z648 : W := mkw 0x29d3fd0a34bfa28e 0x029d3fd0a34bfa28 0xf3c1ff0f303ff3cb 0xbf3c1ff0f303ff3c

def z649 : W := mkw 0x06ec07d03bc5fc51 0xd06ec07d03bc5fc5 0xbffe07f03fcffcff 0x7bffe07f03fcffcf

def z650 : W := mkw 0x01836d3b40c51450 0x901836d3b40c5145 0xf3c7ffffd1cf3cff 0xff3c7ffffd1cf3cf

def z651 : W := mkw 0x4a3ebae5c6124925 0x24a3ebae5c612492 0xfc3f9efcee33cf3f 0xdfc3f9efcee33cf3

def z652 : W := mkw 0x4be76d6b7028a288 0x04be76d6b7028a28 0xf3c7e77f303cf3cb 0xbf3c7e77f303cf3c

def z653 : W := mkw 0x01c1451a3068b688 0x801c1451a3068b68 0xf3c7e7ff31fcffcf 0xff3c7e7ff31fcffc

def z654 : W := mkw 0x01c36d2b7028a288 0x001c36d2b7028a28 0xf3c7fffff03cf3cb 0xff3c7fffff03cf3c

def z655 : W := mkw 0x6bfdd7cebd3a000e 0x06bfdd7cebd3a000 0x0ff9860c2e300000 0x10ff9860c2e30000

def z656 : W := mkw 0x4bbdd7ce86124925 0x24bbdd7ce8612492 0xfff99e8cee33cf3f 0xdfff99e8cee33cf3

def z657 : W := mkw 0x07ed47da3b68fe89 0xc07ed47da3b68fe8 0x8ffe67f33fccfccf 0x78ffe67f33fccfcc

def z658 : W := mkw 0x4bbfffffc0c51450 0x94bbfffffc0c5145 0xcbffffffc1c30c35 0xfcbffffffc1c30c3

def z659 : W := mkw 0x06fc97c4bf12e925 0x606fc97c4bf12e92 0x0ff9860c2e30c300 0x10ff9860c2e30c30

def z660 : W := mkw 0x0000000000280288 0x0000000000028028 0x30000000003c03c0 0x030000000003c03c

def z661 : W := mkw 0x0008028002004801 0x0000802800200480 0xfc381e80ee03cc3f 0xdfc381e80ee03cc3

def z662 : W := mkw 0x001abaa5c6974975 0x3001abaa5c697497 0xfc39fe8fee3fcfff 0xdfc39fe8fee3fcff

def z663 : W := mkw 0x01c1450a30280008 0x001c1450a3028000 0xe3c1e70f303c0003 0xbe3c1e70f303c000

def z664 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc39860c2e30c30b 0x9fc39860c2e30c30

def z665 : W := mkw 0x2a3eba848f974927 0x22a3eba848f97492 0xfc3f9e8ceff3cf3f 0xdfc3f9e8ceff3cf3

def z666 : W := mkw 0x4bffffeff028a288 0x04bffffeff028a28 0xcbffffffe030c301 0xfcbffffffe030c30

def z667 : W := mkw 0x0000000000000000 0x0000000000000000 0x70001800c0030030 0x870001800c003003

def z668 : W := mkw 0x06febff5ffd7fd75 0xf06febff5ffd7fd7 0xffffffffffffffff 0xffffffffffffffff

def z669 : W := mkw 0x2a3eba848f974927 0x22a3eba848f97492 0x0c3e1880cfc30c34 0x40c3e1880cfc30c3

def z670 : W := mkw 0x0002282140850050 0x1000228214085005 0xf0067803d1cf00f6 0xef0067803d1cf00f

def z671 : W := mkw 0x0002283146d75d75 0xb0002283146d75d7 0xf40679f3ffffffff 0xef40679f3fffffff

def z672 : W := mkw 0x0018928486124925 0x2001892848612492 0x7c39988cce330f34 0xc7c39988cce330f3

def z673 : W := mkw 0x01c145003028a008 0x001c145003028a00 0xa3c1e700303cf00b 0xba3c1e700303cf00

def z674 : W := mkw 0x4abebfefc0000000 0x04abebfefc000000 0x483e1fffc0000001 0x4483e1fffc000000

def z675 : W := mkw 0x0000003140c51450 0x90000003140c5145 0x700001f3d1cf3cff 0x0700001f3d1cf3cf

def z676 : W := mkw 0x0080050a0000a280 0x00080050a0000a28 0xf001870f2030f3cb 0x9f001870f2030f3c

def z677 : W := mkw 0x048005500040b400 0xc048005500040b40 0x0000017000003000 0x0000001700000300

def z678 : W := mkw 0x4a3ebae5c0000000 0x04a3ebae5c000000 0xc83e79f3c0000001 0xec83e79f3c000000

def z679 : W := mkw 0x6b7ffae5fdbf000e 0x06b7ffae5fdbf000 0xaffff8f0ffff0006 0xfaffff8f0ffff000

def z680 : W := mkw 0x0002280000850000 0x0000228000085000 0xf006790311cf30cf 0xef006790311cf30c

def z681 : W := mkw 0x0000001000401400 0x8000000100040140 0xf00661f311cc3ccf 0xef00661f311cc3cc

def z682 : W := mkw 0x0040000030280008 0x0004000003028000 0x20000000303c0002 0x020000000303c000

def z683 : W := mkw 0x07ed47ca3b28ea89 0x407ed47ca3b28ea8 0xfff9e70f3e3cf3cb 0xbfff9e70f3e3cf3c

def z684 : W := mkw 0x044000003b00e801 0x4044000003b00e80 0x040000002e00c000 0x0040000002e00c00

def z685 : W := mkw 0x062c02d00b405c01 0xc062c02d00b405c0 0x8c3e06f02fc0cc0f 0x58c3e06f02fc0cc0

def z686 : W := mkw 0x4913f82fc0280288 0x04913f82fc028028 0x7001f80fc03c03c0 0x87001f80fc03c03c

def z687 : W := mkw 0x0010900484120124 0x2001090048412012 0xf0019e0ce033c33b 0x9f0019e0ce033c33

def z688 : W := mkw 0x01c36d3b70edb6d8 0x901c36d3b70edb6d 0xf3c679f3d1cf3cff 0xef3c679f3d1cf3cf

def z689 : W := mkw 0x0000000004120124 0x2000000000412012 0x3000000000330330 0x0300000000033033

def z690 : W := mkw 0x0080050a0000a280 0x00080050a0000a28 0xf000670f100cf3cb 0xaf000670f100cf3c

def z691 : W := mkw 0x0000000006124925 0x2000000000612492 0xf401860c2e33cf3f 0x9f401860c2e33cf3

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x30000000100c30ca 0x030000000100c30c

def z693 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x73c1e10f103c33c0 0xa73c1e10f103c33c

def z694 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x300618f0d1cf3cfe 0x4300618f0d1cf3cf

def z695 : W := mkw 0x0080050a0000a280 0x00080050a0000a28 0x0000060c0000c300 0x00000060c0000c30

def z696 : W := mkw 0x001abaa5c0000000 0x0001abaa5c000000 0xc83fffffc0000001 0xfc83fffffc000000

def z697 : W := mkw 0x4913f82fc0850050 0x14913f82fc085005 0x7001f80fc00f00f0 0x87001f80fc00f00f

def z698 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001880c0030c34 0x400001880c0030c3

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0001880c0000001 0xcc0001880c000000

def z700 : W := mkw 0x4b3ffaefc0000000 0x04b3ffaefc000000 0x483ff8ffc0000000 0xc483ff8ffc000000

def z701 : W := mkw 0x00c005003000a000 0x000c005003000a00 0xf3c06703300cf0cb 0xbf3c06703300cf0c

def z702 : W := mkw 0x04c005103b40fc01 0xc04c005103b40fc0 0x87c007003fc0fc0f 0x387c007003fc0fc0

def z703 : W := mkw 0x491bfaafc6124925 0x2491bfaafc612492 0xfc39fe8fee33cf3f 0xdfc39fe8fee33cf3

def z704 : W := mkw 0x062c02c00b004801 0x4062c02c00b00480 0x0c3800000e000000 0x00c3800000e00000

def z705 : W := mkw 0x07ed47da3b40fc01 0xc07ed47da3b40fc0 0xcfffe7ff3fc0fc0f 0xfcfffe7ff3fc0fc0

def z706 : W := mkw 0x00c005003000a000 0x000c005003000a00 0x03c006002000c000 0x103c006002000c00

def z707 : W := mkw 0x02749004bd120124 0x202749004bd12012 0xffff980cfff30336 0xfffff980cfff3033

def z708 : W := mkw 0x02ac07c482004921 0x202ac07c48200492 0xdbfe07fcc000cf39 0x7dbfe07fcc000cf3

def z709 : W := mkw 0x02ac07ca0000a280 0x002ac07ca0000a28 0xdbfe07ff0000f3c9 0x7dbfe07ff0000f3c

def z710 : W := mkw 0x4bbfffefc0850000 0x04bbfffefc085000 0xcbffffffc1c30005 0xfcbffffffc1c3000

def z711 : W := mkw 0x2b37f8000d970006 0x02b37f8000d97000 0x0ffe78000fc30004 0x60ffe78000fc3000

def z712 : W := mkw 0x4bbdd7ce80000000 0x04bbdd7ce8000000 0x0bf987fc00000001 0x10bf987fc0000000

def z713 : W := mkw 0x6bbfffefc43a000e 0x06bbfffefc43a000 0xcbffffffc0300001 0xfcbffffffc030000

def z714 : W := mkw 0x0bbfffc480000000 0x00bbfffc48000000 0xcbfffffcc0000001 0xfcbfffffcc000000

def z715 : W := mkw 0x0141400030280008 0x0014140003028000 0xf3c1e70f303cf3cb 0xbf3c1e70f303cf3c

def z716 : W := mkw 0x6b77f80ebdbf000e 0x06b77f80ebdbf000 0xaffff80c3fff0006 0xfaffff80c3fff000

def z717 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xfc3e79f3ffcf3cff 0xffc3e79f3ffcf3cf

def z718 : W := mkw 0x2b75d0003d3a000e 0x02b75d0003d3a000 0xafffe0003ffc0006 0xfafffe0003ffc000

def z719 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xebffffffe0300003 0xfebffffffe030000

def z720 : W := mkw 0x2ab6bd0a0d97a286 0x02ab6bd0a0d97a28 0x5c3e1f0f0fc3f3cd 0x45c3e1f0f0fc3f3c

def z721 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe07f03fc0fc09 0x30ffe07f03fc0fc0

def z722 : W := mkw 0x4d53f83ffb40fc01 0xc4d53f83ffb40fc0 0x4401f80fffc0fc0e 0x84401f80fffc0fc0

def z723 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x73c1e70f203cf3c9 0x973c1e70f203cf3c

def z724 : W := mkw 0x2b75d0003d3a000e 0x02b75d0003d3a000 0x0ff980003ff00006 0x10ff980003ff0000

def z725 : W := mkw 0x0b37f80004970004 0x00b37f8000497000 0xaffff8003fff0006 0xfaffff8003fff000

def z726 : W := mkw 0x06ee2fe17b85e851 0x506ee2fe17b85e85 0x7ff87e03ee0fc0f0 0x97ff87e03ee0fc0f

def z727 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x500007f30000fcc9 0x0500007f30000fcc

def z728 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe07f02fc0fc0d 0x50ffe07f02fc0fc0

def z729 : W := mkw 0x2b77f8003dbf005e 0x12b77f8003dbf005 0xbffff8003fff00f6 0xfbffff8003fff00f

def z730 : W := mkw 0x2b75d0317d7a145e 0x92b75d0317d7a145 0x5ff981f3ee303cf9 0x15ff981f3ee303cf

def z731 : W := mkw 0x04589294bf52fd25 0xe04589294bf52fd2 0x0c39860c3ff0ff0e 0x10c39860c3ff0ff0

def z732 : W := mkw 0x4a7ebae5f028a288 0x04a7ebae5f028a28 0x383e18f0f03cf3ca 0x4383e18f0f03cf3c

def z733 : W := mkw 0x072d42da0b685e89 0xc072d42da0b685e8 0x7c3fe0ff0ffc0fc4 0xc7c3fe0ff0ffc0fc

def z734 : W := mkw 0x02bc97c486124925 0x202bc97c48612492 0x8fff87fc2e30c301 0x78fff87fc2e30c30

def z735 : W := mkw 0x4ba76d6b40850050 0x14ba76d6b4085005 0x03c66173000c00c0 0x203c66173000c00c

def z736 : W := mkw 0x0abebfc000000000 0x00abebfc00000000 0x8bfe1ff000000001 0x78bfe1ff00000000

def z737 : W := mkw 0x4bbfffefc4120124 0x24bbfffefc412012 0xffffffffee330337 0xfffffffffee33033

def z738 : W := mkw 0x2b77f8217dbf000e 0x02b77f8217dbf000 0xaffff8f0ffff0006 0xfaffff8f0ffff000

def z739 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x4bf9ffffc0000001 0x94bf9ffffc000000

def z740 : W := mkw 0x2b77f8217dbf000e 0x02b77f8217dbf000 0xeffff803ffff0006 0xfeffff803ffff000

def z741 : W := mkw 0x044000103b68fe89 0xc044000103b68fe8 0x040000003fccfcce 0x0040000003fccfcc

def z742 : W := mkw 0x06ec07d4bb40fd21 0xe06ec07d4bb40fd2 0x8ffe07fc3fc0ff0f 0x78ffe07fc3fc0ff0

def z743 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xafffe0003ffc0002 0xbafffe0003ffc000

def z744 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe07703fc0fc0e 0x30ffe07703fc0fc0

def z745 : W := mkw 0x2b77f804bdbf012e 0x22b77f804bdbf012 0xaffff80c3fff0306 0xfaffff80c3fff030

def z746 : W := mkw 0x058947da0268fe89 0xc058947da0268fe8 0x7001e7ff003cffc9 0x87001e7ff003cffc

def z747 : W := mkw 0x044000103f52fd25 0xe044000103f52fd2 0x040000003ff0ff0e 0x0040000003ff0ff0

def z748 : W := mkw 0x2e76b8103fd7fc07 0xc2e76b8103fd7fc0 0x0c3e18003fc3fc0e 0x40c3e18003fc3fc0

def z749 : W := mkw 0x02bc97c004120004 0x002bc97c00412000 0xafff9ff02e330007 0xfafff9ff02e33000

def z750 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xaffff9033fff30c6 0xfaffff9033fff30c

def z751 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbffffffe000c00b 0xfcbffffffe000c00

def z752 : W := mkw 0x0040001030edb6d8 0x90040001030edb6d 0x3000000031fcf3ca 0x03000000031fcf3c

def z753 : W := mkw 0x4bbfffefc0850050 0x14bbfffefc085005 0xcbffffffc00c00c1 0xfcbffffffc00c00c

def z754 : W := mkw 0x2b77f8217dbf000e 0x02b77f8217dbf000 0xaffff9733fff0006 0xfaffff9733fff000

def z755 : W := mkw 0x044000103bedfed9 0xd044000103bedfed 0x340000003ffffffe 0x0340000003ffffff

def z756 : W := mkw 0x03bdd7ce86124925 0x203bdd7ce8612492 0xffffffffee33cf3f 0xfffffffffee33cf3

def z757 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe06f02fc0cc0f 0x58ffe06f02fc0cc0

def z758 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x000006f00000cc00 0x0000006f00000cc0

def z759 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x8ffff8002ff30004 0xf8ffff8002ff3000

def z760 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xcffe67f33fc0fc0f 0xfcffe67f33fc0fc0

def z761 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x0ffe60001fcc0000 0x20ffe60001fcc000

def z762 : W := mkw 0x02ac07d002405c01 0x802ac07d002405c0 0x8ffe07f03fc0fc0f 0x78ffe07f03fc0fc0

def z763 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xaffe1ff03fc3fc0f 0xfaffe1ff03fc3fc0

def z764 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xeffff880ffff0007 0xfeffff880ffff000

def z765 : W := mkw 0x0264000039000000 0x0026400003900000 0x8ffe00803fc00c0f 0x78ffe00803fc00c0

def z766 : W := mkw 0x4aae2fe140000000 0x04aae2fe14000000 0x8bfe07f000000001 0x78bfe07f00000000

def z767 : W := mkw 0x0181452b40000000 0x00181452b4000000 0xc3c1e7ffc0000001 0xbc3c1e7ffc000000

def z768 : W := mkw 0x4ba76d6b46124925 0x24ba76d6b4612492 0x37c661732e33cf3e 0x237c661732e33cf3

def z769 : W := mkw 0x001abab5c6d75d75 0xb001abab5c6d75d7 0x0c3fe77f3ffcf3c0 0x30c3fe77f3ffcf3c

def z770 : W := mkw 0x06f49554bd52b524 0xe06f49554bd52b52 0x73c7997cd1f33330 0xa73c7997cd1f3333

def z771 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc399f8cfe33ff3f 0xffc399f8cfe33ff3

def z772 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe06f03fc0fc0e 0x50ffe06f03fc0fc0

def z773 : W := mkw 0x044802903b40fc01 0xc044802903b40fc0 0x0c3800803fc0fc0e 0x40c3800803fc0fc0

def z774 : W := mkw 0x4abebfefc0000000 0x04abebfefc000000 0xcbfe1fffc0000001 0x7cbfe1fffc000000

def z775 : W := mkw 0x026400003928a288 0x0026400003928a28 0xbffe00003ffcf3ce 0x7bffe00003ffcf3c

def z776 : W := mkw 0x0264000039000000 0x0026400003900000 0x0ffe00003fc00000 0x30ffe00003fc0000

def z777 : W := mkw 0x2b77f8217dbf000e 0x02b77f8217dbf000 0xfffff9f3ffff0c3f 0xffffff9f3ffff0c3

def z778 : W := mkw 0x4bbfffefc0280288 0x04bbfffefc028028 0xcbffffffc0300301 0xfcbffffffc030030

def z779 : W := mkw 0x6a7ebae5fdbf000e 0x06a7ebae5fdbf000 0x2c3e18f0ffff0006 0x42c3e18f0ffff000

def z780 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xdffe07f33fc0fccf 0x7dffe07f33fc0fcc

def z781 : W := mkw 0x02bc97c486124925 0x202bc97c48612492 0x8ffe1ff0ce030c35 0x78ffe1ff0ce030c3

def z782 : W := mkw 0x448807fb4240fc01 0xc448807fb4240fc0 0x000007f30000fc09 0x0000007f30000fc0

def z783 : W := mkw 0x0226282140000000 0x0022628214000000 0xcbfe79f3c0000001 0xfcbfe79f3c000000

def z784 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc3f9ffcee33cf3f 0xffc3f9ffcee33cf3

def z785 : W := mkw 0x6bbfffefcd120006 0x06bbfffefcd12000 0xcfffffffce000001 0xfcfffffffce00000

def z786 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x000001f000003c00 0x0000001f000003c0

def z787 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe1ff0ffc3fc3f 0x78ffe1ff0ffc3fc3

def z788 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xbffe07f03fccfccf 0x7bffe07f03fccfcc

def z789 : W := mkw 0x244000103bedfc0b 0xc244000103bedfc0 0x040000003fccfc0e 0x0040000003fccfc0

def z790 : W := mkw 0x4bbfffefc000a280 0x04bbfffefc000a28 0xfbffffffd00cf3cb 0xffbffffffd00cf3c

def z791 : W := mkw 0x4bbdd7ce80000000 0x04bbdd7ce8000000 0x0bff86fc00000000 0x50bff86fc0000000

def z792 : W := mkw 0x0040001030ed1458 0x90040001030ed145 0x3000000031ff3cfe 0x03000000031ff3cf

def z793 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xcfffffffce000001 0xfcfffffffce00000

def z794 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xaffff9f03fff0007 0xfaffff9f03fff000

def z795 : W := mkw 0x0040001039401400 0x8004000103940140 0x040000003fc03c0e 0x0040000003fc03c0

def z796 : W := mkw 0x044228317bc5fc51 0xd044228317bc5fc5 0x74007803ffcffcfe 0x874007803ffcffcf

def z797 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xeffff9033fff0007 0xfeffff9033fff000

def z798 : W := mkw 0x2913f82144bf000e 0x02913f82144bf000 0x6001f803c03f0000 0x86001f803c03f000

def z799 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8fff87fc3ff0ff0f 0x78fff87fc3ff0ff0

def z800 : W := mkw 0x06e405503940b400 0xc06e405503940b40 0x8ffe01f03fc03c0f 0x78ffe01f03fc03c0

def z801 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x0bfe617300000000 0x20bfe61730000000

def z802 : W := mkw 0x0264000039280008 0x0026400003928000 0xaffe00003ffc0006 0x7affe00003ffc000

def z803 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xfffff800ffff0036 0xffffff800ffff003

def z804 : W := mkw 0x42ac07efc0000000 0x042ac07efc000000 0x4bf807ffc0000001 0x14bf807ffc000000

def z805 : W := mkw 0x2b6768003dbf000e 0x02b6768003dbf000 0xaffe60003fff0006 0x7affe60003fff000

def z806 : W := mkw 0x4b3ffae5c0000000 0x04b3ffae5c000000 0xcbfff9f3c0000001 0xfcbfff9f3c000000

def z807 : W := mkw 0x06ec07da3b68fe89 0xc06ec07da3b68fe8 0xfffe07ff3ffcffcf 0x7fffe07ff3ffcffc

def z808 : W := mkw 0x0181450a0028a288 0x00181450a0028a28 0xf3c1e70f003cf3c9 0xbf3c1e70f003cf3c

def z809 : W := mkw 0x2b6540003928000a 0x02b6540003928000 0x8ffe00003fc00006 0x78ffe00003fc0000

def z810 : W := mkw 0x048807d48240fd21 0xe048807d48240fd2 0x000007fc0000ff09 0x0000007fc0000ff0

def z811 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x83c661f300000001 0x683c661f30000000

def z812 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c1ff0ff03ff3fb 0xbf3c1ff0ff03ff3f

def z813 : W := mkw 0x4bbfffefc0ad02d8 0x14bbfffefc0ad02d 0xfbffffffc03f03f1 0xffbffffffc03f03f

def z814 : W := mkw 0x204000103dff145e 0x9204000103dff145 0x240000003fff0c36 0x0240000003fff0c3

def z815 : W := mkw 0x01d9d78eb63aebad 0x201d9d78eb63aeba 0x0ff87983de0f3cf4 0x60ff87983de0f3cf

def z816 : W := mkw 0x06ec07debb40ffa1 0xe06ec07debb40ffa 0xdffe07ffffc0ffff 0x7dffe07ffffc0fff

def z817 : W := mkw 0x4baf6fefc0000000 0x04baf6fefc000000 0xcbfe67ffc0000001 0x7cbfe67ffc000000

def z818 : W := mkw 0x044000103968b688 0xc044000103968b68 0x0000000011cc30c0 0x00000000011cc30c

def z819 : W := mkw 0x0264000039000000 0x0026400003900000 0x0ff800003fc00006 0x10ff800003fc0000

def z820 : W := mkw 0x4bbfffefc2004921 0x24bbfffefc200492 0xcbffffffc0000c31 0xfcbffffffc0000c3

def z821 : W := mkw 0x06ec07d03b68fe89 0xc06ec07d03b68fe8 0x8ffe07f03fccfccf 0x78ffe07f03fccfcc

def z822 : W := mkw 0x04509014bf52fd25 0xe04509014bf52fd2 0x7401980cfff3ff3e 0x87401980cfff3ff3

def z823 : W := mkw 0x4bb7fd6fc0000000 0x04bb7fd6fc000000 0x03c67973c0000000 0x203c67973c000000

def z824 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x4bffe7ffc0000001 0x34bffe7ffc000000

def z825 : W := mkw 0x0266280039850000 0x0026628003985000 0x8ffe60003fcc0006 0x78ffe60003fcc000

def z826 : W := mkw 0x2b77f80039ad000a 0x02b77f80039ad000 0x8ffff8003fcc0006 0xf8ffff8003fcc000

def z827 : W := mkw 0x004228217028a288 0x0004228217028a28 0xf00679f3f03cf3cb 0xef00679f3f03cf3c

def z828 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xcfff87fc3fc0fc0f 0xfcfff87fc3fc0fc0

def z829 : W := mkw 0x01836d2b40000000 0x001836d2b4000000 0xc3c679f3c0000001 0xec3c679f3c000000

def z830 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0xc3c6617300000001 0xac3c661730000000

def z831 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x340000003fccfcce 0x0340000003fccfcc

def z832 : W := mkw 0x4bbfffe5c0000000 0x04bbfffe5c000000 0x8bfffff0c0000001 0xf8bfffff0c000000

def z833 : W := mkw 0x045090103f52fc05 0xc045090103f52fc0 0xac3998003ff3fc0e 0xdac3998003ff3fc0

def z834 : W := mkw 0x6b77f82ffdbf012e 0x26b77f82ffdbf012 0xfffff80fffff0336 0xffffff80fffff033

def z835 : W := mkw 0x408807efc0000000 0x0408807efc000000 0xc3c007ffc0000001 0x3c3c007ffc000000

def z836 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xfbffffffc033cf39 0xffbffffffc033cf3

def z837 : W := mkw 0x0143683b70edb6d8 0x90143683b70edb6d 0x7001f80ff1fffffe 0x87001f80ff1fffff

def z838 : W := mkw 0x0264000039000000 0x0026400003900000 0xffff860c3ff0c30f 0xfffff860c3ff0c30

def z839 : W := mkw 0x2b75d0003dbf000e 0x02b75d0003dbf000 0x0ff980003ffc0000 0x10ff980003ffc000

def z840 : W := mkw 0x2b77f80a3dbfa28e 0x02b77f80a3dbfa28 0xfffff80f3ffff3ce 0xffffff80f3ffff3c

def z841 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x73c1e60f303cf3ca 0x973c1e60f303cf3c

def z842 : W := mkw 0x0264000039000000 0x0026400003900000 0x0ffe00001fc00004 0x60ffe00001fc0000

def z843 : W := mkw 0x2b37f8000d970006 0x02b37f8000d97000 0xaffff8002ff30006 0xfaffff8002ff3000

def z844 : W := mkw 0x4aa62d6140000000 0x04aa62d614000000 0x03c6017000000000 0x203c601700000000

def z845 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xf007ffffd1cf3cff 0xff007ffffd1cf3cf

def z846 : W := mkw 0x4bbfffefc4120004 0x04bbfffefc412000 0xebffffffc0330001 0xfebffffffc033000

def z847 : W := mkw 0x06ec07da3b40fe81 0xc06ec07da3b40fe8 0xffff87ff3ff0ffcf 0xfffff87ff3ff0ffc

def z848 : W := mkw 0x02ec07c03b004801 0x002ec07c03b00480 0x8ffe07f03fc0cc0f 0x78ffe07f03fc0cc0

def z849 : W := mkw 0x4bbdd7de80c51450 0x94bbdd7de80c5145 0x3bf9860c11cf3cfe 0x13bf9860c11cf3cf

def z850 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x500679f3d1cf3cfd 0x6500679f3d1cf3cf

def z851 : W := mkw 0x00589294b6fffffd 0xb00589294b6fffff 0xfc399e8cffffffff 0xdfc399e8cfffffff

def z852 : W := mkw 0x2b37f82144bf005e 0x12b37f82144bf005 0xfbfff9f3c03f00f1 0xffbfff9f3c03f00f

def z853 : W := mkw 0x048807f5c240fd71 0xf048807f5c240fd7 0x500007ffc000fff9 0x0500007ffc000fff

def z854 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x300679f3d1cf3cfe 0x6300679f3d1cf3cf

def z855 : W := mkw 0x048807d002405c01 0xc048807d002405c0 0x000007f000000c01 0x0000007f000000c0

def z856 : W := mkw 0x06ac07d00b405c01 0xc06ac07d00b405c0 0x8ffe07f01fc03c0f 0x78ffe07f01fc03c0

def z857 : W := mkw 0x4bb7fd6fc4120124 0x24bb7fd6fc412012 0x73c7f97fc0330330 0xa73c7f97fc033033

def z858 : W := mkw 0x02ac07ca00000000 0x002ac07ca0000000 0xcbfe07ff00000001 0x7cbfe07ff0000000

def z859 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x0ffff8003fff0004 0x70ffff8003fff000

def z860 : W := mkw 0x4bb7fd6fc0000000 0x04bb7fd6fc000000 0x03c7e17f00000000 0x203c7e17f0000000

def z861 : W := mkw 0x066400103b40fc01 0xc066400103b40fc0 0x0c3e00003fc0fc0e 0x40c3e00003fc0fc0

def z862 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x800679f3d1cf3cff 0x6800679f3d1cf3cf

def z863 : W := mkw 0x4bad47efc0000000 0x04bad47efc000000 0x43c007ffc0000001 0x043c007ffc000000

def z864 : W := mkw 0x048807d48240fc01 0xc048807d48240fc0 0x400007fcc000fc09 0x0400007fcc000fc0

def z865 : W := mkw 0x4bbfffefc0850050 0x14bbfffefc085005 0xfbffffffc00f0cff 0xffbffffffc00f0cf

def z866 : W := mkw 0x02ae2fe142004801 0x002ae2fe14200480 0xfffe7ff3ee03cc3f 0xffffe7ff3ee03cc3

def z867 : W := mkw 0x03ad47ca00000000 0x003ad47ca0000000 0x8bfe67f300000001 0x78bfe67f30000000

def z868 : W := mkw 0x06e405503940b400 0xc06e405503940b40 0x0ffe01701fc03004 0x60ffe01701fc0300

def z869 : W := mkw 0x01836d2b40000000 0x001836d2b4000000 0xc3c7e77f00000001 0xbc3c7e77f0000000

def z870 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc39fe8fee3fcfff 0xdfc39fe8fee3fcff

def z871 : W := mkw 0x048807de8240ffa1 0xe048807de8240ffa 0x500007ffc000fff9 0x0500007ffc000fff

def z872 : W := mkw 0x6913f82fc4bf012e 0x26913f82fc4bf012 0x7001f80fc03f0330 0x87001f80fc03f033

def z873 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x4bfffeffc0000000 0xd4bfffeffc000000

def z874 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x700679f3d1cf3cf9 0xa700679f3d1cf3cf

def z875 : W := mkw 0x418947efc0000000 0x0418947efc000000 0x43c067ffc0000001 0x243c067ffc000000

def z876 : W := mkw 0x4bbfffefc0000120 0x24bbfffefc000012 0xdbffffffc0000331 0xfdbffffffc000033

def z877 : W := mkw 0x418947efc2004921 0x2418947efc200492 0xf3c1e7ffe030cf3b 0xbf3c1e7ffe030cf3

def z878 : W := mkw 0x499bffefc0000000 0x0499bffefc000000 0xc3c1ffffc0000001 0xbc3c1ffffc000000

def z879 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xaffe67f03fccfc0f 0xfaffe67f03fccfc0

def z880 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0xf00067f3100cfccb 0xaf00067f3100cfcc

def z881 : W := mkw 0x03ad47ca00280288 0x003ad47ca0028028 0xfbffe7ff003c03c1 0xffbffe7ff003c03c

def z882 : W := mkw 0x0264000039000000 0x0026400003900000 0x0ffe00002fc00004 0x50ffe00002fc0000

def z883 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0xf401860c3ff0ff0f 0x9f401860c3ff0ff0

def z884 : W := mkw 0x049897d48652fd25 0xe049897d48652fd2 0x70019ffcc033ff39 0x870019ffcc033ff3

def z885 : W := mkw 0x0b77f8003d120004 0x00b77f8003d12000 0xaffff8003ff30006 0xfaffff8003ff3000

def z886 : W := mkw 0x418b6fefc0000000 0x0418b6fefc000000 0xc3c7ffffc0000001 0xfc3c7ffffc000000

def z887 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x040000001fc03c04 0x0040000001fc03c0

def z888 : W := mkw 0x4ba76d6fc0000000 0x04ba76d6fc000000 0x43c6617fc0000000 0x243c6617fc000000

def z889 : W := mkw 0x044000103b40fd21 0xe044000103b40fd2 0x140000003fc0ff3e 0x0140000003fc0ff3

def z890 : W := mkw 0x42ac07e5c0000000 0x042ac07e5c000000 0x8bfe07f0c0000001 0x78bfe07f0c000000

def z891 : W := mkw 0x4bbfffefc9000000 0x04bbfffefc900000 0xcfffffffcfc00005 0xfcfffffffcfc0000

def z892 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xcfffffffee33cf35 0xfcfffffffee33cf3

def z893 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c7e7ff303cf3cb 0xff3c7e7ff303cf3c

def z894 : W := mkw 0x2040001039ed145a 0x92040001039ed145 0x0000000011cc30c0 0x00000000011cc30c

def z895 : W := mkw 0x06ac07d00b40fc01 0xc06ac07d00b40fc0 0x8ffe07f00fc0fc0d 0x78ffe07f00fc0fc0

def z896 : W := mkw 0x044802903bc5fc51 0xd044802903bc5fc5 0xfc381e80ffcffcff 0xdfc381e80ffcffcf

def z897 : W := mkw 0x03bdd7ce80000000 0x003bdd7ce8000000 0xcbffffffc0000001 0xfcbffffffc000000

def z898 : W := mkw 0x2b75d0003dbf000e 0x02b75d0003dbf000 0xaff9e0003fff0006 0xbaff9e0003fff000

def z899 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c1ff0f303ff3cf 0xff3c1ff0f303ff3c

def z900 : W := mkw 0x2040001039ed145a 0x92040001039ed145 0x3000000011cf3cfe 0x03000000011cf3cf

def z901 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x03c7e77f00000000 0x303c7e77f0000000

def z902 : W := mkw 0x0266282179000000 0x0026628217900000 0xcffe79f3ffc00007 0xfcffe79f3ffc0000

def z903 : W := mkw 0x204000103dff145e 0x9204000103dff145 0x240000003fff30c6 0x0240000003fff30c

def z904 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xffffffffce030c3f 0xfffffffffce030c3

def z905 : W := mkw 0x2b77f804bdbf012e 0x22b77f804bdbf012 0xfffff88cffff0f3f 0xffffff88cffff0f3

def z906 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x2ffff8001fff0004 0xe2ffff8001fff000

def z907 : W := mkw 0x06ec07d03940b400 0xc06ec07d03940b40 0x8ffe07f03fc03007 0x78ffe07f03fc0300

def z908 : W := mkw 0x01c36d3b70edb6d8 0x901c36d3b70edb6d 0x03c79efce1f3cf34 0x503c79efce1f3cf3

def z909 : W := mkw 0x2b75d0003dbf000e 0x02b75d0003dbf000 0xafff80003fff0006 0x7afff80003fff000

def z910 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe07f03fc0f001 0x78ffe07f03fc0f00

def z911 : W := mkw 0x226628003dbf000e 0x0226628003dbf000 0xaffe78003fff0006 0xfaffe78003fff000

def z912 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xfffff983ffff3cff 0xffffff983ffff3cf

def z913 : W := mkw 0x2b75d0003d3a000e 0x02b75d0003d3a000 0x0fff80002ff00004 0x50fff80002ff0000

def z914 : W := mkw 0x6bbfffefc4bf012e 0x26bbfffefc4bf012 0xfbffffffc03f0331 0xffbffffffc03f033

def z915 : W := mkw 0x2d9bffd006fffc0f 0xc2d9bffd006fffc0 0x2001fff0003ffc09 0x82001fff0003ffc0

def z916 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe01f01fc03c0f 0x68ffe01f01fc03c0

def z917 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x840600003fc0fc0e 0x6840600003fc0fc0

def z918 : W := mkw 0x06ec07d4bb40fc01 0xc06ec07d4bb40fc0 0xcffe07fcffc0fc0f 0x7cffe07fcffc0fc0

def z919 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x040000002e00fc08 0x0040000002e00fc0

def z920 : W := mkw 0x0274900039000000 0x0027490003900000 0x8fff98003fc00006 0xf8fff98003fc0000

def z921 : W := mkw 0x4b37f82fc0000000 0x04b37f82fc000000 0xcbfff9ffc0000001 0xfcbfff9ffc000000

def z922 : W := mkw 0x02ac07c009000000 0x002ac07c00900000 0x8ffe07f00fc00005 0x78ffe07f00fc0000

def z923 : W := mkw 0x044000103268fe89 0xc044000103268fe8 0x30000000303cffca 0x030000000303cffc

def z924 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x800007f02000fc0b 0x1800007f02000fc0

def z925 : W := mkw 0x2440001039edb40a 0xc2440001039edb40 0x0000000011cc3000 0x00000000011cc300

def z926 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc39ff8fee33cf3f 0xffc39ff8fee33cf3

def z927 : W := mkw 0x04589294bf7affad 0xe04589294bf7affa 0xfc399e8cffffffff 0xdfc399e8cfffffff

def z928 : W := mkw 0x02e405103940b400 0x802e405103940b40 0x8ffe07f03fc0fc0f 0x78ffe07f03fc0fc0

def z929 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x340000003fc3fc3e 0x0340000003fc3fc3

def z930 : W := mkw 0x2a76b8003d970006 0x02a76b8003d97000 0xaffe78003fcf0006 0xfaffe78003fcf000

def z931 : W := mkw 0x0b3ffac000000000 0x00b3ffac00000000 0x8bfff8f000000000 0xf8bfff8f00000000

def z932 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xdbffffffc00030c9 0xfdbffffffc00030c

def z933 : W := mkw 0x6b77f82ffdbf005e 0x16b77f82ffdbf005 0xfffff80fffff00f6 0xffffff80fffff00f

def z934 : W := mkw 0x06ec07d03b68fe89 0xc06ec07d03b68fe8 0xffff87fc3ffcffcf 0xfffff87fc3ffcffc

def z935 : W := mkw 0x448807ffc2405c01 0xc448807ffc2405c0 0x400007ffc0000c01 0x0400007ffc0000c0

def z936 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0xcbfe67f300000001 0xfcbfe67f30000000

def z937 : W := mkw 0x03ad47ca00000000 0x003ad47ca0000000 0x8bff87fc00000001 0x78bff87fc0000000

def z938 : W := mkw 0x048a2ff142c5fc51 0xd048a2ff142c5fc5 0x70007ff3c00ffcf9 0x870007ff3c00ffcf

def z939 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x0fff80002ff00000 0x10fff80002ff0000

def z940 : W := mkw 0x244000103dffb40e 0xc244000103dffb40 0x240000003fff3006 0x0240000003fff300

def z941 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbffffffe030c301 0xfcbffffffe030c30

def z942 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x800607f00000fc09 0x6800607f00000fc0

def z943 : W := mkw 0x06e405503b40fc01 0xc06e405503b40fc0 0x8ffe01703fc0fc0e 0x78ffe01703fc0fc0

def z944 : W := mkw 0x0018928486124925 0x2001892848612492 0x8c399e8cee33cf3f 0x58c399e8cee33cf3

def z945 : W := mkw 0x066400103b40fc01 0xc066400103b40fc0 0x8ffe01f03fc0fc0f 0x78ffe01f03fc0fc0

def z946 : W := mkw 0x044000103940b400 0xc044000103940b40 0x040000003fc03006 0x0040000003fc0300

def z947 : W := mkw 0x4bbfffefc0280008 0x04bbfffefc028000 0xebffffffc03c0001 0xfebffffffc03c000

def z948 : W := mkw 0x2b77f8003dbfa28e 0x02b77f8003dbfa28 0xaffff8003fffc306 0xfaffff8003fffc30

def z949 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xfbffffffc000000b 0xffbffffffc000000

def z950 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x040000003fc0f000 0x0040000003fc0f00

def z951 : W := mkw 0x06ec07d03b40fc51 0xd06ec07d03b40fc5 0x9ffe07f03fc0fcff 0x79ffe07f03fc0fcf

def z952 : W := mkw 0x06ac07d00b405c01 0xc06ac07d00b405c0 0x0ffe06f00fc00c04 0x50ffe06f00fc00c0

def z953 : W := mkw 0x4ba76d6b4000a280 0x04ba76d6b4000a28 0x53c6677f0000f3c9 0x253c6677f0000f3c

def z954 : W := mkw 0x60c807effdbf000e 0x060c807effdbf000 0x640007ffffff0007 0x0640007ffffff000

def z955 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbffffffc0000c0f 0xfcbffffffc0000c0

def z956 : W := mkw 0x0264000039000000 0x0026400003900000 0xafff80003ff00006 0xfafff80003ff0000

def z957 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c1e78f303cffcf 0xff3c1e78f303cffc

def z958 : W := mkw 0x4baf6feb40000000 0x04baf6feb4000000 0x0bfe677300000000 0x30bfe67730000000

def z959 : W := mkw 0x4bbfffefc0850000 0x04bbfffefc085000 0xfbffffffd1cf30cf 0xffbffffffd1cf30c

def z960 : W := mkw 0x03a5454a00000000 0x003a5454a0000000 0xc3c7e77f00000001 0xbc3c7e77f0000000

def z961 : W := mkw 0x4bbfffefc6124805 0x04bbfffefc612480 0xefffffffee33cc0f 0xfefffffffee33cc0

def z962 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x43c661f3c0000001 0x243c661f3c000000

def z963 : W := mkw 0x0b37f81000c51450 0x90b37f81000c5145 0xbbfff80011cf3cfe 0xfbbfff80011cf3cf

def z964 : W := mkw 0x0153f80034bf000c 0x00153f80034bf000 0xaffff8003fff0006 0xfaffff8003fff000

def z965 : W := mkw 0x2913f82144bf005e 0x12913f82144bf005 0x2001f800c03f0030 0x82001f800c03f003

def z966 : W := mkw 0x2b77f804bdbf012e 0x22b77f804bdbf012 0xfffffe0cffffc33f 0xffffffe0cffffc33

def z967 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x2ffe78003fff0006 0x62ffe78003fff000

def z968 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe07f01fc03c05 0x78ffe07f01fc03c0

def z969 : W := mkw 0x4baf6feb42004801 0x04baf6feb4200480 0x8ffe67f32e00cc0f 0x78ffe67f32e00cc0

def z970 : W := mkw 0x2b77f8003dbfa28e 0x02b77f8003dbfa28 0xfffffe0c3ffff3cf 0xffffffe0c3ffff3c

def z971 : W := mkw 0x42ac07ce80000000 0x042ac07ce8000000 0x8bfe07fc00000001 0x78bfe07fc0000000

def z972 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xf0067ff3f1cffcff 0xff0067ff3f1cffcf

def z973 : W := mkw 0x4abebfe5c0000000 0x04abebfe5c000000 0x0bfe19f0c0000000 0x60bfe19f0c000000

def z974 : W := mkw 0x4bbfffefc0000280 0x04bbfffefc000028 0xdbffffffc00003c1 0xfdbffffffc00003c

def z975 : W := mkw 0x2b75d0003dbf000e 0x02b75d0003dbf000 0x0ff980002ff30004 0x10ff980002ff3000

def z976 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x8bfe07f01000300b 0x78bfe07f01000300

def z977 : W := mkw 0x4abebfe5c0000000 0x04abebfe5c000000 0xcbff9ffcc0000001 0xfcbff9ffcc000000

def z978 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xbffff8003fffc30e 0xfbffff8003fffc30

def z979 : W := mkw 0x0103682140000000 0x0010368214000000 0xc3c7f9f3c0000001 0xfc3c7f9f3c000000

def z980 : W := mkw 0x0a76b80039000000 0x00a76b8003900000 0x8ffe18003fc00006 0x78ffe18003fc0000

def z981 : W := mkw 0x6913f82fc4bf005e 0x16913f82fc4bf005 0x7001f80fc03f00f0 0x87001f80fc03f00f

def z982 : W := mkw 0x048807da0240fe81 0xc048807da0240fe8 0x000007fc0000ff09 0x0000007fc0000ff0

def z983 : W := mkw 0x06ec07d4bb40fd21 0xe06ec07d4bb40fd2 0xfffe1ffcffc3ff3f 0xffffe1ffcffc3ff3

def z984 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c1e78ff03cfffb 0xbf3c1e78ff03cfff

def z985 : W := mkw 0x4b77f82ff9000000 0x04b77f82ff900000 0xcffff80fffc00006 0xfcffff80fffc0000

def z986 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x0bff867c00000000 0x10bff867c0000000

def z987 : W := mkw 0x4abc97c480000000 0x04abc97c48000000 0x8bfe07f000000001 0x78bfe07f00000000

def z988 : W := mkw 0x044000103b40fc51 0xd044000103b40fc5 0x140000003fc0fcfe 0x0140000003fc0fcf

def z989 : W := mkw 0x4b3ffae5c0000000 0x04b3ffae5c000000 0x0bff98f0c0000000 0x50bff98f0c000000

def z990 : W := mkw 0x204228217dbf000e 0x0204228217dbf000 0xe40679f3ffff0007 0xee40679f3ffff000

def z991 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xffff9efcee33cf3f 0xdffff9efcee33cf3

def z992 : W := mkw 0x06ac07c00200e801 0x406ac07c00200e80 0x8bfe07f00000c001 0x78bfe07f00000c00

def z993 : W := mkw 0x6bbfffefcf974927 0x26bbfffefcf97492 0xffffffffeff3cf3f 0xfffffffffeff3cf3

def z994 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe67f33fccfccf 0x78ffe67f33fccfcc

def z995 : W := mkw 0x0365400039280008 0x0036540003928000 0x8fff80003ff00006 0x78fff80003ff0000

def z996 : W := mkw 0x2b77f825fdbf017e 0x32b77f825fdbf017 0xfffff80fffff03f6 0xffffff80fffff03f

def z997 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xaffffe0c3fffc306 0xfaffffe0c3fffc30

def z998 : W := mkw 0x004000103068b6d8 0x9004000103068b6d 0x30000000303cfffa 0x030000000303cfff

def z999 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x000007700000f000 0x0000007700000f00

def z1000 : W := mkw 0x227490003dbf000e 0x0227490003dbf000 0xafff98003fff0006 0xfafff98003fff000

def z1001 : W := mkw 0x0264000039000000 0x0026400003900000 0xfffe1880ffc30c3f 0xffffe1880ffc30c3

def z1002 : W := mkw 0x6bbfffefcd970006 0x06bbfffefcd97000 0xefffffffeff30007 0xfefffffffeff3000

def z1003 : W := mkw 0x226400003d970006 0x0226400003d97000 0x8ffe00003fc30006 0x78ffe00003fc3000

def z1004 : W := mkw 0x06ec07d03b68fe89 0xc06ec07d03b68fe8 0xfffe67f33ffcffcf 0xffffe67f33ffcffc

def z1005 : W := mkw 0x4bbfffefc2004921 0x24bbfffefc200492 0xdfffffffee00cf3f 0xfdfffffffee00cf3

def z1006 : W := mkw 0x004000103040b400 0x8004000103040b40 0x0000000031c0fc0e 0x00000000031c0fc0

def z1007 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x03c607f000000001 0x203c607f00000000

def z1008 : W := mkw 0x6bbfffefc4bf028e 0x06bbfffefc4bf028 0xfbffffffc03f03c1 0xffbffffffc03f03c

def z1009 : W := mkw 0x4bbfffefc0850050 0x14bbfffefc085005 0xcbffffffc0030031 0xfcbffffffc003003

def z1010 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xffffffffee33c331 0xfffffffffee33c33

def z1011 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe00f00fc00c04 0x40ffe00f00fc00c0

def z1012 : W := mkw 0x0264000039000000 0x0026400003900000 0xfffe61033fcc30cf 0xffffe61033fcc30c

def z1013 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0x0ffe79f3ce030c34 0x60ffe79f3ce030c3

def z1014 : W := mkw 0x02ac07c00000a000 0x002ac07c00000a00 0x8bfe07f00000f009 0x78bfe07f00000f00

def z1015 : W := mkw 0x048807d00240fc51 0xd048807d00240fc5 0x100007f00000fcf9 0x0100007f00000fcf

def z1016 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcfffffffee000007 0xfcfffffffee00000

def z1017 : W := mkw 0x4fbfffefc200e801 0x44fbfffefc200e80 0xcbffffffc000c001 0xfcbffffffc000c00

def z1018 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x8fffe0003ffc0006 0x78fffe0003ffc000

def z1019 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x8bffff7f00000000 0xf8bffff7f0000000

def z1020 : W := mkw 0x4bb7fd6fc0000000 0x04bb7fd6fc000000 0xc3c7f9ffc0000001 0xec3c7f9ffc000000

def z1021 : W := mkw 0x0264000039000000 0x0026400003900000 0xaffe60003fcc0006 0xfaffe60003fcc000

def z1022 : W := mkw 0x2b75d0003d3a000e 0x02b75d0003d3a000 0x0fff80003ff00000 0x30fff80003ff0000

def z1023 : W := mkw 0x4bbfffefc028a288 0x04bbfffefc028a28 0xfbffffffc03cf3c9 0xffbffffffc03cf3c

def z1024 : W := mkw 0x044000103fd7fd75 0xf044000103fd7fd7 0x340000003ffffffe 0x0340000003ffffff

def z1025 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xfffff8033fff00c6 0xffffff8033fff00c

def z1026 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xfbffffffc00c00c1 0xffbffffffc00c00c

def z1027 : W := mkw 0x2b77f80a3dbf028e 0x02b77f80a3dbf028 0xaffff8033fff00c6 0xfaffff8033fff00c

def z1028 : W := mkw 0x2bbfffc004bf000e 0x02bbfffc004bf000 0xabfffff0003f0001 0xfabfffff0003f000

def z1029 : W := mkw 0x4bbfffefc4120004 0x04bbfffefc412000 0xffffffffee33c30f 0xfffffffffee33c30

def z1030 : W := mkw 0x4bbfffefc0280288 0x04bbfffefc028028 0xfbffffffd03c33cb 0xffbffffffd03c33c

def z1031 : W := mkw 0x044000103b68fc09 0xc044000103b68fc0 0x240000003ffcfc0e 0x0240000003ffcfc0

def z1032 : W := mkw 0x01836d2b40000000 0x001836d2b4000000 0x03c6617300000000 0x203c661730000000

def z1033 : W := mkw 0x0266282179850050 0x1026628217985005 0xfffe7803ffcf00f6 0xffffe7803ffcf00f

def z1034 : W := mkw 0x2b77f8217dbf000e 0x02b77f8217dbf000 0xfffff9f3ffff30cf 0xffffff9f3ffff30c

def z1035 : W := mkw 0x0018928486124925 0x2001892848612492 0x7c399e8cee33cf39 0x97c399e8cee33cf3

def z1036 : W := mkw 0x2b37f8000dbf000e 0x02b37f8000dbf000 0xaffff8000fff0004 0xfaffff8000fff000

def z1037 : W := mkw 0x4bad47ca00000000 0x04bad47ca0000000 0x8bfe07f000000001 0x78bfe07f00000000

def z1038 : W := mkw 0x022c02c000000000 0x0022c02c00000000 0x8bfe00f000000000 0x78bfe00f00000000

def z1039 : W := mkw 0x026c02c039000000 0x0026c02c03900000 0x8ffe00f03fc00006 0x78ffe00f03fc0000

def z1040 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x2ff9f8003fff0006 0x92ff9f8003fff000

def z1041 : W := mkw 0x06ec07da3b40fe81 0xc06ec07da3b40fe8 0x8ffe07fc3fc0ff0f 0x78ffe07fc3fc0ff0

def z1042 : W := mkw 0x42ac07eb40000000 0x042ac07eb4000000 0x8bfe07f300000001 0x78bfe07f30000000

def z1043 : W := mkw 0x6bbfffefc6bf492f 0x26bbfffefc6bf492 0xffffffffee3fcf3f 0xfffffffffee3fcf3

def z1044 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xaffe78001fcf0006 0xeaffe78001fcf000

def z1045 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xffff9ffcfff3ff3f 0xfffff9ffcfff3ff3

def z1046 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xfffffe8cffffcf3f 0xffffffe8cffffcf3

def z1047 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x0bfe077000000000 0x30bfe07700000000

def z1048 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x8ffff8001fcf0004 0xf8ffff8001fcf000

def z1049 : W := mkw 0x2a66280039850002 0x02a6628003985000 0x8ffe00003fc00006 0x78ffe00003fc0000

def z1050 : W := mkw 0x40c807eff028a288 0x040c807eff028a28 0x700007fff03cf3cb 0x0700007fff03cf3c

def z1051 : W := mkw 0x2913f82144bf005e 0x12913f82144bf005 0x2001f803003f00c0 0x82001f803003f00c

def z1052 : W := mkw 0x6bbfffefc4bf000e 0x06bbfffefc4bf000 0xefffffffee3f0007 0xfefffffffee3f000

def z1053 : W := mkw 0x2b77f8217dbf005e 0x12b77f8217dbf005 0xfffff9f3ffff00f7 0xffffff9f3ffff00f

def z1054 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe07703fc0f006 0x78ffe07703fc0f00

def z1055 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xfbffffffe033cf3f 0xffbffffffe033cf3

def z1056 : W := mkw 0x02ae2fe140850050 0x102ae2fe14085005 0xfbfe7ff3c00f00f1 0xffbfe7ff3c00f00f

def z1057 : W := mkw 0x4bbfffefc612eba5 0x24bbfffefc612eba 0xffffffffee33ffff 0xfffffffffee33fff

def z1058 : W := mkw 0x06ac07d00b405c01 0xc06ac07d00b405c0 0x8ffe07f02fc0cc0f 0x78ffe07f02fc0cc0

def z1059 : W := mkw 0x0018928486124925 0x2001892848612492 0xcc399e8cee33cf35 0xdcc399e8cee33cf3

def z1060 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x73c1e70f103cf3c9 0xa73c1e70f103cf3c

def z1061 : W := mkw 0x408807ffc2405d71 0xb408807ffc2405d7 0x500007ffc000fff9 0x0500007ffc000fff

def z1062 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc39fe8cfe3fcf3f 0xffc39fe8cfe3fcf3

def z1063 : W := mkw 0x4ba76d6b40850000 0x04ba76d6b4085000 0xa3c6797311cf0006 0xea3c6797311cf000

def z1064 : W := mkw 0x02ae2fc000850000 0x002ae2fc00085000 0xabfe7ff011cf0007 0xfabfe7ff011cf000

def z1065 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x0bfe06f000000000 0x50bfe06f00000000

def z1066 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x0bfe01f000000000 0x60bfe01f00000000

def z1067 : W := mkw 0x42ac07efc2004921 0x242ac07efc200492 0xdffe07ffee00cf3f 0x7dffe07ffee00cf3

def z1068 : W := mkw 0x02bc97c480000000 0x002bc97c48000000 0x8bff87fc00000001 0x78bff87fc0000000

def z1069 : W := mkw 0x4ba76d6b4000a280 0x04ba76d6b4000a28 0x03c66173000030c0 0x203c66173000030c

def z1070 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0xf3c66173100c30cb 0xaf3c66173100c30c

def z1071 : W := mkw 0x02ae2fe140000000 0x002ae2fe14000000 0x8bfe1ff0c0000001 0x78bfe1ff0c000000

def z1072 : W := mkw 0x4abebfe5c0000000 0x04abebfe5c000000 0xcbfe7ff3c0000001 0xfcbfe7ff3c000000

def z1073 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x8bfe617300000000 0x78bfe61730000000

def z1074 : W := mkw 0x02bc97c484120124 0x202bc97c48412012 0xfbff9ffcc0330331 0xffbff9ffcc033033

def z1075 : W := mkw 0x2b77f8003dbfa00e 0x02b77f8003dbfa00 0xaffff8003ffff00e 0xfaffff8003ffff00

def z1076 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbfe79f3c0000001 0xecbfe79f3c000000

def z1077 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc3f9e8cfff3cf3f 0xffc3f9e8cfff3cf3

def z1078 : W := mkw 0x044000103940b400 0xc044000103940b40 0x0000000011c03c0e 0x00000000011c03c0

def z1079 : W := mkw 0x4bbdd7ce80000000 0x04bbdd7ce8000000 0x0bff877c00000000 0x30bff877c0000000

def z1080 : W := mkw 0x02a4054000000000 0x002a405400000000 0x83c601f000000001 0x683c601f00000000

def z1081 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x0000000011c0fc08 0x00000000011c0fc0

def z1082 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xfff9e70f3e3cf3cf 0xffff9e70f3e3cf3c

def z1083 : W := mkw 0x4abebfe5c6124925 0x24abebfe5c612492 0x8ffe1ff0ee03cc3f 0x78ffe1ff0ee03cc3

def z1084 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x83c1e70f303cf3cb 0x383c1e70f303cf3c

def z1085 : W := mkw 0x4bbdd7ce86124925 0x24bbdd7ce8612492 0xffff9ffcee33cf3f 0xfffff9ffcee33cf3

def z1086 : W := mkw 0x4bbfffeb40000000 0x04bbfffeb4000000 0x8bfffff300000001 0xf8bfffff30000000

def z1087 : W := mkw 0x448807ffc240fd21 0xe448807ffc240fd2 0x500007ffc000ff39 0x0500007ffc000ff3

def z1088 : W := mkw 0x04c807d03b40fc01 0xc04c807d03b40fc0 0x040006003fc0fc0e 0x0040006003fc0fc0

def z1089 : W := mkw 0x2b75d0003dbf000e 0x02b75d0003dbf000 0xaff998003fff0006 0xdaff998003fff000

def z1090 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xffffffffce330f35 0xfffffffffce330f3

def z1091 : W := mkw 0x42bc97efc6124925 0x242bc97efc612492 0xffff9fffee33cf3f 0xfffff9fffee33cf3

def z1092 : W := mkw 0x2b77f804bdbf000e 0x02b77f804bdbf000 0xeffff80cffff0006 0xfeffff80cffff000

def z1093 : W := mkw 0x02ac07c480000000 0x002ac07c48000000 0xcbfe07fcc0000001 0x7cbfe07fcc000000

def z1094 : W := mkw 0x044802903b40fc01 0xc044802903b40fc0 0x040006803fc0fc0f 0x0040006803fc0fc0

def z1095 : W := mkw 0x4bbfffefc000a280 0x04bbfffefc000a28 0xfbffffffe030f3cb 0xffbffffffe030f3c

def z1096 : W := mkw 0x02ac07c006124925 0x202ac07c00612492 0xbffe07f02e33cf3f 0x7bffe07f02e33cf3

def z1097 : W := mkw 0x6bbfffefcf974927 0x26bbfffefcf97492 0xcfffffffcfc30c35 0xfcfffffffcfc30c3

def z1098 : W := mkw 0x00822d2140000000 0x000822d214000000 0xc3c67ff3c0000001 0xfc3c67ff3c000000

def z1099 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x2fffe0003fff0006 0x32fffe0003fff000

def z1100 : W := mkw 0x2be76d3b79edb6da 0x92be76d3b79edb6d 0x03c6617311cc30c0 0x203c6617311cc30c

def z1101 : W := mkw 0x026400003d120004 0x0026400003d12000 0xaffe00003ff30006 0x7affe00003ff3000

def z1102 : W := mkw 0x06ec07d03b68fc09 0xc06ec07d03b68fc0 0xaffe07f03ffcfc0f 0x7affe07f03ffcfc0

def z1103 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x4bff9fffc0000001 0x54bff9fffc000000

def z1104 : W := mkw 0x0bbfffc486124925 0x20bbfffc48612492 0xfffffffcee33cf3f 0xffffffffcee33cf3

def z1105 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xbffe07f03fc3fc3f 0x7bffe07f03fc3fc3

def z1106 : W := mkw 0x2b67680039ad000a 0x02b67680039ad000 0x0ffe60003fcc0000 0x30ffe60003fcc000

def z1107 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x8ffe78003fcf0006 0x78ffe78003fcf000

def z1108 : W := mkw 0x4ba5454a00000000 0x04ba5454a0000000 0x03c6017000000000 0x203c601700000000

def z1109 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xc3c1e70f303cf3c1 0xbc3c1e70f303cf3c

def z1110 : W := mkw 0x226400003d3a000e 0x0226400003d3a000 0x8ffe00003ff00006 0x78ffe00003ff0000

def z1111 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xdffe07fc3fc0ff0f 0x7dffe07fc3fc0ff0

def z1112 : W := mkw 0x06ec07d4bb40fd21 0xe06ec07d4bb40fd2 0x8ffe07f0ffc0fc3f 0x78ffe07f0ffc0fc3

def z1113 : W := mkw 0x2a36b8000d970006 0x02a36b8000d97000 0x8ffe18000fc30004 0x78ffe18000fc3000

def z1114 : W := mkw 0x6913f82fc4970006 0x06913f82fc497000 0x4001f80fc0030000 0x84001f80fc003000

def z1115 : W := mkw 0x2b77f80a3dbf028e 0x02b77f80a3dbf028 0xaffff80c3fff0306 0xfaffff80c3fff030

def z1116 : W := mkw 0x0264000039000000 0x0026400003900000 0x8ffe01f03fc00007 0x78ffe01f03fc0000

def z1117 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xfffff80c3fff0306 0xffffff80c3fff030

def z1118 : W := mkw 0x4b3ffaefc0000000 0x04b3ffaefc000000 0xcbfff8ffc0000000 0xfcbfff8ffc000000

def z1119 : W := mkw 0x4baf6feb40000000 0x04baf6feb4000000 0xcbfe7ff3c0000001 0xfcbfe7ff3c000000

def z1120 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0xcbff87fc00000001 0xfcbff87fc0000000

def z1121 : W := mkw 0x02a4054000000000 0x002a405400000000 0x8bfe017000000000 0x78bfe01700000000

def z1122 : W := mkw 0x0b27682140000000 0x00b2768214000000 0xc3c679f3c0000001 0xec3c679f3c000000

def z1123 : W := mkw 0x244000103fff5c0f 0xc244000103fff5c0 0x240000003fff0c06 0x0240000003fff0c0

def z1124 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xdfffffffce03cf3d 0xfdfffffffce03cf3

def z1125 : W := mkw 0x2b37f8000d970006 0x02b37f8000d97000 0xaffff8001fcf0006 0xfaffff8001fcf000

def z1126 : W := mkw 0x2a76b8003d970006 0x02a76b8003d97000 0x0ffe18002fc30004 0x50ffe18002fc3000

def z1127 : W := mkw 0x0224000000000000 0x0022400000000000 0x8bfe01f000000001 0x78bfe01f00000000

def z1128 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xf007f9ffd1ff3fff 0xef007f9ffd1ff3ff

def z1129 : W := mkw 0x245892903ffffc0f 0xc245892903ffffc0 0xac399e803ffffc0f 0xdac399e803ffffc0

def z1130 : W := mkw 0x226400003dbf000e 0x0226400003dbf000 0x2ff800003fff0006 0x12ff800003fff000

def z1131 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c1ff8ff03cf3cb 0xff3c1ff8ff03cf3c

def z1132 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x03c6007000000000 0x003c600700000000

def z1133 : W := mkw 0x6ba76d6b49850002 0x06ba76d6b4985000 0x03c6617301c00000 0x203c6617301c0000

def z1134 : W := mkw 0x044802903b40fc01 0xc044802903b40fc0 0x0c3806003fc0fc0e 0x10c3806003fc0fc0

def z1135 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x8ffe07f02e000007 0x78ffe07f02e00000

def z1136 : W := mkw 0x02ac07c002004801 0x002ac07c00200480 0x8ffe07f02e00c001 0x78ffe07f02e00c00

def z1137 : W := mkw 0x6b77f82ffdbf000e 0x06b77f82ffdbf000 0xeffff9ffffff0007 0xfeffff9ffffff000

def z1138 : W := mkw 0x4bbfffefc4120004 0x04bbfffefc412000 0xcfffffffce030005 0xfcfffffffce03000

def z1139 : W := mkw 0x02a62d6140000000 0x002a62d614000000 0x03c6617300000000 0x203c661730000000

def z1140 : W := mkw 0x0375d0003d3a000c 0x00375d0003d3a000 0xaffff8003fff0006 0xfaffff8003fff000

def z1141 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xfbffffffc0300301 0xffbffffffc030030

def z1142 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe07f01fc0fc0d 0x60ffe07f01fc0fc0

def z1143 : W := mkw 0x03ad47c000000000 0x003ad47c00000000 0x8bffe7f000000001 0xf8bffe7f00000000

def z1144 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xfffffffffe3fffff 0xffffffffffe3ffff

def z1145 : W := mkw 0x0018928486124925 0x2001892848612492 0xac399e8cee33cf36 0xdac399e8cee33cf3

def z1146 : W := mkw 0x0264000039850000 0x0026400003985000 0xaffe00003fcf0006 0x7affe00003fcf000

def z1147 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xafff87f03ff0fc0f 0xfafff87f03ff0fc0

def z1148 : W := mkw 0x06ec07d03b40fe81 0xc06ec07d03b40fe8 0x9ffe07f03fc0ffcf 0x79ffe07f03fc0ffc

def z1149 : W := mkw 0x0bbfffe140000000 0x00bbfffe14000000 0xcbfffff3c0000001 0xfcbfffff3c000000

def z1150 : W := mkw 0x044000103940b400 0xc044000103940b40 0x0000000031c0f00a 0x00000000031c0f00

def z1151 : W := mkw 0x048807fb4240fed1 0xd048807fb4240fed 0x500007ffc000fff9 0x0500007ffc000fff

def z1152 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbff9efcc0000001 0xdcbff9efcc000000

def z1153 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x0bffffffc0000000 0x70bffffffc000000

def z1154 : W := mkw 0x0266280039000000 0x0026628003900000 0x8ffe78003fc00006 0xf8ffe78003fc0000

def z1155 : W := mkw 0x4ba76d6b40280288 0x04ba76d6b4028028 0x73c7e17f003c03c0 0xa73c7e17f003c03c

def z1156 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x83c7e17300000000 0xb83c7e1730000000

def z1157 : W := mkw 0x4b37f86140000000 0x04b37f8614000000 0x8bfff87000000000 0xf8bfff8700000000

def z1158 : W := mkw 0x4bb7fd6b40000000 0x04bb7fd6b4000000 0xcbffff7f00000001 0xfcbffff7f0000000

def z1159 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x83c6797300000000 0xe83c679730000000

def z1160 : W := mkw 0x418947efc0000000 0x0418947efc000000 0x43c187ffc0000001 0x143c187ffc000000

def z1161 : W := mkw 0x048807f14240fc01 0xc048807f14240fc0 0x400007f3c000fc09 0x0400007f3c000fc0

def z1162 : W := mkw 0x4baf6feb40000000 0x04baf6feb4000000 0xcbffe7ff00000001 0xfcbffe7ff0000000

def z1163 : W := mkw 0x0440001039c5b450 0xd0440001039c5b45 0x0000000011cc30c0 0x00000000011cc30c

def z1164 : W := mkw 0x03ad47ca02004801 0x003ad47ca0200480 0xffffe7ff2e30cf0f 0xfffffe7ff2e30cf0

def z1165 : W := mkw 0x6b77f825fdbf000e 0x06b77f825fdbf000 0xaffff800ffff0006 0xfaffff800ffff000

def z1166 : W := mkw 0x06ec07d03b405c01 0xc06ec07d03b405c0 0x8ffe07f03fc00c07 0x78ffe07f03fc00c0

def z1167 : W := mkw 0x4bb7fd6b40000000 0x04bb7fd6b4000000 0x03c7f97300000000 0xa03c7f9730000000

def z1168 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xffffff0f3ffff3cf 0xfffffff0f3ffff3c

def z1169 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xdbffffffc000c309 0xfdbffffffc000c30

def z1170 : W := mkw 0x04c807d03240fc01 0xc04c807d03240fc0 0x000007f03000fc0b 0x0000007f03000fc0

def z1171 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x4bffff7fc0000000 0xb4bffff7fc000000

def z1172 : W := mkw 0x4bbfffefc2004801 0x04bbfffefc200480 0xcbffffffc000cc09 0xfcbffffffc000cc0

def z1173 : W := mkw 0x2b6f6a84bbad492b 0x22b6f6a84bbad492 0x53c6668cd1cccf39 0x253c6668cd1cccf3

def z1174 : W := mkw 0x6ba76d6b40ad000a 0x06ba76d6b40ad000 0x03c66173000c0000 0x203c66173000c000

def z1175 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x840000803fc0fc0f 0x4840000803fc0fc0

def z1176 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x500007fc0000ff09 0x0500007fc0000ff0

def z1177 : W := mkw 0x048807d48240fd21 0xe048807d48240fd2 0x000007f0c000fc39 0x0000007f0c000fc3

def z1178 : W := mkw 0x0bbfffca00000000 0x00bbfffca0000000 0xcbffffff00000001 0xfcbffffff0000000

def z1179 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x03c679f3c0000000 0x603c679f3c000000

def z1180 : W := mkw 0x6b77f8617dbf000e 0x06b77f8617dbf000 0xaffff8703fff0006 0xfaffff8703fff000

def z1181 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0xc3c7ffffc0000001 0xfc3c7ffffc000000

def z1182 : W := mkw 0x044000103b40fe81 0xc044000103b40fe8 0x140000003fc0ffce 0x0140000003fc0ffc

def z1183 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xfbfffffff03cf3cb 0xffbfffffff03cf3c

def z1184 : W := mkw 0x0264001039401400 0x8026400103940140 0x8ffe01703fc03006 0x78ffe01703fc0300

def z1185 : W := mkw 0x0664005039401400 0xc066400503940140 0x8ffe00703fc00006 0x78ffe00703fc0000

def z1186 : W := mkw 0x02ec07d039401400 0x802ec07d03940140 0x8ffe07f03fc03c0f 0x78ffe07f03fc03c0

def z1187 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x53c1e70f303cf3c9 0x353c1e70f303cf3c

def z1188 : W := mkw 0x027490003d120004 0x0027490003d12000 0x8ffe18003fc30006 0x78ffe18003fc3000

def z1189 : W := mkw 0x01c1450a3928a288 0x001c1450a3928a28 0xf7c1e70f3ffcf3cf 0xbf7c1e70f3ffcf3c

def z1190 : W := mkw 0x06ac07c00b004801 0x406ac07c00b00480 0x8ffe07f00e000001 0x78ffe07f00e00000

def z1191 : W := mkw 0x0b37f82140000000 0x00b37f8214000000 0x8bfff8f0c0000000 0xf8bfff8f0c000000

def z1192 : W := mkw 0x02ac07c002004801 0x002ac07c00200480 0x8ffe07f00e000c05 0x78ffe07f00e000c0

def z1193 : W := mkw 0x6bbfffefc0ad000a 0x06bbfffefc0ad000 0xcbffffffc00c0001 0xfcbffffffc00c000

def z1194 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0xf3c679f3c0030c3f 0xef3c679f3c0030c3

def z1195 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x8bfffefcc0000000 0xf8bfffefcc000000

def z1196 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0x0fff9efcee33cf34 0x50fff9efcee33cf3

def z1197 : W := mkw 0x46ec07debb40fc01 0xc46ec07debb40fc0 0x8ffe07fc3fc0fc0f 0x78ffe07fc3fc0fc0

def z1198 : W := mkw 0x4bbfffefc200eba1 0x24bbfffefc200eba 0xdbffffffc000fff9 0xfdbffffffc000fff

def z1199 : W := mkw 0x6bb7fd6b44bf000e 0x06bb7fd6b44bf000 0x23c7f973003f0000 0xa23c7f973003f000

def z1200 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe07f02fc0cc05 0x78ffe07f02fc0cc0

def z1201 : W := mkw 0x0baf6fc000000000 0x00baf6fc00000000 0x8bfe67f000000001 0x78bfe67f00000000

def z1202 : W := mkw 0x6bbfffefc4970006 0x06bbfffefc497000 0xcbffffffc0030001 0xfcbffffffc003000

def z1203 : W := mkw 0x044000103b405c01 0xc044000103b405c0 0x040000003fc00c06 0x0040000003fc00c0

def z1204 : W := mkw 0x044000103bc5fc51 0xd044000103bc5fc5 0x040000003fccfcce 0x0040000003fccfcc

def z1205 : W := mkw 0x048807d00240fe81 0xc048807d00240fe8 0x100007f00000ffc9 0x0100007f00000ffc

def z1206 : W := mkw 0x0040001030edb6d8 0x90040001030edb6d 0x3000000011cf3cfe 0x03000000011cf3cf

def z1207 : W := mkw 0x4bbfffefc000a280 0x04bbfffefc000a28 0xcbffffffc00030c1 0xfcbffffffc00030c

def z1208 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x8c3800003fc0fc0e 0x58c3800003fc0fc0

def z1209 : W := mkw 0x0b3ffaa5c6124925 0x20b3ffaa5c612492 0xffffffffee33cf3f 0xfffffffffee33cf3

def z1210 : W := mkw 0x6913f825c4bf000e 0x06913f825c4bf000 0x2001f800c03f0000 0x82001f800c03f000

def z1211 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0xcbfe1ff0c0000001 0xfcbfe1ff0c000000

def z1212 : W := mkw 0x019bffafc6124925 0x2019bffafc612492 0xffffffffee33cf3f 0xfffffffffee33cf3

def z1213 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xdfffffffee30cf39 0xfdfffffffee30cf3

def z1214 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbffffffd000300b 0xfcbffffffd000300

def z1215 : W := mkw 0x008807c000000000 0x0008807c00000000 0x83c007f000000001 0x383c007f00000000

def z1216 : W := mkw 0x2953f8317dff145e 0x92953f8317dff145 0x7401f803ffff3cfe 0x87401f803ffff3cf

def z1217 : W := mkw 0x0b37f82140000000 0x00b37f8214000000 0x8bfff97300000000 0xf8bfff9730000000

def z1218 : W := mkw 0x4ba76d6b40850050 0x14ba76d6b4085005 0x73c67973c00f00f0 0xa73c67973c00f00f

def z1219 : W := mkw 0x2b77f8217dbf005e 0x12b77f8217dbf005 0xaffff800ffff0036 0xfaffff800ffff003

def z1220 : W := mkw 0x2151d0003dbf000e 0x02151d0003dbf000 0xaff9f8003fff0006 0xfaff9f8003fff000

def z1221 : W := mkw 0x6bbfffefcdbf000e 0x06bbfffefcdbf000 0xefffffffcfff0005 0xfefffffffcfff000

def z1222 : W := mkw 0x0224000009000000 0x0022400000900000 0x8ffe00000fc00004 0x78ffe00000fc0000

def z1223 : W := mkw 0x42a4056b40000000 0x042a4056b4000000 0x03c6017300000000 0x203c601730000000

def z1224 : W := mkw 0x2a76b8003dbf000e 0x02a76b8003dbf000 0xaffe18003fff0006 0x7affe18003fff000

def z1225 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c7e70f31fcf3cf 0xff3c7e70f31fcf3c

def z1226 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x0ffe18000fc30004 0x40ffe18000fc3000

def z1227 : W := mkw 0x4bbfffefc4120004 0x04bbfffefc412000 0xcfffffffee300001 0xfcfffffffee30000

def z1228 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe01f03fc03c06 0x78ffe01f03fc03c0

def z1229 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xfffe7ff3ffcffcff 0xffffe7ff3ffcffcf

def z1230 : W := mkw 0x04c0051a3b40fe81 0xc04c0051a3b40fe8 0x5400070f3fc0ffcf 0x05400070f3fc0ffc

def z1231 : W := mkw 0x018947ca00000000 0x0018947ca0000000 0xc3c1e7ff00000001 0xbc3c1e7ff0000000

def z1232 : W := mkw 0x0bb7fd4000000000 0x00bb7fd400000000 0x8bfff97000000000 0xf8bfff9700000000

def z1233 : W := mkw 0x2b77f8003dbfa28e 0x02b77f8003dbfa28 0xfffff9033ffff3cf 0xffffff9033ffff3c

def z1234 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x040000002fc0cc04 0x0040000002fc0cc0

def z1235 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xffffe7ff3ffcffcf 0xfffffe7ff3ffcffc

def z1236 : W := mkw 0x4bbdd7ce80000000 0x04bbdd7ce8000000 0xcbff9ffcc0000001 0xfcbff9ffcc000000

def z1237 : W := mkw 0x0b37f80000000000 0x00b37f8000000000 0x8bfff9f000000001 0xf8bfff9f00000000

def z1238 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe06f03fc0cc06 0x78ffe06f03fc0cc0

def z1239 : W := mkw 0x4bbfffefc6974925 0x24bbfffefc697492 0xffffffffffffcf3f 0xfffffffffffffcf3

def z1240 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xcffe1ff0ffc0fc0f 0xfcffe1ff0ffc0fc0

def z1241 : W := mkw 0x2a7490003d120006 0x02a7490003d12000 0x8ffe00003fc00006 0x78ffe00003fc0000

def z1242 : W := mkw 0x42bc97efc0000000 0x042bc97efc000000 0xcbff9fffc0000001 0xfcbff9fffc000000

def z1243 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xefffffffee33c307 0xfefffffffee33c30

def z1244 : W := mkw 0x0541401a3b68fe89 0xc0541401a3b68fe8 0x7401e00f3ffcffce 0x87401e00f3ffcffc

def z1245 : W := mkw 0x4a3ebae5c0000000 0x04a3ebae5c000000 0x8bfe18f0c0000000 0x78bfe18f0c000000

def z1246 : W := mkw 0x204000103dffb6de 0x9204000103dffb6d 0x340000003ffffffe 0x0340000003ffffff

def z1247 : W := mkw 0x4bbfffefc0850050 0x14bbfffefc085005 0xfbffffffd00f30fb 0xffbffffffd00f30f

def z1248 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xa3c1e70f303cf3c2 0xba3c1e70f303cf3c

def z1249 : W := mkw 0x4fbfffefcb004801 0x44fbfffefcb00480 0xcfffffffce000001 0xfcfffffffce00000

def z1250 : W := mkw 0x0264000039000000 0x0026400003900000 0xaffe18003fc30006 0xfaffe18003fc3000

def z1251 : W := mkw 0x4bbfffefc4970004 0x04bbfffefc497000 0xefffffffffff0007 0xfefffffffffff000

def z1252 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xf00679f3f1ffffff 0xef00679f3f1fffff

def z1253 : W := mkw 0x04589294bf52fd25 0xe04589294bf52fd2 0x0c381880ffc3fc3e 0x40c381880ffc3fc3

def z1254 : W := mkw 0x4bbfffefc2004801 0x04bbfffefc200480 0xffffffffee30cf0f 0xfffffffffee30cf0

def z1255 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x0bfe18f0c0000000 0x40bfe18f0c000000

def z1256 : W := mkw 0x0040001030edb6d8 0x90040001030edb6d 0xf0019e8cf1ffffff 0xdf0019e8cf1fffff

def z1257 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x840001003fc0fc0f 0x2840001003fc0fc0

def z1258 : W := mkw 0x6bbfffefc9850002 0x06bbfffefc985000 0xcbffffffc1c00001 0xfcbffffffc1c0000

def z1259 : W := mkw 0x244000103fd7fc07 0xc244000103fd7fc0 0x040000003fc3fc0e 0x0040000003fc3fc0

def z1260 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x8bfe07f000000c0f 0x78bfe07f000000c0

def z1261 : W := mkw 0x019bffafc0000000 0x0019bffafc000000 0xcbffffffc0000001 0xfcbffffffc000000

def z1262 : W := mkw 0x2264000039ad000a 0x02264000039ad000 0x8ffe00003fcc0006 0x78ffe00003fcc000

def z1263 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xaffff9003fff300f 0xfaffff9003fff300

def z1264 : W := mkw 0x044000103968b688 0xc044000103968b68 0x3000000031fcf3ca 0x03000000031fcf3c

def z1265 : W := mkw 0x02ac07c002004801 0x002ac07c00200480 0x8bfe07f00000cc09 0x78bfe07f00000cc0

def z1266 : W := mkw 0x448807de8240fc01 0xc448807de8240fc0 0x000007fc0000fc09 0x0000007fc0000fc0

def z1267 : W := mkw 0x4bb7fd6b40000000 0x04bb7fd6b4000000 0x0bfe797300000000 0x60bfe79730000000

def z1268 : W := mkw 0x6bbfffefc4bf005e 0x16bbfffefc4bf005 0xfbffffffc03f00f1 0xffbffffffc03f00f

def z1269 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xfbffffffc0030031 0xffbffffffc003003

def z1270 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x03c66173100c30c0 0x203c66173100c30c

def z1271 : W := mkw 0x4baf6feb40000000 0x04baf6feb4000000 0x0bfe61f300000000 0x60bfe61f30000000

def z1272 : W := mkw 0x0018928486124925 0x2001892848612492 0x7c399e0cee33cf3e 0x97c399e0cee33cf3

def z1273 : W := mkw 0x4bbfffce80000000 0x04bbfffce8000000 0x8bfffffc00000001 0xf8bfffffc0000000

def z1274 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbffffffc0030c35 0xfcbffffffc0030c3

def z1275 : W := mkw 0x0010900004120004 0x0001090000412000 0xfc399e8cee33cf3f 0xdfc399e8cee33cf3

def z1276 : W := mkw 0x4bbdd7efc0000000 0x04bbdd7efc000000 0xcbf9e7ffc0000001 0xbcbf9e7ffc000000

def z1277 : W := mkw 0x0b37f82144120004 0x00b37f8214412000 0xfffff9f3ee330c3f 0xffffff9f3ee330c3

def z1278 : W := mkw 0x4bbfffefc43a03ac 0x24bbfffefc43a03a 0xfbffffffc03f03f1 0xffbffffffc03f03f

def z1279 : W := mkw 0x4bbfffefc2004801 0x04bbfffefc200480 0xcfffffffee00c001 0xfcfffffffee00c00

def z1280 : W := mkw 0x01836d2b40ad02d8 0x101836d2b40ad02d 0xf3c7ffffc03f03f1 0xff3c7ffffc03f03f

def z1281 : W := mkw 0x4bbdd7efc0000000 0x04bbdd7efc000000 0x0bf9877f00000000 0x10bf9877f0000000

def z1282 : W := mkw 0x4baf6feb40000000 0x04baf6feb4000000 0x03c667f300000001 0x203c667f30000000

def z1283 : W := mkw 0x2abebfc00d970006 0x02abebfc00d97000 0x8ffe1ff00fc30005 0x78ffe1ff00fc3000

def z1284 : W := mkw 0x43ad47efc0000000 0x043ad47efc000000 0xcbffe7ffc0000001 0xfcbffe7ffc000000

def z1285 : W := mkw 0x4bbdd7efc6124925 0x24bbdd7efc612492 0xfff99fffee33cf3f 0xdfff99fffee33cf3

def z1286 : W := mkw 0x6b77f82b7dbf000e 0x06b77f82b7dbf000 0xaffff8033fff0006 0xfaffff8033fff000

def z1287 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbffffffd00c30c1 0xfcbffffffd00c30c

def z1288 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0xf00187fc2030ff0b 0x9f00187fc2030ff0

def z1289 : W := mkw 0x066c02d03b405c01 0xc066c02d03b405c0 0x0ffe00f02fc00c04 0x50ffe00f02fc00c0

def z1290 : W := mkw 0x0365400a39280288 0x00365400a3928028 0xffffe00f3ffc03c6 0xfffffe00f3ffc03c

def z1291 : W := mkw 0x2b77f8003d970006 0x02b77f8003d97000 0x8ffff8003fc30006 0xf8ffff8003fc3000

def z1292 : W := mkw 0x04c807d03268fe89 0xc04c807d03268fe8 0x300007f0303cffcb 0x0300007f0303cffc

def z1293 : W := mkw 0x2b75d0003d3a000e 0x02b75d0003d3a000 0xafff98003ff30006 0xfafff98003ff3000

def z1294 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x0bf807f000000001 0x10bf807f00000000

def z1295 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbffffffd1c00007 0xfcbffffffd1c0000

def z1296 : W := mkw 0x4199d7efc6124925 0x24199d7efc612492 0xfff9ffffee33cf3f 0xffff9ffffee33cf3

def z1297 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xebffffffd00c0003 0xfebffffffd00c000

def z1298 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe06702fc0c000 0x10ffe06702fc0c00

def z1299 : W := mkw 0x2b77f8003dbfa28e 0x02b77f8003dbfa28 0xaffff8003fff30c6 0xfaffff8003fff30c

def z1300 : W := mkw 0x6b77f82ffdbf028e 0x06b77f82ffdbf028 0xfffff80fffff03c6 0xffffff80fffff03c

def z1301 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x43c7ffffc0000001 0xa43c7ffffc000000

def z1302 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x43c67973c0000000 0xa43c67973c000000

def z1303 : W := mkw 0x2b37f8000d970006 0x02b37f8000d97000 0x0fff98000fc30004 0x50fff98000fc3000

def z1304 : W := mkw 0x04480294bb40fd21 0xe04480294bb40fd2 0x5400068cffc0ff3f 0x05400068cffc0ff3

def z1305 : W := mkw 0x066c02d03b405c01 0xc066c02d03b405c0 0x8ffe01f03fc03c0f 0x78ffe01f03fc03c0

def z1306 : W := mkw 0x4a3ebaf5c6d75d75 0xb4a3ebaf5c6d75d7 0x0c3e18f0cfc30c34 0x40c3e18f0cfc30c3

def z1307 : W := mkw 0x06ac07d00b405c01 0xc06ac07d00b405c0 0x0ffe01f00fc00c04 0x60ffe01f00fc00c0

def z1308 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x8bfe07f02000c00b 0x78bfe07f02000c00

def z1309 : W := mkw 0x044000103f52fd25 0xe044000103f52fd2 0x040000003fc3fc3e 0x0040000003fc3fc3

def z1310 : W := mkw 0x044000103f52fc05 0xc044000103f52fc0 0x240000003ff3fc0e 0x0240000003ff3fc0

def z1311 : W := mkw 0x4181456b40000000 0x04181456b4000000 0xc3c1e77f00000001 0xbc3c1e77f0000000

def z1312 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x500007f0c000fc39 0x0500007f0c000fc3

def z1313 : W := mkw 0x4baf6fefc0000000 0x04baf6fefc000000 0x03c6677f00000000 0x203c6677f0000000

def z1314 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x33c1e70f303cf3ca 0x333c1e70f303cf3c

def z1315 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x8ffe07703fc0f00b 0x38ffe07703fc0f00

def z1316 : W := mkw 0x026c02903b405c01 0x8026c02903b405c0 0x8ffe07f03fc0fc0f 0x78ffe07f03fc0fc0

def z1317 : W := mkw 0x066c02d03b405c01 0xc066c02d03b405c0 0x8ffe06f03fc0cc0f 0x78ffe06f03fc0cc0

def z1318 : W := mkw 0x4b3ffae5c6124925 0x24b3ffae5c612492 0xfffffefcee33cf3f 0xffffffefcee33cf3

def z1319 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xafff98002ff30006 0xdafff98002ff3000

def z1320 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x800007f01000fc0b 0x2800007f01000fc0

def z1321 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe07f03fc0fc04 0x70ffe07f03fc0fc0

def z1322 : W := mkw 0x0276b8003d970004 0x00276b8003d97000 0xaffff8003fff0006 0xfaffff8003fff000

def z1323 : W := mkw 0x044802903b68fe89 0xc044802903b68fe8 0xfc39868c3ffcffcf 0xdfc39868c3ffcffc

def z1324 : W := mkw 0x6913f82b44bf000e 0x06913f82b44bf000 0x2001f803003f0000 0x82001f803003f000

def z1325 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x800007f00000fc0f 0x4800007f00000fc0

def z1326 : W := mkw 0x4bbfffefc4120124 0x24bbfffefc412012 0xcbffffffc0300301 0xfcbffffffc030030

def z1327 : W := mkw 0x0080050000000000 0x0008005000000000 0x83c607f000000001 0x783c607f00000000

def z1328 : W := mkw 0x4bbfffefc4120004 0x04bbfffefc412000 0xffffffffee330c3f 0xfffffffffee330c3

def z1329 : W := mkw 0x0b37f80009000000 0x00b37f8000900000 0x8ffff8000fc00004 0xf8ffff8000fc0000

def z1330 : W := mkw 0x004000103068b688 0x8004000103068b68 0x3000000031fcffce 0x03000000031fcffc

def z1331 : W := mkw 0x2b77f8003dbf012e 0x22b77f8003dbf012 0xbffff8003fff0336 0xfbffff8003fff033

def z1332 : W := mkw 0x04589294bb40fc01 0xc04589294bb40fc0 0xcc399e8cffc0fc0f 0xdcc399e8cffc0fc0

def z1333 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0x73c1e70f303cf3c0 0xb73c1e70f303cf3c

def z1334 : W := mkw 0x06e405503940b400 0xc06e405503940b40 0x0ffe01703fc03000 0x30ffe01703fc0300

def z1335 : W := mkw 0x4b27686140000000 0x04b2768614000000 0x03c6607000000000 0x203c660700000000

def z1336 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x43c7e17f00000000 0xa43c7e17f0000000

def z1337 : W := mkw 0x0b77f80039850000 0x00b77f8003985000 0xaffff8003fcf0006 0xfaffff8003fcf000

def z1338 : W := mkw 0x448807f5c240fc01 0xc448807f5c240fc0 0x000007f0c000fc09 0x0000007f0c000fc0

def z1339 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xaffff8803fff0c0f 0xfaffff8803fff0c0

def z1340 : W := mkw 0x0440001039c5b450 0xd0440001039c5b45 0x3000000011cf3cfe 0x03000000011cf3cf

def z1341 : W := mkw 0x6913f82fc4bf028e 0x06913f82fc4bf028 0x7001f80fc03f03c0 0x87001f80fc03f03c

def z1342 : W := mkw 0x4bb7fd6b44120004 0x04bb7fd6b4412000 0xaffff9732e330006 0xfaffff9732e33000

def z1343 : W := mkw 0x4baf6fefc2004921 0x24baf6fefc200492 0x53c667ffc000cf39 0x253c667ffc000cf3

def z1344 : W := mkw 0x06ec07d4bb40fd21 0xe06ec07d4bb40fd2 0xffff87fcfff0ff3f 0xfffff87fcfff0ff3

def z1345 : W := mkw 0x044000103bc5fc01 0xc044000103bc5fc0 0x240000003fcffc0e 0x0240000003fcffc0

def z1346 : W := mkw 0x0040001039c51450 0x90040001039c5145 0x340000003fcf3cfe 0x0340000003fcf3cf

def z1347 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc399f8fee33ffff 0xdfc399f8fee33fff

def z1348 : W := mkw 0x02bebfe5c6124925 0x202bebfe5c612492 0xffffffffee33cf3f 0xfffffffffee33cf3

def z1349 : W := mkw 0x2b77f82b7dbf02de 0x12b77f82b7dbf02d 0xfffff80fffff03f6 0xffffff80fffff03f

def z1350 : W := mkw 0x4bbfffefc2004801 0x04bbfffefc200480 0xcfffffffce000c05 0xfcfffffffce000c0

def z1351 : W := mkw 0x4bbfffefc4120124 0x24bbfffefc412012 0xfbffffffe033c33b 0xffbffffffe033c33

def z1352 : W := mkw 0x4bbfffefc4970174 0x34bbfffefc497017 0xfbffffffc03f03f1 0xffbffffffc03f03f

def z1353 : W := mkw 0x03af6feb40000000 0x003af6feb4000000 0xcbffffffc0000001 0xfcbffffffc000000

def z1354 : W := mkw 0x244000103f7afc0f 0xc244000103f7afc0 0x040000003ff0fc0e 0x0040000003ff0fc0

def z1355 : W := mkw 0x044000103b68fe89 0xc044000103b68fe8 0x040000003ff0ff0e 0x0040000003ff0ff0

def z1356 : W := mkw 0x4bbdd7ce86124925 0x24bbdd7ce8612492 0x8fff87fc2e30cf0f 0x78fff87fc2e30cf0

def z1357 : W := mkw 0x4abebfe5c0000000 0x04abebfe5c000000 0x0bfe1ef0c0000000 0x50bfe1ef0c000000

def z1358 : W := mkw 0x02bc97c480000000 0x002bc97c48000000 0x8bfe1ff0c0000001 0x78bfe1ff0c000000

def z1359 : W := mkw 0x048a2ff14240fc01 0xc048a2ff14240fc0 0xc0067ff3c000fc09 0xec0067ff3c000fc0

def z1360 : W := mkw 0x448807ffc240fe81 0xc448807ffc240fe8 0x500007ffc000ffc9 0x0500007ffc000ffc

def z1361 : W := mkw 0x0264001039401400 0x8026400103940140 0x8ffe00f03fc00c06 0x78ffe00f03fc00c0

def z1362 : W := mkw 0x0018928486124925 0x2001892848612492 0x3c399e8cee33cf3e 0x53c399e8cee33cf3

def z1363 : W := mkw 0x4ba76d6b40850000 0x04ba76d6b4085000 0x03c6617311cc0000 0x203c6617311cc000

def z1364 : W := mkw 0x4bbdd7ce80000000 0x04bbdd7ce8000000 0xcbffe7ff00000001 0xfcbffe7ff0000000

def z1365 : W := mkw 0x4bb7fd6b40000000 0x04bb7fd6b4000000 0x0bffe17300000000 0x30bffe1730000000

def z1366 : W := mkw 0x0113f82fc4bf03fc 0x30113f82fc4bf03f 0x7001f80fc03f03f0 0x87001f80fc03f03f

def z1367 : W := mkw 0x2913f825c4bf017e 0x32913f825c4bf017 0x7001f80fc03f03f0 0x87001f80fc03f03f

def z1368 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x83c6677300000001 0x383c667730000000

def z1369 : W := mkw 0x02ac07e140000000 0x002ac07e14000000 0xcbfe07f3c0000001 0x7cbfe07f3c000000

def z1370 : W := mkw 0x04589294bfd7fd75 0xf04589294bfd7fd7 0xfc399e8cffffffff 0xdfc399e8cfffffff

def z1371 : W := mkw 0x00c807903240fc01 0x800c807903240fc0 0x8ffe07f03fc0fc0f 0x78ffe07f03fc0fc0

def z1372 : W := mkw 0x4bbfffefc2004921 0x24bbfffefc200492 0xcbffffffc000c301 0xfcbffffffc000c30

def z1373 : W := mkw 0x4bbfffefc2004801 0x04bbfffefc200480 0xffffffffee03cc3f 0xfffffffffee03cc3

def z1374 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xbffff8003fff0c3e 0xfbffff8003fff0c3

def z1375 : W := mkw 0x204000103fff5d7f 0xb204000103fff5d7 0x340000003ffffffe 0x0340000003ffffff

def z1376 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe01f03fc0fc0e 0x60ffe01f03fc0fc0

def z1377 : W := mkw 0x066c02d03b40fc01 0xc066c02d03b40fc0 0x8ffe00f03fc0fc0e 0x78ffe00f03fc0fc0

def z1378 : W := mkw 0x4bbfffefc0850000 0x04bbfffefc085000 0xcbffffffd1cc0001 0xfcbffffffd1cc000

def z1379 : W := mkw 0x02bc97c000000000 0x002bc97c00000000 0x8bff9ff000000001 0xf8bff9ff00000000

def z1380 : W := mkw 0x4bbfffefc000a000 0x04bbfffefc000a00 0xcbffffffc000f009 0xfcbffffffc000f00

def z1381 : W := mkw 0x4bbfffefc63a4bad 0x24bbfffefc63a4ba 0xffffffffee3fcfff 0xfffffffffee3fcff

def z1382 : W := mkw 0x2b77f8003d3a000e 0x02b77f8003d3a000 0x8ffff8003ff00006 0xf8ffff8003ff0000

def z1383 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x8bfff9f3c0000000 0xf8bfff9f3c000000

def z1384 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xc00679f3d1cf3cf5 0xec00679f3d1cf3cf

def z1385 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xfbffffffd00f3cff 0xffbffffffd00f3cf

def z1386 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0x0fffe77f2e30c300 0x30fffe77f2e30c30

def z1387 : W := mkw 0x2b77f80a3dbf028e 0x02b77f80a3dbf028 0xfffff90f3fff33cf 0xffffff90f3fff33c

def z1388 : W := mkw 0x0018928486124925 0x2001892848612492 0x5c399e8cee33cf3d 0x55c399e8cee33cf3

def z1389 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0x000006000000fc08 0x0000006000000fc0

def z1390 : W := mkw 0x2b67680039ad000a 0x02b67680039ad000 0xafffe0003ffc0006 0xfafffe0003ffc000

def z1391 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0x8bfe07f011c00007 0x78bfe07f011c0000

def z1392 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xaffffe003fffc00f 0xfaffffe003fffc00

def z1393 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0xfbfe67f3100c30cb 0xffbfe67f3100c30c

def z1394 : W := mkw 0x2a76b8003d970006 0x02a76b8003d97000 0xafff98003ff30006 0xfafff98003ff3000

def z1395 : W := mkw 0x03a5454a00000000 0x003a5454a0000000 0x03c6617300000000 0x203c661730000000

def z1396 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x8bff9ffcc0000001 0x78bff9ffcc000000

def z1397 : W := mkw 0x06ec07d03b40fd21 0xe06ec07d03b40fd2 0x9ffe07f03fc0ff3f 0x79ffe07f03fc0ff3

def z1398 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xbffe07f03ff0ff0f 0x7bffe07f03ff0ff0

def z1399 : W := mkw 0x4ba5456b40000000 0x04ba5456b4000000 0x03c0017300000000 0x003c001730000000

def z1400 : W := mkw 0x0bbdd7c000000000 0x00bbdd7c00000000 0x8bff87f000000001 0x78bff87f00000000

def z1401 : W := mkw 0x0b67680039000000 0x00b6768003900000 0x8ffe60003fc00006 0x78ffe60003fc0000

def z1402 : W := mkw 0x2b67680039ad000a 0x02b67680039ad000 0x0ffe60001fcc0004 0x60ffe60001fcc000

def z1403 : W := mkw 0x42ae2fefc0000000 0x042ae2fefc000000 0xcbfe7fffc0000001 0xfcbfe7fffc000000

def z1404 : W := mkw 0x4bbfffefc0850000 0x04bbfffefc085000 0xebffffffc00f0001 0xfebffffffc00f000

def z1405 : W := mkw 0x244000103ffffd2f 0xe244000103ffffd2 0x340000003fffff3e 0x0340000003fffff3

def z1406 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x2fff98003fff0006 0x52fff98003fff000

def z1407 : W := mkw 0x0bb7fd2b40000000 0x00bb7fd2b4000000 0xcbffffffc0000001 0xfcbffffffc000000

def z1408 : W := mkw 0x2a76b8003d970006 0x02a76b8003d97000 0x0ffe18001fc30004 0x60ffe18001fc3000

def z1409 : W := mkw 0x063ebaf5cfd75d75 0xf063ebaf5cfd75d7 0x0c3e18f0cfc30c34 0x40c3e18f0cfc30c3

def z1410 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xf0067fffd1cfffff 0xef0067fffd1cffff

def z1411 : W := mkw 0x4bbfffefc000a280 0x04bbfffefc000a28 0xcbffffffc000c301 0xfcbffffffc000c30

def z1412 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xeffffe0c3fff0007 0xfeffffe0c3fff000

def z1413 : W := mkw 0x2b77f804bdbf012e 0x22b77f804bdbf012 0xaffff800ffff0036 0xfaffff800ffff003

def z1414 : W := mkw 0x02a4054000000000 0x002a405400000000 0x83c6077000000001 0x383c607700000000

def z1415 : W := mkw 0x4181456b40000000 0x04181456b4000000 0x03c0617300000000 0x203c061730000000

def z1416 : W := mkw 0x048807f14240fc51 0xd048807f14240fc5 0x000007f0c000fc39 0x0000007f0c000fc3

def z1417 : W := mkw 0x2b77f8217dbf005e 0x12b77f8217dbf005 0xaffff8033fff00c6 0xfaffff8033fff00c

def z1418 : W := mkw 0x4bbdd7efc0000000 0x04bbdd7efc000000 0xcbf99fffc0000001 0xdcbf99fffc000000

def z1419 : W := mkw 0x4913f82fc4970174 0x34913f82fc497017 0x7001f80fc03f03f0 0x87001f80fc03f03f

def z1420 : W := mkw 0x4bbfffefc0280288 0x04bbfffefc028028 0xfbffffffe03cc3cb 0xffbffffffe03cc3c

def z1421 : W := mkw 0x4d9bffffc240fc01 0xc4d9bffffc240fc0 0x4001ffffc000fc09 0x84001ffffc000fc0

def z1422 : W := mkw 0x0181450a00000000 0x00181450a0000000 0xf3c1e70f303cf3cb 0xbf3c1e70f303cf3c

def z1423 : W := mkw 0x02e4054039000000 0x002e405403900000 0x8ffe01703fc00006 0x78ffe01703fc0000

def z1424 : W := mkw 0x4bbfffefc4120124 0x24bbfffefc412012 0xfbffffffc0330f3f 0xffbffffffc0330f3

def z1425 : W := mkw 0x4b3ffae5c6124925 0x24b3ffae5c612492 0xaffff8f0ee330c36 0xfaffff8f0ee330c3

def z1426 : W := mkw 0x06ec07d03b68fe89 0xc06ec07d03b68fe8 0x8ffe07f03ff0ff0f 0x78ffe07f03ff0ff0

def z1427 : W := mkw 0x06ec07da3b40fc01 0xc06ec07da3b40fc0 0xcffe07ff3fc0fc0f 0x7cffe07ff3fc0fc0

def z1428 : W := mkw 0x06ec07c03b00e801 0x406ec07c03b00e80 0x8ffe07f03fc0c007 0x78ffe07f03fc0c00

def z1429 : W := mkw 0x0040001030c5b450 0x90040001030c5b45 0x3000000031cffcfe 0x03000000031cffcf

def z1430 : W := mkw 0x062c02d00b405c01 0xc062c02d00b405c0 0x8ffe00f00fc00c04 0x78ffe00f00fc00c0

def z1431 : W := mkw 0x0264000039000000 0x0026400003900000 0x8ffe01003fc0300f 0x78ffe01003fc0300

def z1432 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x340000003ff0ff0e 0x0340000003ff0ff0

def z1433 : W := mkw 0x4199d7efc0000000 0x04199d7efc000000 0xcbf9ffffc0000001 0xfcbf9ffffc000000

def z1434 : W := mkw 0x0b77f80039280008 0x00b77f8003928000 0xaffff8003ffc0006 0xfaffff8003ffc000

def z1435 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xcfffffffee30cf0f 0xfcfffffffee30cf0

def z1436 : W := mkw 0x4bbdd7efc0000000 0x04bbdd7efc000000 0x0bf986fcc0000000 0x10bf986fcc000000

def z1437 : W := mkw 0x0b27682140000000 0x00b2768214000000 0x03c6617300000000 0x203c661730000000

def z1438 : W := mkw 0x2b77f80ebdbf03ae 0x22b77f80ebdbf03a 0xfffff80fffff03f6 0xffffff80fffff03f

def z1439 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0x0ffe01701fc03000 0x20ffe01701fc0300

def z1440 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0x43c6677f00000001 0x243c6677f0000000

def z1441 : W := mkw 0x008807bfc240fff1 0xb008807bfc240fff 0x500007ffc000fff9 0x0500007ffc000fff

def z1442 : W := mkw 0x0264000039000000 0x0026400003900000 0x8ffe06003fc0c00f 0x78ffe06003fc0c00

def z1443 : W := mkw 0x0ba76d4000000000 0x00ba76d400000000 0x03c6617000000000 0x203c661700000000

def z1444 : W := mkw 0x06ec07da3b40fe81 0xc06ec07da3b40fe8 0xfffe67ff3fccffcf 0xffffe67ff3fccffc

def z1445 : W := mkw 0x4bbfffefc4120124 0x24bbfffefc412012 0xcbffffffc0030031 0xfcbffffffc003003

def z1446 : W := mkw 0x02ec07c03900a000 0x002ec07c03900a00 0x8ffe07f03fc0f00f 0x78ffe07f03fc0f00

def z1447 : W := mkw 0x02ae2fe140000000 0x002ae2fe14000000 0x8bfe67f300000001 0x78bfe67f30000000

def z1448 : W := mkw 0x2b77f8003dbf028e 0x02b77f8003dbf028 0xbffff8003fff03c6 0xfbffff8003fff03c

def z1449 : W := mkw 0x06ec07da3b40fe81 0xc06ec07da3b40fe8 0x8ffe07f33fc0fccf 0x78ffe07f33fc0fcc

def z1450 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x4bfff9ffc0000000 0xe4bfff9ffc000000

def z1451 : W := mkw 0x048807d00240fd21 0xe048807d00240fd2 0x100007f00000ff39 0x0100007f00000ff3

def z1452 : W := mkw 0x236540003dbf000e 0x0236540003dbf000 0xafffe0003fff0006 0xfafffe0003fff000

def z1453 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xdbffffffc0000c39 0xfdbffffffc0000c3

def z1454 : W := mkw 0x0018928486124925 0x2001892848612492 0x7c399e8cee33cf34 0xd7c399e8cee33cf3

def z1455 : W := mkw 0x4b3ffae5c0000000 0x04b3ffae5c000000 0xcbfffefcc0000001 0xfcbfffefcc000000

def z1456 : W := mkw 0x4baf6fefc0000000 0x04baf6fefc000000 0xc3c67fffc0000001 0xec3c67fffc000000

def z1457 : W := mkw 0x4bbdd7efc6124925 0x24bbdd7efc612492 0x5ff987ffee30cf39 0x15ff987ffee30cf3

def z1458 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x2ffff8002fff0004 0xd2ffff8002fff000

def z1459 : W := mkw 0x4bbfffefc0000050 0x14bbfffefc000005 0xdbffffffc00000f1 0xfdbffffffc00000f

def z1460 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xbffff8003fff30ce 0xfbffff8003fff30c

def z1461 : W := mkw 0x4bbfffefc6974975 0x34bbfffefc697497 0xffffffffee3fcfff 0xfffffffffee3fcff

def z1462 : W := mkw 0x0018928486124925 0x2001892848612492 0xfc399e8cfe3fffff 0xdfc399e8cfe3ffff

def z1463 : W := mkw 0x0181450a00000000 0x00181450a0000000 0xc3c7e7ff00000001 0xfc3c7e7ff0000000

def z1464 : W := mkw 0x2b67680039ad000a 0x02b67680039ad000 0xaffe78003fcf0006 0xfaffe78003fcf000

def z1465 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0xfbfe1ff0c0030c3f 0xffbfe1ff0c0030c3

def z1466 : W := mkw 0x02bebfe5c0000000 0x002bebfe5c000000 0xcbffffffc0000001 0xfcbffffffc000000

def z1467 : W := mkw 0x01836d2b40000000 0x001836d2b4000000 0xf3c7ffffe033cf3f 0xff3c7ffffe033cf3

def z1468 : W := mkw 0x4bbfffefc2004921 0x24bbfffefc200492 0xfbffffffc003cf3f 0xffbffffffc003cf3

def z1469 : W := mkw 0x0040001036fffffd 0xb0040001036fffff 0x340000003ffffffe 0x0340000003ffffff

def z1470 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x8ffff8003ffc0000 0xf8ffff8003ffc000

def z1471 : W := mkw 0x06e405503940b400 0xc06e405503940b40 0x8ffe07703fc0f00f 0x78ffe07703fc0f00

def z1472 : W := mkw 0x4bbfffefc0850000 0x04bbfffefc085000 0xfbffffffd1cf0c3f 0xffbffffffd1cf0c3

def z1473 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xaffff880ffff0c36 0xfaffff880ffff0c3

def z1474 : W := mkw 0x0002283140c51450 0x90002283140c5145 0x700679f3d1cf3cf4 0xe700679f3d1cf3cf

def z1475 : W := mkw 0x0365400039280008 0x0036540003928000 0x8ffe60003fcc0006 0x78ffe60003fcc000

def z1476 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xebffffffc0030007 0xfebffffffc003000

def z1477 : W := mkw 0x02ae2fc000000000 0x002ae2fc00000000 0x8bfe7ff000000001 0xf8bfe7ff00000000

def z1478 : W := mkw 0x2b77f8217dbf005e 0x12b77f8217dbf005 0xfffff903ffff30ff 0xffffff903ffff30f

def z1479 : W := mkw 0x4bbfffefc0850050 0x14bbfffefc085005 0xfbffffffd1cf00f7 0xffbffffffd1cf00f

def z1480 : W := mkw 0x048807da0240fc01 0xc048807da0240fc0 0x400007ff0000fc09 0x0400007ff0000fc0

def z1481 : W := mkw 0x2d53f8103ffffc0f 0xc2d53f8103ffffc0 0x2401f8003ffffc0e 0x82401f8003ffffc0

def z1482 : W := mkw 0x00c005003000a000 0x000c005003000a00 0xf3c1e70f303cf3cb 0xbf3c1e70f303cf3c

def z1483 : W := mkw 0x448807ffc240fc51 0xd448807ffc240fc5 0x500007ffc000fcf9 0x0500007ffc000fcf

def z1484 : W := mkw 0x6bbfffefc4bf000e 0x06bbfffefc4bf000 0xebffffffd1ff0007 0xfebffffffd1ff000

def z1485 : W := mkw 0x02a62d6140000000 0x002a62d614000000 0xc3c679f3c0000001 0xec3c679f3c000000

def z1486 : W := mkw 0x044000103bc5fc51 0xd044000103bc5fc5 0x040000003fc3fc3e 0x0040000003fc3fc3

def z1487 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x8bfe7ff3c0000001 0x78bfe7ff3c000000

def z1488 : W := mkw 0x048807f14240fc51 0xd048807f14240fc5 0x000007f30000fcc9 0x0000007f30000fcc

def z1489 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xa00679f3d1cf3cf6 0xea00679f3d1cf3cf

def z1490 : W := mkw 0x0000001000401400 0x8000000100040140 0xf00679f3d1cf3cff 0xef00679f3d1cf3cf

def z1491 : W := mkw 0x4bbdd7efc0000000 0x04bbdd7efc000000 0xcbff87ffc0000001 0x7cbff87ffc000000

def z1492 : W := mkw 0x0181451a00c51450 0x90181451a00c5145 0xf3c1e70f11cf3cff 0xbf3c1e70f11cf3cf

def z1493 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0xf4001880ffc3fc3f 0xcf4001880ffc3fc3

def z1494 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0x840006003fc0fc0f 0x1840006003fc0fc0

def z1495 : W := mkw 0x04c005103b40fc01 0xc04c005103b40fc0 0x040007003fc0fc0f 0x0040007003fc0fc0

def z1496 : W := mkw 0x01c1450a3028a288 0x001c1450a3028a28 0xf3c1e70f303fffff 0xbf3c1e70f303ffff

def z1497 : W := mkw 0x20589294bfff5d7f 0xb20589294bfff5d7 0xfc399e8cffffffff 0xdfc399e8cfffffff

def z1498 : W := mkw 0x4bb7fd6fc0000000 0x04bb7fd6fc000000 0xcbfff97fc0000000 0xfcbfff97fc000000

def z1499 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0xfffff8003fff000f 0xffffff8003fff000

def z1500 : W := mkw 0x0367680039ad0008 0x00367680039ad000 0xaffff8003fff0006 0xfaffff8003fff000

def z1501 : W := mkw 0x4ba76d6b40280288 0x04ba76d6b4028028 0x03c66173000c00c0 0x203c66173000c00c

def z1502 : W := mkw 0x066c02d03b40fc01 0xc066c02d03b40fc0 0x0c3800003fc0fc0e 0x00c3800003fc0fc0

def z1503 : W := mkw 0x026400003900a000 0x0026400003900a00 0x8ffe00003fc0f00e 0x78ffe00003fc0f00

def z1504 : W := mkw 0x4bb7fd6b40000000 0x04bb7fd6b4000000 0xcbfff9f3c0000001 0xfcbfff9f3c000000

def z1505 : W := mkw 0x048807da0240fe81 0xc048807da0240fe8 0x000007f30000fcc9 0x0000007f30000fcc

def z1506 : W := mkw 0x0365400039000000 0x0036540003900000 0x8fffe0003fc00006 0xf8fffe0003fc0000

def z1507 : W := mkw 0x0b75d00039000000 0x00b75d0003900000 0x8fff80003fc00006 0x78fff80003fc0000

def z1508 : W := mkw 0x6bb7fd6b4d970006 0x06bb7fd6b4d97000 0x0ffe79730fc30004 0x60ffe79730fc3000

def z1509 : W := mkw 0x2b77f80a3dbf000e 0x02b77f80a3dbf000 0xeffff80f3fff0006 0xfeffff80f3fff000

def z1510 : W := mkw 0x0002283140c51450 0x90002283140c5145 0xf007f9f3f1ff3cff 0xff007f9f3f1ff3cf

def z1511 : W := mkw 0x2b77f80a3dbf028e 0x02b77f80a3dbf028 0xfffffe0f3fffc3cf 0xffffffe0f3fffc3c

def z1512 : W := mkw 0x0bbfffc006124805 0x00bbfffc00612480 0xaffffff02e33cc0f 0xfaffffff02e33cc0

def z1513 : W := mkw 0x4bbfffefc0280288 0x04bbfffefc028028 0xcbffffffc00c00c1 0xfcbffffffc00c00c

def z1514 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x8bffe7ff00000001 0x78bffe7ff0000000

def z1515 : W := mkw 0x0040001030edb6d8 0x90040001030edb6d 0x0000000011cc30c0 0x00000000011cc30c

def z1516 : W := mkw 0x2913f82b44bf02de 0x12913f82b44bf02d 0x7001f80fc03f03f0 0x87001f80fc03f03f

def z1517 : W := mkw 0x42ac07efc0000000 0x042ac07efc000000 0x43c607ffc0000001 0x243c607ffc000000

def z1518 : W := mkw 0x244000103ffffe8f 0xc244000103ffffe8 0x340000003fffffce 0x0340000003fffffc

def z1519 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xfffe07f03fc0fc0f 0xffffe07f03fc0fc0

def z1520 : W := mkw 0x027490003d120004 0x0027490003d12000 0x8fff80003ff00006 0x78fff80003ff0000

def z1521 : W := mkw 0x24589294bffffd2f 0xe24589294bffffd2 0xfc399e8cffffff3f 0xdfc399e8cffffff3

def z1522 : W := mkw 0x044000103f7affad 0xe044000103f7affa 0x340000003ffffffe 0x0340000003ffffff

def z1523 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xefffffffee330c37 0xfefffffffee330c3

def z1524 : W := mkw 0x204000103dff140e 0x8204000103dff140 0x240000003fff3c0e 0x0240000003fff3c0

def z1525 : W := mkw 0x02ac07c000000000 0x002ac07c00000000 0xfbff87fc2030c30b 0xffbff87fc2030c30

def z1526 : W := mkw 0x044000103240fc01 0xc044000103240fc0 0x000000003000fc0a 0x0000000003000fc0

def z1527 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xffffffffee30c30b 0xfffffffffee30c30

def z1528 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0xcbffe77f00000001 0xbcbffe77f0000000

def z1529 : W := mkw 0x048807d00240fc01 0xc048807d00240fc0 0xf0001ff0c003fc3f 0xcf0001ff0c003fc3

def z1530 : W := mkw 0x044228103bc5fc01 0xc044228103bc5fc0 0xa40678003fcffc0e 0xea40678003fcffc0

def z1531 : W := mkw 0x066c02d03b405c01 0xc066c02d03b405c0 0x0ffe00f01fc00c04 0x60ffe00f01fc00c0

def z1532 : W := mkw 0x2a3ebab5cfd75d77 0xb2a3ebab5cfd75d7 0x0c3e18f0cfc30c34 0x40c3e18f0cfc30c3

def z1533 : W := mkw 0x044000103b40fc01 0xc044000103b40fc0 0xf40061033fccfccf 0xaf40061033fccfcc

def z1534 : W := mkw 0x6bbfffefcd970006 0x06bbfffefcd97000 0xefffffffdfcf0007 0xfefffffffdfcf000

def z1535 : W := mkw 0x244000103ffffc5f 0xd244000103ffffc5 0x340000003ffffcfe 0x0340000003ffffcf

def z1536 : W := mkw 0x4ba76d6b40000000 0x04ba76d6b4000000 0xf3c7e77f2030c30b 0xbf3c7e77f2030c30

def z1537 : W := mkw 0x0008028002004801 0x0000802800200480 0xfc399e8cee33cf3f 0xdfc399e8cee33cf3

def z1538 : W := mkw 0x06ec07d03b40fc01 0xc06ec07d03b40fc0 0xdffe07f0ffc0fc3f 0x7dffe07f0ffc0fc3

def z1539 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x8fff98003ff30006 0x78fff98003ff3000

def z1540 : W := mkw 0x0266280039850000 0x0026628003985000 0x8ffe18003fc30006 0x78ffe18003fc3000

def z1541 : W := mkw 0x4abebfe5c6124925 0x24abebfe5c612492 0xffff9ffcee33cf3f 0xfffff9ffcee33cf3

def z1542 : W := mkw 0x2b77f8003dbf000e 0x02b77f8003dbf000 0x2ffff8003fff0000 0xb2ffff8003fff000

def z1543 : W := mkw 0x07e76d7b79edb6d8 0xd07e76d7b79edb6d 0x03c6617311cc30c0 0x203c6617311cc30c

def z1544 : W := mkw 0x4bb7fd6fc0000000 0x04bb7fd6fc000000 0xc3c7ff7fc0000001 0xbc3c7ff7fc000000

def z1545 : W := mkw 0x0b3ffaa5c0000000 0x00b3ffaa5c000000 0xcbffffffc0000001 0xfcbffffffc000000

def z1546 : W := mkw 0x4bbfffefc6124925 0x24bbfffefc612492 0xcfffffffee03cc3f 0xfcfffffffee03cc3

def z1547 : W := mkw 0x4baf6fefc0000000 0x04baf6fefc000000 0x03c661f3c0000000 0x203c661f3c000000

def z1548 : W := mkw 0x4993fd2fc0000000 0x04993fd2fc000000 0xc3c7ffffc0000001 0xfc3c7ffffc000000

def z1549 : W := mkw 0x205090103dff145e 0x9205090103dff145 0xfc399880ffff3cff 0xdfc399880ffff3cf

def z1550 : W := mkw 0x4bbfffefc0000000 0x04bbfffefc000000 0x4bfe7fffc0000001 0x64bfe7fffc000000

def z1551 : W := mkw 0x4baf6fefc0000000 0x04baf6fefc000000 0xc3c7e7ffc0000001 0xbc3c7e7ffc000000

def z1552 : W := mkw 0x4b3ffae5c0000000 0x04b3ffae5c000000 0x0bfe78f0c0000000 0x60bfe78f0c000000

def z1553 : W := mkw 0x4bbfffefc2004921 0x24bbfffefc200492 0xfbffffffe030cf3b 0xffbffffffe030cf3

def z1554 : W := mkw 0x07fdd7cebf3aebad 0x607fdd7cebf3aeba 0x0ff9860c2e30c300 0x10ff9860c2e30c30

def z1555 : W := mkw 0x2b77f8217dbf005e 0x12b77f8217dbf005 0xfffff883ffff0cff 0xffffff883ffff0cf

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z7,z8]),(0,[z1,z2,z3,z4,z9,z5,z10]),(1,[z1,z2,z3,z4,z5,z11])],[(0,[z12,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z13,z4,z5,z8]),(0,[z1,z2,z3,z4,z14,z5,z8]),(0,[z1,z2,z3,z4,z5,z15,z8]),(0,[z1,z2,z3,z16,z4,z4,z5])],[(0,[z1,z2,z3,z17,z4,z5,z8]),(0,[z1,z2,z3,z4,z18,z5,z10])],[(0,[z1,z2,z3,z19,z20,z4,z8]),(0,[z21,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z22,z8]),(0,[z1,z2,z23,z3,z24,z4,z8]),(1,[z1,z2,z3,z25,z5,z8]),(0,[z1,z2,z3,z16,z4,z5,z8]),(0,[z1,z2,z3,z16,z4,z5,z26])],[(0,[z1,z2,z3,z4,z5,z8,z27]),(0,[z1,z28,z2,z19,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z29]),(1,[z1,z2,z3,z16,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z30,z8]),(0,[z1,z2,z3,z4,z5,z31,z8])],[(0,[z1,z28,z32,z3,z4,z5,z8]),(0,[z1,z33,z2,z3,z16,z4,z5])],[(0,[z1,z2,z3,z34,z35,z5,z8]),(0,[z1,z2,z3,z36,z4,z5,z8]),(0,[z1,z2,z37,z3,z24,z4,z8])],[(0,[z1,z2,z3,z4,z5,z8,z38]),(0,[z1,z39,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z40,z4,z5,z8]),(0,[z1,z2,z3,z4,z41,z5,z8]),(0,[z1,z2,z37,z3,z42,z5,z8]),(0,[z1,z2,z3,z16,z4,z43,z5])],[(0,[z1,z2,z3,z4,z5,z44,z8])],[(0,[z45,z1,z2,z3,z4,z5,z8])],[(0,[z46,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z47,z8]),(0,[z1,z48,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z49]),(0,[z1,z2,z3,z4,z50,z5,z51]),(0,[z1,z2,z3,z52,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z53,z8])],[(0,[z1,z2,z3,z4,z54,z5,z8]),(0,[z55,z2,z3,z4,z5,z6,z8])],[(0,[z1,z2,z32,z3,z16,z4,z5])]],
   [[(0,[z1,z33,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z57,z10]),(0,[z1,z58,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z59,z4,z5,z8]),(0,[z1,z2,z3,z4,z18,z60,z8]),(0,[z1,z2,z3,z61,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z62]),(0,[z1,z2,z3,z63,z4,z5,z64])],[(1,[z1,z2,z3,z65,z4,z5])],[(0,[z1,z2,z3,z4,z5,z66,z8])],[(0,[z1,z2,z3,z4,z5,z8,z67]),(0,[z68,z1,z2,z3,z4,z5,z69]),(0,[z1,z2,z3,z34,z4,z5,z10])],[(0,[z1,z2,z3,z4,z70,z5,z8]),(1,[z1,z33,z3,z4,z71,z8]),(0,[z1,z2,z3,z4,z5,z72,z8])],[(0,[z1,z2,z73,z3,z4,z5,z10])],[(0,[z1,z2,z3,z4,z74,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z26])],[(0,[z75,z1,z2,z3,z24,z4,z8]),(0,[z1,z2,z76,z3,z4,z5,z8]),(0,[z1,z2,z37,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z77,z5,z10]),(0,[z1,z2,z3,z4,z78,z5,z79]),(0,[z80,z1,z2,z3,z24,z4,z8]),(0,[z1,z2,z81,z3,z4,z5,z8])],[(0,[z1,z2,z82,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z83,z8]),(0,[z68,z1,z2,z3,z63,z4,z5]),(0,[z1,z2,z3,z20,z4,z84,z8]),(0,[z1,z2,z3,z4,z71,z85,z8]),(0,[z86,z1,z2,z3,z4,z5,z8])],[(0,[z1,z87,z2,z3,z4,z5,z8]),(0,[z88,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z89]),(0,[z1,z90,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z91,z8,z92])],[(0,[z1,z2,z3,z63,z93,z4,z5]),(0,[z1,z2,z34,z4,z94,z5,z8]),(0,[z95,z1,z2,z3,z63,z4,z5])],[(0,[z1,z96,z2,z3,z24,z4,z8])],[(0,[z1,z2,z3,z4,z97,z5,z8]),(0,[z68,z1,z2,z3,z24,z5,z8]),(1,[z1,z2,z3,z98,z5,z8]),(0,[z1,z2,z3,z20,z4,z18,z8]),(1,[z1,z2,z3,z99,z4,z5]),(0,[z1,z2,z100,z3,z4,z5,z101])],[(0,[z1,z2,z3,z16,z4,z5,z102])],[(0,[z1,z2,z3,z34,z4,z5,z8]),(0,[z1,z2,z3,z103,z4,z5,z8]),(1,[z1,z2,z3,z52,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z104,z8]),(0,[z105,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z106,z3,z4,z5,z8]),(0,[z1,z2,z23,z3,z4,z50,z8]),(0,[z107,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z73,z3,z4,z5,z8])],[(0,[z55,z1,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z16,z5,z8,z92])],[(0,[z1,z2,z3,z93,z35,z5,z8]),(0,[z1,z108,z2,z3,z4,z5,z8]),(0,[z1,z33,z2,z3,z4,z18,z8]),(0,[z1,z2,z3,z4,z77,z5,z8])],[(0,[z1,z2,z3,z4,z5,z109,z10]),(0,[z1,z2,z37,z3,z4,z50,z8]),(0,[z1,z110,z2,z3,z4,z5,z8])],[(0,[z1,z111,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z112,z5,z8])],[(0,[z113,z1,z2,z3,z4,z114,z8]),(0,[z115,z1,z2,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z63,z4,z5]),(0,[z1,z2,z3,z4,z116,z5,z8]),(0,[z1,z2,z3,z117,z4,z5,z8])],[(1,[z1,z2,z3,z118,z5,z8]),(0,[z1,z2,z3,z16,z119,z4,z5])],[(0,[z68,z1,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z120,z5,z8])],[(0,[z1,z2,z3,z121,z4,z5,z10]),(0,[z75,z1,z2,z3,z4,z5,z51]),(0,[z122,z1,z2,z3,z4,z123,z8]),(0,[z80,z1,z2,z3,z4,z5,z51])],[(1,[z1,z2,z3,z4,z5,z124]),(1,[z1,z2,z3,z125,z5,z8]),(1,[z1,z2,z3,z24,z109,z8])],[(1,[z126,z2,z3,z4,z84,z8]),(0,[z1,z2,z3,z4,z127,z5,z8]),(0,[z1,z128,z2,z3,z4,z5,z129])],[(0,[z1,z2,z3,z4,z130,z5,z8]),(0,[z55,z1,z2,z3,z4,z5,z131]),(0,[z1,z2,z132,z3,z4,z5,z79])],[(1,[z1,z2,z3,z4,z133,z8]),(0,[z1,z2,z3,z4,z134,z84,z8]),(1,[z1,z2,z3,z135,z5,z8])],[(0,[z1,z2,z3,z4,z5,z136,z51]),(0,[z1,z2,z100,z3,z4,z137,z8]),(1,[z1,z2,z3,z24,z63,z4]),(0,[z1,z138,z2,z3,z4,z5,z8])],[(0,[z1,z2,z139,z3,z121,z4,z5]),(0,[z1,z2,z3,z4,z5,z140,z8]),(0,[z141,z1,z2,z3,z16,z4,z5]),(1,[z1,z2,z3,z142,z5,z8]),(0,[z143,z1,z96,z3,z4,z5,z8]),(0,[z1,z2,z144,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z109,z8])]],
   [[(0,[z145,z1,z2,z121,z4,z5,z8]),(0,[z1,z2,z3,z93,z4,z5,z10])],[(0,[z1,z2,z3,z4,z5,z8,z146]),(0,[z1,z2,z73,z3,z34,z5,z8]),(0,[z1,z147,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z63,z4,z134,z5])],[(0,[z1,z2,z3,z4,z5,z148,z8]),(0,[z1,z2,z3,z149,z4,z5,z8])],[(0,[z150,z2,z3,z121,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z151]),(0,[z1,z2,z3,z4,z5,z8,z152]),(0,[z1,z2,z153,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z84,z71,z8]),(0,[z154,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z155,z4,z5,z8])],[(0,[z1,z2,z156,z121,z4,z5,z8]),(0,[z1,z2,z3,z157,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z158]),(0,[z0,z1,z2,z159,z3,z4,z5]),(0,[z0,z1,z2,z3,z20,z4,z8]),(0,[z1,z58,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z160,z4,z5,z8])],[(0,[z161,z1,z2,z3,z4,z5,z8]),(0,[z1,z162,z2,z3,z4,z5,z163]),(0,[z1,z2,z3,z4,z164,z5,z8]),(0,[z1,z2,z100,z3,z94,z5,z8]),(0,[z1,z2,z165,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z77,z5,z166])],[(0,[z1,z2,z3,z20,z167,z4,z8]),(0,[z168,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z169,z10]),(0,[z1,z2,z73,z3,z63,z4,z5]),(1,[z1,z2,z3,z24,z16,z5])],[(0,[z170,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z171]),(0,[z1,z33,z3,z4,z5,z71,z8]),(0,[z1,z2,z3,z63,z4,z5,z51]),(0,[z1,z2,z3,z20,z4,z94,z8]),(0,[z1,z2,z172,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z10,z131]),(0,[z1,z162,z2,z3,z167,z5,z8]),(0,[z1,z2,z3,z16,z4,z5,z79]),(0,[z1,z2,z173,z3,z16,z4,z5])],[(0,[z1,z174,z2,z3,z4,z5,z8]),(1,[z1,z3,z4,z5,z10,z51]),(0,[z1,z2,z3,z175,z4,z5,z8])],[(0,[z1,z2,z3,z93,z4,z5,z8]),(0,[z1,z2,z3,z4,z94,z5,z10])],[(0,[z1,z2,z3,z4,z5,z176,z10])],[(0,[z145,z1,z177,z3,z4,z5,z8]),(0,[z1,z178,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z179,z5,z8])],[(0,[z1,z2,z3,z4,z60,z71,z8]),(0,[z1,z2,z3,z63,z4,z5,z6]),(0,[z1,z2,z3,z180,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z181]),(0,[z1,z2,z3,z63,z4,z5,z44])],[(0,[z1,z2,z3,z4,z5,z182,z8]),(1,[z1,z2,z3,z4,z5,z183]),(0,[z1,z2,z3,z4,z184,z5,z8])]],
   [[],[(0,[z113,z1,z2,z185,z4,z5,z8]),(0,[z186,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z187,z5,z8]),(0,[z1,z2,z3,z4,z188,z5,z8]),(2,[z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z189,z4,z5,z8]),(0,[z1,z2,z190,z3,z4,z5,z8])],[(1,[z191,z2,z3,z4,z60,z8]),(0,[z1,z2,z3,z4,z5,z169,z8]),(1,[z1,z2,z3,z192,z4,z8]),(0,[z1,z2,z3,z4,z193,z5,z8])],[(0,[z145,z1,z194,z3,z4,z5,z8]),(1,[z1,z2,z139,z3,z4,z5]),(0,[z1,z2,z3,z63,z4,z5,z10])],[(1,[z1,z2,z3,z4,z104,z8]),(0,[z1,z2,z3,z4,z5,z8,z131]),(0,[z122,z1,z3,z19,z4,z5,z8])],[(0,[z113,z1,z2,z3,z195,z5,z8]),(0,[z75,z150,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z93,z4,z8])],[(0,[z68,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z73,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z94,z5,z8]),(0,[z1,z2,z3,z196,z16,z4,z5])],[(0,[z1,z2,z197,z3,z4,z5,z8]),(0,[z1,z2,z3,z198,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z10,z199])],[(0,[z145,z1,z2,z3,z54,z5,z8]),(0,[z95,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z77,z5,z200])],[(0,[z1,z201,z2,z3,z4,z5,z10])],[(1,[z1,z2,z3,z4,z5,z202]),(0,[z1,z2,z3,z121,z63,z4,z5]),(0,[z126,z1,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z4,z5,z203,z51])],[(0,[z1,z2,z3,z4,z204,z5,z8])],[(0,[z1,z2,z3,z4,z5,z133,z8]),(1,[z1,z2,z3,z4,z205,z5]),(0,[z1,z2,z3,z4,z5,z8,z206])],[(0,[z207,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z208,z5,z51]),(0,[z209,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z79])],[(0,[z1,z2,z3,z4,z9,z5,z8])],[]],
   [[(0,[z1,z2,z3,z210,z4,z5,z8]),(0,[z1,z2,z3,z4,z18,z5,z8]),(0,[z211,z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z5,z51,z92]),(0,[z1,z2,z3,z4,z5,z212,z8])],[(1,[z1,z2,z3,z213,z4,z5]),(0,[z1,z2,z3,z4,z5,z214,z8]),(0,[z1,z2,z215,z3,z4,z5,z8]),(0,[z1,z2,z216,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z217,z5,z8]),(1,[z1,z2,z3,z4,z5,z56])],[],[(0,[z150,z201,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z187,z8]),(0,[z0,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z63,z4,z5,z218])],[],[],[(0,[z1,z2,z219,z3,z4,z5,z8]),(0,[z1,z2,z3,z99,z4,z5,z51]),(1,[z1,z2,z3,z24,z94,z8])],[(0,[z1,z2,z3,z4,z220,z5,z8]),(0,[z1,z221,z2,z3,z4,z5,z8]),(0,[z1,z2,z23,z3,z4,z5,z51])],[],[(0,[z1,z2,z3,z121,z20,z4,z8])],[(1,[z1,z2,z3,z222,z4,z8]),(0,[z1,z2,z3,z4,z50,z5,z10]),(0,[z1,z223,z2,z3,z4,z5,z8])],[(0,[z1,z2,z224,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z205,z5,z60]),(0,[z1,z225,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z226,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z134,z8]),(0,[z1,z2,z165,z3,z20,z4,z8])],[(0,[z113,z1,z2,z3,z24,z4,z8]),(1,[z1,z2,z3,z4,z227,z8]),(0,[z1,z2,z3,z4,z35,z5,z51]),(0,[z1,z162,z2,z3,z4,z5,z228]),(0,[z1,z2,z3,z63,z34,z4,z5]),(0,[z1,z2,z132,z3,z16,z4,z5]),(0,[z1,z2,z229,z3,z24,z4,z8]),(0,[z1,z2,z3,z24,z5,z109,z8]),(0,[z1,z230,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z231,z5,z8])],[(0,[z75,z1,z2,z232,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z56,z8])],[(0,[z2,z232,z3,z121,z4,z5,z8]),(0,[z1,z2,z3,z233,z4,z5,z8]),(0,[z1,z2,z3,z24,z167,z5,z8]),(0,[z1,z2,z3,z4,z5,z57,z8]),(0,[z143,z1,z3,z4,z5,z10,z8])],[(0,[z1,z234,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z20,z93,z4,z8]),(1,[z1,z2,z3,z4,z8,z235]),(0,[z1,z2,z3,z4,z5,z8,z236])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z124]),(0,[z1,z2,z3,z4,z5,z237,z8]),(0,[z1,z2,z238,z3,z4,z5,z8]),(0,[z1,z2,z3,z239,z4,z5,z8])],[(0,[z1,z2,z3,z63,z4,z5,z60]),(0,[z1,z2,z3,z4,z5,z240,z51])],[(0,[z1,z241,z2,z3,z4,z5,z8]),(0,[z1,z2,z23,z3,z4,z5,z10]),(1,[z1,z2,z3,z4,z78,z26])],[(0,[z1,z2,z3,z63,z4,z35,z5])],[(0,[z1,z2,z3,z242,z4,z5,z8]),(0,[z1,z2,z23,z4,z5,z85,z8]),(0,[z1,z243,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z63,z63,z4,z5])],[(0,[z1,z2,z3,z4,z244,z5,z8]),(0,[z1,z245,z2,z3,z4,z5,z8]),(0,[z1,z128,z3,z4,z18,z5,z8]),(0,[z1,z2,z3,z246,z4,z5,z8]),(0,[z1,z2,z3,z4,z42,z5,z8])],[(0,[z1,z2,z3,z4,z247,z5,z8]),(0,[z1,z2,z37,z3,z4,z5,z10]),(0,[z1,z248,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z16,z20,z4,z5])],[],[(0,[z1,z2,z3,z63,z4,z208,z5]),(0,[z1,z2,z3,z4,z50,z60,z8]),(0,[z1,z2,z3,z4,z5,z249,z8]),(0,[z1,z2,z3,z16,z16,z4,z5])],[(0,[z113,z1,z2,z3,z4,z5,z250]),(0,[z1,z201,z2,z3,z63,z4,z5]),(0,[z251,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z252,z5,z8]),(0,[z1,z2,z253,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z254]),(0,[z1,z2,z3,z20,z77,z5,z8])],[(0,[z191,z1,z2,z3,z24,z4,z8]),(0,[z1,z2,z255,z3,z4,z5,z8]),(0,[z1,z162,z2,z3,z24,z4,z8]),(0,[z1,z2,z159,z3,z4,z256,z8])],[(0,[z1,z2,z3,z4,z257,z5,z8])],[(0,[z113,z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z258,z5,z8])],[(0,[z1,z259,z2,z3,z4,z5,z8]),(0,[z1,z2,z260,z3,z4,z5,z8])],[]],
   [[(0,[z1,z2,z3,z4,z5,z49,z8]),(0,[z1,z96,z2,z3,z4,z5,z51])],[(0,[z1,z2,z261,z3,z4,z5,z8]),(0,[z1,z2,z3,z262,z4,z208,z8]),(0,[z1,z2,z3,z263,z4,z5,z8]),(0,[z1,z2,z37,z3,z4,z5,z264])],[(0,[z1,z2,z3,z265,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z64,z8]),(0,[z207,z1,z2,z3,z20,z4,z8])],[(0,[z1,z2,z266,z3,z4,z5,z8]),(0,[z1,z2,z3,z16,z4,z5,z131]),(0,[z1,z2,z3,z24,z94,z5,z8]),(0,[z1,z2,z3,z63,z20,z4,z8]),(0,[z267,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z268,z3,z4,z5,z8]),(0,[z1,z2,z269,z3,z24,z4,z8])],[(0,[z1,z2,z3,z270,z4,z94,z5]),(0,[z1,z2,z4,z50,z5,z85,z8]),(1,[z1,z2,z3,z4,z5,z271]),(0,[z1,z2,z3,z4,z5,z8,z183]),(0,[z1,z2,z3,z210,z20,z4,z8]),(0,[z1,z2,z3,z20,z4,z134,z8])],[(1,[z272,z2,z3,z4,z5,z8]),(0,[z273,z1,z2,z3,z4,z5,z8])],[(0,[z145,z2,z3,z121,z4,z5,z8]),(0,[z1,z2,z3,z121,z4,z5,z8]),(0,[z75,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z274,z8]),(0,[z1,z2,z3,z4,z5,z275,z8]),(0,[z1,z2,z3,z276,z167,z4,z5]),(0,[z80,z1,z2,z3,z4,z5,z10])],[(0,[z1,z2,z3,z4,z5,z8,z277]),(0,[z278,z1,z2,z3,z4,z5,z8])],[(0,[z279,z1,z2,z3,z4,z5,z8]),(0,[z1,z201,z2,z3,z20,z4,z8]),(0,[z272,z1,z2,z3,z4,z5,z8]),(0,[z1,z280,z2,z3,z4,z5,z8]),(0,[z1,z2,z281,z3,z4,z5,z8]),(0,[z1,z2,z282,z3,z63,z4,z5])],[(0,[z283,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z284,z4,z5]),(1,[z1,z2,z3,z5,z8,z285])],[(0,[z1,z96,z2,z3,z4,z5,z10]),(0,[z1,z2,z2,z3,z4,z5,z51])],[(0,[z1,z162,z2,z3,z4,z5,z51])],[(0,[z1,z2,z3,z286,z4,z5,z8]),(0,[z1,z287,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z288])],[(0,[z1,z2,z289,z3,z4,z5,z8]),(0,[z290,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z235])],[(0,[z1,z2,z291,z3,z4,z5,z8]),(0,[z1,z128,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z4,z5,z292,z8]),(0,[z1,z2,z3,z4,z293,z5,z109]),(1,[z1,z2,z3,z4,z134,z64]),(0,[z1,z2,z3,z4,z5,z294,z8])]],
   [[(0,[z1,z2,z3,z4,z295,z5,z8])],[(0,[z1,z296,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z297,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z298,z10]),(1,[z1,z2,z3,z24,z34,z8])],[(0,[z299,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z85,z8])],[(0,[z1,z2,z3,z4,z5,z300,z8]),(0,[z1,z2,z23,z3,z63,z4,z5]),(0,[z1,z2,z3,z63,z4,z50,z5]),(0,[z1,z2,z3,z4,z218,z8,z235])],[],[],[(0,[z1,z2,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z24,z34,z4,z8]),(0,[z1,z2,z301,z3,z4,z5,z8])],[(0,[z1,z2,z3,z19,z16,z4,z5]),(0,[z1,z2,z3,z4,z5,z136,z8]),(0,[z1,z2,z73,z3,z16,z4,z5]),(0,[z1,z2,z37,z3,z63,z4,z5])],[(0,[z1,z2,z3,z302,z4,z5,z8]),(0,[z1,z2,z3,z4,z303,z5,z51]),(0,[z1,z2,z3,z304,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z305])],[(0,[z113,z150,z2,z3,z4,z5,z8]),(1,[z75,z2,z232,z4,z5,z8]),(0,[z1,z306,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z307,z5,z8]),(0,[z1,z2,z3,z4,z134,z5,z308]),(0,[z1,z108,z2,z3,z16,z4,z5])],[(0,[z1,z2,z3,z4,z5,z176,z8])],[(0,[z309,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z205,z5,z8]),(0,[z310,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z311,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z312]),(0,[z1,z2,z159,z3,z4,z5,z308])],[(1,[z1,z2,z3,z4,z123,z8]),(0,[z122,z1,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z24,z4,z35,z8])],[(0,[z1,z2,z3,z313,z4,z5,z8]),(1,[z141,z2,z3,z208,z5,z8]),(0,[z1,z2,z314,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z63,z4,z8]),(0,[z1,z2,z3,z4,z315,z5,z8])],[(0,[z1,z2,z100,z3,z4,z5,z316]),(0,[z1,z2,z3,z63,z4,z4,z5])]],
   [[(0,[z317,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z318,z8]),(0,[z1,z2,z3,z4,z5,z8,z319]),(0,[z1,z128,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z24,z24,z4,z8])],[(1,[z1,z177,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z320,z5,z8]),(0,[z1,z2,z3,z63,z4,z5,z8]),(0,[z1,z2,z321,z3,z63,z4,z5])],[(0,[z322,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z171,z8]),(0,[z1,z2,z3,z94,z5,z218,z8]),(0,[z1,z2,z23,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z5,z323,z8])],[(0,[z1,z2,z324,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z208,z8])],[(1,[z1,z2,z3,z4,z325,z8]),(0,[z1,z128,z2,z3,z326,z5,z8]),(0,[z1,z2,z3,z4,z5,z327,z8])],[(0,[z1,z2,z3,z4,z5,z328,z8])],[(0,[z1,z2,z100,z3,z24,z4,z8]),(0,[z1,z2,z329,z3,z4,z5,z8]),(0,[z1,z2,z37,z3,z20,z4,z8])],[(0,[z1,z201,z2,z3,z4,z5,z8]),(1,[z1,z194,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z330,z5,z8])],[(0,[z75,z1,z2,z3,z63,z4,z5]),(0,[z80,z1,z2,z3,z63,z4,z5])],[(0,[z331,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z64,z51]),(0,[z1,z2,z3,z332,z4,z5,z8])],[(0,[z333,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z50,z71,z8])],[(1,[z1,z2,z197,z4,z5,z8]),(0,[z1,z2,z3,z4,z208,z5,z10]),(0,[z334,z1,z2,z3,z4,z5,z8]),(0,[z1,z335,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z256,z8]),(0,[z1,z2,z3,z24,z336,z4,z8])],[(0,[z150,z1,z2,z3,z24,z4,z8]),(1,[z1,z2,z3,z54,z5,z8]),(0,[z1,z337,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z84,z8,z26]),(1,[z1,z2,z3,z4,z338,z8]),(0,[z1,z96,z2,z3,z63,z4,z5]),(0,[z1,z2,z3,z4,z5,z51,z51])],[(0,[z145,z75,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z339,z5,z8])],[(0,[z126,z1,z2,z3,z4,z5,z51]),(0,[z122,z1,z2,z3,z4,z5,z51]),(0,[z1,z280,z2,z3,z20,z4,z8])],[(0,[z1,z2,z3,z4,z5,z340,z8]),(0,[z1,z341,z2,z3,z4,z5,z8])]],
   [[(0,[z2,z3,z4,z5,z6,z8,z131]),(0,[z342,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z343,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z5,z51])],[(0,[z344,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z156,z3,z24,z4,z8]),(0,[z1,z2,z345,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z346,z5,z8])],[],[(0,[z1,z2,z3,z4,z5,z347,z8])],[(0,[z1,z201,z2,z3,z4,z5,z348]),(0,[z1,z2,z349,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z350,z5,z8])],[(0,[z1,z351,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z352,z4,z5,z8]),(0,[z1,z2,z353,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z208,z5,z8]),(0,[z1,z2,z3,z4,z60,z8,z26]),(0,[z1,z2,z282,z3,z4,z5,z8]),(0,[z1,z2,z354,z3,z4,z5,z8]),(0,[z1,z2,z3,z355,z4,z5,z8])],[(0,[z75,z1,z2,z3,z20,z4,z8]),(0,[z1,z2,z232,z3,z24,z4,z8]),(0,[z1,z2,z3,z4,z356,z5,z8]),(0,[z1,z2,z100,z3,z4,z5,z51]),(0,[z80,z1,z2,z3,z20,z4,z8])],[(0,[z1,z2,z3,z4,z357,z5,z8]),(0,[z1,z358,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z50,z5,z8]),(0,[z1,z2,z3,z4,z91,z5,z8])],[(0,[z211,z1,z2,z3,z4,z5,z8]),(0,[z126,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z359,z5,z8]),(0,[z1,z2,z3,z4,z5,z85,z51])],[(0,[z1,z2,z3,z360,z4,z5,z8]),(0,[z1,z2,z3,z4,z35,z5,z10]),(0,[z1,z2,z3,z4,z5,z361,z8]),(0,[z1,z2,z3,z4,z5,z362,z8])],[(0,[z1,z96,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z5,z10,z363]),(0,[z1,z2,z3,z4,z5,z8,z271]),(0,[z1,z2,z364,z3,z4,z5,z8])],[(0,[z68,z1,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z5,z123,z8])],[(0,[z150,z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z24,z4,z50,z8])],[(0,[z1,z2,z365,z3,z4,z5,z8])],[(0,[z1,z2,z3,z99,z4,z5,z8]),(0,[z1,z2,z3,z366,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z8,z92])]],
   [[(1,[z1,z2,z3,z157,z4,z8]),(0,[z367,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z23,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z368,z8]),(0,[z1,z2,z3,z4,z369,z5,z10])],[(0,[z1,z2,z3,z13,z5,z60,z8]),(0,[z1,z2,z370,z3,z4,z5,z8]),(0,[z1,z2,z132,z4,z5,z8,z79])],[(0,[z1,z2,z3,z4,z5,z325,z8]),(0,[z1,z2,z156,z3,z4,z5,z51])],[(0,[z1,z2,z3,z371,z4,z5,z8]),(0,[z1,z2,z372,z3,z4,z5,z8]),(0,[z1,z2,z373,z3,z4,z5,z8]),(0,[z1,z2,z37,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z374,z5,z8])],[(0,[z375,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z35,z5,z8])],[(0,[z1,z2,z376,z3,z4,z5,z8]),(0,[z2,z3,z93,z4,z208,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z363])],[],[(0,[z68,z1,z2,z3,z4,z187,z8]),(0,[z126,z1,z2,z3,z4,z60,z8]),(0,[z377,z1,z2,z3,z4,z5,z8])],[(0,[z0,z1,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z24,z4,z4,z8])],[(0,[z1,z2,z3,z4,z5,z240,z8]),(0,[z1,z2,z3,z4,z5,z256,z8]),(0,[z1,z2,z3,z4,z378,z5,z8])],[(0,[z113,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z338,z8]),(1,[z1,z2,z3,z4,z5,z101]),(0,[z379,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z380,z4,z5,z8])],[(0,[z1,z2,z3,z4,z381,z5,z8]),(0,[z1,z162,z2,z3,z35,z5,z8]),(0,[z1,z2,z3,z4,z5,z382,z8]),(1,[z1,z2,z100,z34,z5,z8]),(0,[z383,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z78,z5,z308]),(0,[z1,z2,z3,z336,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z384,z8]),(0,[z1,z2,z3,z4,z5,z8,z385]),(0,[z1,z2,z3,z4,z5,z8,z386]),(0,[z1,z2,z321,z3,z4,z5,z8]),(0,[z1,z2,z387,z3,z4,z5,z8])],[(0,[z191,z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z388,z5,z8]),(0,[z55,z1,z2,z3,z4,z78,z5]),(0,[z1,z2,z4,z5,z308,z8,z79]),(0,[z1,z2,z3,z24,z4,z308,z8]),(0,[z389,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z390,z8]),(0,[z1,z2,z3,z391,z24,z4,z8])],[(0,[z1,z2,z392,z3,z4,z5,z8]),(0,[z1,z2,z159,z3,z24,z4,z8])],[(0,[z1,z2,z3,z4,z5,z348,z8]),(0,[z1,z2,z3,z393,z24,z4,z8])],[(0,[z0,z1,z2,z3,z4,z5,z131])],[],[(0,[z80,z1,z2,z3,z4,z5,z8]),(0,[z75,z1,z2,z3,z4,z5,z8]),(0,[z1,z394,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z189,z4,z8])],[(0,[z395,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z293,z5])],[(0,[z1,z28,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z20,z4,z50,z8]),(0,[z1,z2,z3,z4,z50,z5,z11]),(0,[z1,z2,z3,z63,z4,z5,z79])],[(1,[z1,z2,z3,z4,z330,z8]),(0,[z1,z2,z3,z34,z5,z218,z8]),(0,[z1,z2,z3,z103,z16,z4,z5])],[(0,[z1,z2,z3,z185,z4,z5,z8]),(0,[z1,z96,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z20,z4,z8,z92])],[(0,[z191,z1,z2,z3,z4,z5,z10]),(0,[z126,z1,z2,z3,z63,z4,z5]),(0,[z1,z162,z2,z3,z4,z5,z10]),(0,[z396,z1,z2,z3,z4,z5,z51])],[(0,[z1,z2,z3,z4,z5,z397,z8])],[(0,[z1,z2,z398,z3,z4,z5,z8]),(0,[z1,z2,z3,z167,z77,z5,z8]),(0,[z1,z2,z3,z4,z5,z51,z399]),(1,[z1,z2,z3,z4,z137,z8])],[(0,[z1,z400,z2,z3,z4,z5,z8]),(0,[z1,z2,z401,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z402,z4,z8])],[(0,[z0,z1,z2,z3,z4,z227,z8])],[(0,[z75,z2,z232,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z18,z84,z8]),(0,[z1,z2,z3,z4,z5,z298,z8]),(0,[z1,z2,z3,z20,z4,z64,z8]),(0,[z1,z2,z3,z63,z52,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z403]),(0,[z1,z2,z3,z4,z5,z404,z8])],[(0,[z1,z405,z2,z3,z4,z5,z8]),(0,[z406,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z407,z4,z5,z8])],[(0,[z1,z2,z3,z20,z4,z4,z8])],[(0,[z1,z2,z2,z3,z4,z5,z8]),(0,[z408,z1,z2,z3,z4,z5,z8]),(0,[z409,z1,z2,z3,z4,z5,z8]),(0,[z410,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z411,z5,z8]),(0,[z1,z2,z3,z63,z4,z5,z26])],[(0,[z412,z1,z2,z3,z4,z5,z8]),(0,[z68,z1,z2,z3,z4,z133,z8]),(0,[z1,z162,z2,z3,z4,z5,z8]),(0,[z1,z90,z2,z3,z167,z5,z8]),(0,[z413,z1,z2,z3,z4,z5,z8]),(0,[z389,z1,z2,z3,z63,z4,z5])],[],[(0,[z1,z2,z3,z414,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z415,z8])],[(0,[z201,z2,z32,z3,z4,z5,z8]),(0,[z1,z2,z3,z262,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z416,z8]),(0,[z1,z2,z3,z24,z4,z417,z8]),(0,[z1,z2,z3,z5,z218,z8,z92])],[(0,[z191,z1,z2,z3,z4,z60,z8]),(0,[z1,z2,z3,z24,z4,z6,z8]),(0,[z1,z2,z3,z4,z5,z418,z8])],[(0,[z1,z2,z3,z4,z419,z5,z8])],[(0,[z1,z2,z3,z4,z5,z250,z8]),(0,[z1,z420,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z24,z4,z51])],[(0,[z113,z1,z2,z3,z63,z4,z5]),(0,[z1,z2,z121,z19,z4,z5,z8]),(0,[z1,z2,z421,z3,z4,z5,z51]),(0,[z1,z422,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z423,z8]),(0,[z1,z2,z3,z20,z4,z8,z424]),(1,[z1,z2,z3,z20,z77,z8])],[(0,[z1,z2,z3,z121,z16,z4,z5]),(0,[z1,z2,z3,z4,z425,z5,z8]),(0,[z1,z2,z3,z426,z63,z4,z5])],[(0,[z1,z128,z2,z3,z4,z5,z10]),(0,[z1,z2,z269,z3,z4,z5,z8]),(0,[z427,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z428]),(0,[z1,z2,z3,z429,z4,z5,z8])],[(0,[z1,z2,z3,z20,z4,z85,z8])]],
   [[(0,[z145,z1,z2,z3,z24,z4,z8]),(1,[z1,z2,z3,z4,z5,z129])],[(0,[z75,z2,z32,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z303,z5,z8])],[(0,[z145,z1,z2,z232,z4,z5,z8]),(0,[z1,z2,z3,z430,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z64,z6]),(0,[z1,z2,z3,z24,z35,z5,z8]),(0,[z431,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z432,z4,z5,z8]),(1,[z1,z2,z3,z433,z5,z8])],[(0,[z150,z1,z201,z3,z4,z5,z8]),(0,[z434,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z20,z34,z4,z8]),(0,[z1,z2,z3,z4,z134,z64,z8])],[(0,[z1,z2,z3,z4,z5,z435,z8]),(0,[z1,z28,z2,z3,z4,z5,z415])],[],[(0,[z113,z1,z201,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z308,z51]),(0,[z1,z2,z3,z4,z5,z203,z8]),(1,[z1,z2,z3,z24,z4,z10])],[(0,[z1,z2,z156,z232,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z64,z10])],[(0,[z436,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z437])],[(0,[z1,z2,z3,z295,z5,z60,z8]),(0,[z1,z2,z3,z20,z4,z35,z8]),(0,[z1,z2,z3,z4,z438,z5,z8])],[(0,[z113,z1,z2,z3,z20,z4,z8]),(0,[z191,z1,z2,z3,z63,z4,z5]),(0,[z1,z2,z439,z3,z4,z5,z8]),(0,[z1,z162,z2,z3,z63,z4,z5]),(0,[z1,z2,z440,z3,z4,z5,z8])],[(0,[z122,z1,z2,z3,z4,z5,z10])],[(0,[z1,z2,z3,z441,z4,z5,z8]),(0,[z431,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z442,z8])],[(0,[z443,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z444,z3,z4,z5,z8]),(0,[z1,z2,z445,z3,z4,z5,z8]),(0,[z1,z2,z3,z284,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z8,z446]),(0,[z1,z2,z159,z3,z4,z5,z64])],[(0,[z1,z2,z3,z4,z5,z447,z8]),(0,[z1,z2,z3,z167,z94,z5,z8]),(0,[z1,z2,z3,z24,z4,z5,z10])]],
   [[(0,[z1,z2,z3,z20,z4,z208,z8]),(0,[z1,z2,z3,z4,z448,z5,z8])],[(0,[z145,z1,z2,z3,z4,z5,z51]),(1,[z1,z2,z3,z226,z4,z5]),(0,[z1,z2,z3,z4,z449,z5,z8])],[(0,[z1,z2,z3,z4,z5,z64,z8])],[(0,[z1,z2,z450,z3,z4,z5,z8]),(0,[z1,z33,z2,z3,z24,z4,z8]),(1,[z1,z2,z3,z42,z5,z8])],[(0,[z1,z2,z3,z4,z451,z5,z8]),(0,[z1,z2,z269,z3,z63,z4,z5])],[(0,[z1,z2,z3,z4,z452,z5,z8]),(0,[z1,z2,z100,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z453,z8]),(0,[z1,z2,z3,z63,z20,z4,z5])],[(0,[z1,z2,z3,z24,z4,z218,z8])],[(0,[z126,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z85,z10]),(0,[z1,z2,z3,z4,z5,z454,z8]),(0,[z1,z2,z3,z63,z5,z218,z8])],[(0,[z1,z455,z2,z3,z4,z5,z8]),(0,[z122,z1,z28,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z456,z8]),(0,[z457,z1,z2,z3,z4,z5,z8])],[(0,[z1,z162,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z24,z4,z5,z8])],[(0,[z150,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z232,z3,z4,z5,z51]),(0,[z122,z1,z2,z3,z4,z5,z458]),(0,[z1,z2,z3,z24,z4,z8,z51]),(0,[z1,z2,z37,z23,z4,z5,z8])],[(0,[z1,z2,z32,z3,z24,z4,z8]),(0,[z1,z2,z3,z459,z4,z5,z8])],[(0,[z1,z201,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z5,z460,z8]),(0,[z1,z2,z3,z4,z5,z8,z461]),(0,[z1,z2,z3,z4,z462,z5,z8]),(1,[z1,z2,z37,z4,z50,z8])],[(1,[z1,z2,z3,z4,z114,z8]),(0,[z1,z2,z3,z24,z4,z60,z8]),(0,[z1,z2,z3,z20,z4,z5,z51]),(0,[z1,z2,z3,z463,z4,z5,z8])],[(0,[z2,z32,z3,z121,z4,z5,z8]),(0,[z122,z1,z2,z3,z4,z464,z8]),(1,[z1,z2,z3,z4,z5,z163]),(0,[z1,z128,z2,z3,z63,z4,z5]),(0,[z1,z2,z3,z4,z369,z5,z8]),(0,[z143,z1,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z332,z16,z4,z5])]],
   [[(0,[z1,z2,z100,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z78,z134,z8])],[(0,[z1,z2,z3,z63,z4,z5,z131]),(0,[z1,z2,z156,z3,z4,z5,z10])],[(0,[z1,z2,z3,z208,z94,z5,z8]),(0,[z1,z2,z3,z4,z5,z85,z8]),(0,[z1,z2,z3,z4,z465,z5,z8])],[],[(0,[z1,z2,z3,z16,z4,z84,z5]),(0,[z466,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z467,z167,z4,z5]),(0,[z1,z33,z2,z3,z4,z5,z51])],[(1,[z1,z2,z3,z4,z5,z468]),(0,[z1,z2,z3,z4,z469,z5,z8])],[(0,[z150,z1,z2,z3,z4,z5,z8]),(0,[z1,z470,z2,z3,z4,z5,z8]),(0,[z1,z2,z232,z3,z4,z5,z10]),(0,[z0,z1,z2,z3,z4,z325,z8]),(0,[z1,z2,z3,z471,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z10,z8]),(0,[z1,z2,z3,z16,z4,z78,z5])],[(0,[z1,z90,z162,z3,z4,z5,z8]),(0,[z1,z90,z2,z3,z24,z4,z8])],[(0,[z1,z2,z472,z3,z4,z5,z8]),(1,[z1,z2,z3,z24,z35,z8]),(0,[z1,z2,z3,z16,z4,z18,z5])],[(0,[z113,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z229,z3,z4,z5,z8])],[(0,[z1,z473,z2,z3,z4,z5,z8]),(0,[z1,z33,z2,z3,z4,z5,z474]),(0,[z1,z2,z3,z276,z4,z5,z10]),(0,[z1,z2,z3,z426,z4,z5,z8]),(0,[z1,z2,z3,z24,z34,z5,z8])],[(0,[z1,z2,z3,z4,z5,z10,z475])],[(0,[z1,z2,z476,z3,z4,z5,z8])],[(0,[z1,z2,z32,z3,z4,z5,z51]),(0,[z122,z1,z2,z3,z63,z4,z5]),(1,[z1,z2,z3,z24,z16,z4])],[(1,[z1,z2,z3,z295,z5,z8]),(0,[z1,z128,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z477,z5,z8])],[(0,[z478,z1,z2,z3,z4,z5,z8]),(0,[z1,z248,z2,z3,z16,z4,z5]),(1,[z1,z2,z3,z429,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z4,z5,z8]),(0,[z143,z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z100,z3,z34,z5,z8]),(0,[z1,z2,z3,z24,z63,z4,z5]),(0,[z1,z2,z3,z4,z5,z479,z8]),(0,[z1,z2,z440,z3,z20,z4,z8]),(0,[z1,z2,z3,z20,z4,z218,z8])],[(0,[z1,z2,z3,z4,z5,z480,z8]),(0,[z1,z2,z3,z4,z5,z51,z152]),(0,[z1,z2,z3,z20,z481,z4,z8])],[(0,[z1,z2,z3,z4,z134,z5,z51])],[(0,[z2,z3,z4,z84,z5,z60,z8])],[(0,[z1,z482,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z192,z4,z35,z8]),(0,[z1,z2,z132,z3,z4,z5,z308])],[(0,[z55,z1,z2,z132,z3,z4,z5]),(0,[z1,z2,z159,z3,z4,z5,z51]),(0,[z1,z2,z3,z20,z4,z8,z51]),(1,[z1,z2,z3,z304,z4,z8])],[(0,[z1,z2,z3,z4,z5,z483,z8]),(0,[z1,z2,z100,z3,z63,z4,z5]),(0,[z1,z2,z23,z3,z16,z4,z5]),(0,[z1,z2,z3,z16,z77,z5,z8])],[(0,[z484,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z485,z4,z5,z8])],[(0,[z191,z1,z2,z3,z4,z5,z8]),(0,[z1,z90,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z486,z4,z5,z8]),(1,[z1,z2,z3,z487,z4,z8])],[(1,[z1,z2,z185,z4,z5,z8]),(0,[z1,z2,z3,z4,z488,z5,z8]),(0,[z1,z2,z73,z4,z94,z5,z8])],[(0,[z1,z2,z37,z3,z16,z4,z5]),(0,[z1,z2,z3,z16,z4,z77,z5])],[(1,[z113,z32,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z489,z8]),(0,[z1,z2,z490,z3,z4,z5,z8]),(0,[z1,z28,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z491,z5,z8]),(0,[z1,z2,z3,z4,z5,z101,z8])],[(0,[z150,z1,z2,z3,z63,z4,z5]),(0,[z126,z1,z2,z3,z20,z4,z8]),(0,[z122,z1,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z20,z4,z308,z8])],[(1,[z1,z2,z3,z195,z5,z8]),(0,[z141,z68,z2,z3,z4,z5,z8]),(0,[z1,z492,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z167,z4,z5,z51]),(0,[z1,z2,z3,z4,z5,z493,z8]),(0,[z1,z2,z3,z4,z5,z218,z51])],[(0,[z1,z128,z2,z3,z4,z71,z8]),(0,[z1,z2,z3,z4,z494,z5,z8]),(0,[z1,z2,z3,z4,z5,z495,z8]),(0,[z1,z2,z3,z77,z5,z218,z8])],[(0,[z141,z1,z2,z3,z77,z5,z8]),(0,[z1,z2,z3,z24,z20,z4,z8]),(1,[z1,z2,z3,z63,z20,z4])]],
   [[(0,[z1,z2,z159,z3,z4,z5,z10])],[(0,[z1,z2,z3,z4,z496,z5,z8]),(0,[z1,z2,z3,z4,z497,z5,z60]),(0,[z1,z2,z3,z4,z5,z498,z8]),(0,[z1,z2,z3,z4,z5,z131,z26]),(0,[z499,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z16,z4,z5,z308]),(0,[z500,z1,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z24,z16,z4,z8])],[(0,[z113,z1,z2,z3,z4,z501,z8]),(0,[z410,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z502,z4,z5,z8]),(0,[z1,z2,z3,z4,z503,z5,z8]),(0,[z1,z2,z156,z3,z63,z4,z5]),(0,[z1,z2,z3,z16,z167,z4,z5])],[(0,[z396,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z16,z4,z94,z5]),(0,[z504,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z505,z3,z4,z5,z8]),(0,[z1,z2,z159,z132,z4,z5,z8]),(0,[z506,z1,z2,z3,z63,z4,z5])],[(0,[z1,z2,z3,z4,z5,z10,z92])],[(0,[z113,z2,z32,z3,z4,z5,z8]),(0,[z141,z2,z3,z4,z208,z5,z8]),(0,[z1,z2,z3,z4,z5,z60,z51]),(0,[z1,z2,z3,z507,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z228]),(0,[z1,z2,z100,z3,z20,z4,z8])],[(0,[z1,z28,z2,z3,z4,z5,z10]),(0,[z1,z128,z2,z3,z4,z5,z508]),(0,[z1,z2,z3,z304,z4,z94,z8]),(0,[z1,z2,z509,z3,z4,z5,z8])],[(0,[z1,z2,z232,z3,z63,z4,z5]),(0,[z191,z1,z2,z3,z4,z5,z510]),(0,[z1,z2,z3,z4,z50,z84,z8]),(0,[z1,z2,z3,z4,z78,z85,z8]),(0,[z511,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z512,z3,z4,z5,z8]),(0,[z1,z2,z3,z513,z4,z5,z8]),(0,[z1,z514,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z487,z4,z5,z8]),(0,[z1,z2,z3,z433,z4,z5,z8])],[],[(0,[z1,z2,z3,z4,z515,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z516]),(0,[z1,z2,z3,z391,z4,z5,z8])],[(0,[z150,z1,z2,z3,z20,z4,z8]),(0,[z75,z1,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z50,z18,z8]),(0,[z1,z2,z159,z3,z4,z517,z8]),(0,[z80,z1,z2,z3,z16,z4,z5])],[(0,[z518,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z519,z3,z4,z5,z8]),(0,[z1,z128,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z43,z5,z8]),(0,[z1,z2,z520,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z521,z5,z8])],[(0,[z1,z2,z3,z4,z5,z522,z8]),(0,[z1,z2,z3,z4,z5,z228,z8]),(0,[z1,z2,z3,z4,z5,z10,z51]),(1,[z1,z2,z3,z4,z5,z316]),(0,[z1,z2,z3,z523,z4,z5,z8])],[(0,[z1,z2,z524,z3,z4,z5,z8]),(0,[z1,z2,z3,z525,z4,z5,z8]),(0,[z1,z2,z3,z4,z134,z5,z64])],[(0,[z1,z2,z3,z4,z5,z308,z6]),(0,[z122,z526,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z71,z8]),(0,[z1,z96,z2,z3,z16,z4,z5]),(0,[z1,z527,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z4,z5,z8,z92])]],
   [[(0,[z1,z2,z3,z63,z523,z4,z5])],[(0,[z528,z1,z2,z3,z4,z5,z8]),(0,[z1,z529,z2,z3,z4,z5,z8]),(0,[z1,z2,z156,z3,z20,z4,z8])],[(1,[z1,z90,z3,z35,z5,z8]),(0,[z1,z2,z3,z4,z5,z51,z62])],[(0,[z1,z2,z3,z222,z4,z35,z8]),(0,[z1,z2,z530,z3,z4,z5,z8]),(0,[z1,z531,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z308,z10]),(1,[z1,z2,z3,z24,z4,z8])],[(0,[z1,z2,z3,z4,z5,z8,z163]),(0,[z532,z1,z2,z3,z4,z5,z8])],[(0,[z1,z32,z3,z19,z4,z5,z8]),(0,[z1,z2,z533,z3,z4,z5,z8]),(0,[z1,z2,z3,z534,z4,z5,z8]),(0,[z1,z2,z3,z20,z4,z6,z8]),(0,[z1,z2,z3,z535,z4,z5,z8]),(0,[z1,z2,z3,z35,z77,z5,z8]),(0,[z1,z2,z3,z4,z536,z5,z8])],[(0,[z1,z2,z537,z3,z4,z5,z8]),(0,[z68,z2,z3,z93,z4,z5,z8]),(0,[z406,z1,z2,z3,z16,z4,z5])],[(0,[z1,z2,z3,z4,z5,z51,z26]),(1,[z1,z2,z3,z4,z184,z8])],[(0,[z122,z1,z2,z3,z4,z5,z300]),(0,[z1,z2,z3,z16,z94,z5,z8]),(0,[z1,z2,z3,z4,z293,z5,z8])],[(0,[z538,z1,z2,z3,z4,z5,z8]),(0,[z122,z1,z2,z3,z4,z5,z8]),(0,[z539,z1,z2,z3,z4,z5,z8])],[(0,[z540,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z468]),(0,[z1,z2,z3,z4,z5,z541,z8]),(0,[z542,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z543,z5,z8]),(0,[z1,z2,z3,z284,z4,z5,z8])],[(0,[z145,z1,z2,z3,z343,z5,z8]),(0,[z191,z1,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z16,z4,z5,z71]),(1,[z1,z2,z159,z4,z5,z308])],[(1,[z150,z201,z3,z4,z5,z8]),(0,[z544,z1,z2,z3,z4,z5,z8])],[(0,[z145,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z94,z77,z5,z8]),(0,[z1,z2,z3,z4,z5,z11,z8]),(0,[z1,z2,z3,z4,z5,z308,z8])]],
   [[(1,[z1,z2,z3,z534,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z545]),(0,[z1,z2,z3,z4,z227,z5,z8]),(0,[z1,z2,z3,z546,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z129,z8]),(0,[z1,z2,z3,z4,z547,z5,z8])],[(0,[z1,z2,z3,z4,z5,z202,z8]),(0,[z1,z2,z159,z3,z63,z4,z5]),(0,[z1,z548,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z250]),(0,[z1,z2,z3,z4,z549,z5,z8]),(0,[z1,z2,z3,z550,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z551]),(0,[z1,z2,z3,z4,z5,z8,z424])],[(0,[z1,z552,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z51]),(0,[z1,z553,z2,z3,z4,z5,z8])],[(0,[z1,z2,z554,z3,z4,z5,z8])],[(0,[z1,z2,z3,z167,z93,z5,z8]),(0,[z1,z2,z555,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z517,z5,z8])],[(0,[z1,z556,z2,z3,z4,z5,z8]),(0,[z1,z557,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z78,z5,z51]),(0,[z1,z2,z3,z4,z85,z64,z8])],[(0,[z1,z28,z2,z3,z63,z4,z5])],[(0,[z1,z2,z3,z4,z558,z5,z8]),(0,[z1,z2,z3,z559,z4,z5,z8]),(0,[z1,z2,z37,z3,z4,z5,z271])],[(0,[z113,z1,z2,z3,z4,z5,z67]),(0,[z560,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z139,z3,z4,z5,z8]),(0,[z1,z2,z3,z20,z4,z71,z8]),(1,[z1,z2,z3,z326,z5,z8]),(0,[z1,z2,z3,z467,z4,z5,z51]),(0,[z1,z2,z3,z4,z50,z5,z183]),(0,[z1,z2,z132,z3,z24,z4,z8]),(0,[z1,z2,z3,z16,z4,z5,z109])],[(0,[z1,z1,z2,z3,z4,z5,z8]),(0,[z145,z1,z2,z3,z4,z5,z8]),(0,[z561,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z562,z4,z5,z8])],[(1,[z1,z2,z3,z563,z4,z5]),(1,[z1,z2,z3,z4,z5,z474])],[(0,[z191,z2,z3,z4,z5,z60,z8]),(0,[z1,z2,z3,z20,z4,z5,z10]),(0,[z1,z2,z3,z4,z564,z5,z8])],[(0,[z0,z2,z3,z4,z5,z8,z131])],[(0,[z1,z2,z3,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z565])],[(0,[z1,z2,z3,z167,z208,z5,z8]),(0,[z1,z2,z156,z3,z4,z5,z8])]],
   [[(0,[z506,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z142,z4,z5,z8]),(0,[z1,z2,z3,z566,z4,z5,z8]),(0,[z1,z2,z567,z3,z4,z5,z51]),(0,[z1,z2,z100,z3,z4,z53,z8])],[(0,[z1,z28,z201,z3,z4,z5,z8]),(0,[z1,z2,z3,z534,z4,z208,z5]),(0,[z1,z2,z3,z4,z497,z5,z8]),(1,[z1,z2,z3,z4,z5,z415]),(1,[z1,z2,z3,z16,z34,z5]),(1,[z1,z2,z3,z4,z91,z8])],[(0,[z568,z1,z2,z3,z4,z5,z8]),(0,[z55,z1,z2,z3,z24,z4,z8]),(0,[z1,z33,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z569,z8]),(0,[z1,z2,z3,z4,z78,z50,z8])],[(0,[z1,z2,z3,z4,z5,z570,z8])],[(0,[z1,z2,z232,z3,z4,z5,z8]),(0,[z571,z1,z2,z3,z4,z5,z8])],[(0,[z141,z1,z2,z3,z93,z5,z8]),(0,[z1,z2,z3,z270,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z572,z8]),(0,[z0,z1,z2,z3,z4,z78,z5]),(0,[z1,z28,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z5,z71,z51]),(0,[z1,z573,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z574,z8]),(0,[z1,z2,z3,z4,z5,z131,z79]),(0,[z1,z2,z73,z3,z94,z5,z8]),(0,[z1,z2,z3,z4,z575,z5,z8]),(0,[z1,z2,z3,z20,z4,z5,z8])],[(0,[z1,z2,z3,z276,z4,z5,z8]),(0,[z1,z2,z576,z3,z4,z5,z8]),(0,[z1,z2,z530,z3,z20,z4,z8])],[(0,[z68,z1,z2,z3,z77,z5,z8]),(0,[z1,z90,z2,z3,z35,z5,z8]),(0,[z1,z2,z3,z35,z94,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z475]),(0,[z1,z553,z2,z3,z63,z4,z5])],[(0,[z1,z28,z2,z3,z4,z5,z577]),(0,[z1,z2,z132,z3,z4,z5,z51])],[(0,[z1,z2,z32,z3,z4,z5,z10]),(0,[z1,z2,z3,z20,z4,z60,z8]),(1,[z1,z2,z3,z4,z5,z264]),(1,[z1,z2,z3,z4,z517,z8]),(0,[z1,z2,z3,z4,z5,z578,z8])],[(0,[z55,z1,z2,z3,z4,z134,z5]),(0,[z1,z2,z3,z4,z579,z5,z8]),(0,[z1,z2,z580,z3,z4,z5,z10]),(0,[z1,z2,z3,z16,z4,z5,z85])],[(0,[z126,z1,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z581,z5,z8]),(0,[z1,z2,z3,z4,z5,z582,z8])],[(0,[z143,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z16,z4,z5,z92])],[(0,[z141,z1,z2,z3,z208,z5,z8]),(0,[z141,z1,z2,z3,z24,z4,z8]),(1,[z1,z2,z3,z4,z5,z458]),(0,[z1,z2,z159,z4,z5,z308,z8])]],
   [[(0,[z145,z1,z2,z3,z63,z4,z5]),(0,[z122,z1,z2,z156,z4,z5,z8]),(0,[z1,z2,z3,z4,z134,z5,z10]),(1,[z1,z2,z3,z16,z77,z5])],[(0,[z1,z2,z3,z4,z5,z71,z10]),(0,[z1,z2,z583,z3,z4,z5,z8]),(1,[z1,z2,z3,z16,z5,z92]),(0,[z1,z584,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z64,z131]),(0,[z1,z2,z3,z4,z78,z5,z64])],[(0,[z55,z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z20,z4,z10,z8]),(1,[z1,z2,z3,z4,z585,z8])],[],[(0,[z1,z2,z3,z4,z5,z586,z8]),(0,[z1,z2,z587,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z51,z131]),(0,[z1,z2,z3,z4,z588,z5,z8])],[(0,[z1,z2,z32,z3,z4,z5,z8]),(0,[z1,z90,z2,z3,z4,z5,z10]),(0,[z1,z2,z100,z3,z16,z4,z5])],[(0,[z1,z2,z3,z16,z4,z5,z51])],[(0,[z1,z2,z3,z20,z175,z4,z8])],[(0,[z1,z194,z2,z3,z4,z5,z8]),(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z143,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z16,z94,z5])],[(0,[z1,z2,z3,z589,z4,z5,z8]),(1,[z1,z2,z3,z20,z4,z51])],[(0,[z1,z2,z3,z167,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z218,z10]),(0,[z1,z2,z3,z4,z134,z5,z8])],[(0,[z150,z1,z2,z3,z16,z4,z5]),(1,[z1,z2,z3,z4,z5,z274]),(0,[z1,z2,z590,z3,z4,z5,z10]),(0,[z1,z591,z2,z3,z4,z5,z8]),(0,[z1,z592,z2,z3,z4,z5,z8])],[(0,[z593,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z23,z4,z85,z8])],[(0,[z1,z2,z594,z3,z4,z5,z8]),(0,[z55,z1,z2,z3,z4,z5,z10]),(0,[z1,z128,z33,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z51,z79]),(0,[z1,z2,z159,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z595]),(0,[z1,z2,z3,z4,z5,z200,z8])],[(0,[z113,z1,z2,z3,z16,z4,z5]),(0,[z145,z1,z2,z3,z20,z4,z8]),(0,[z596,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z393,z4,z5,z8]),(0,[z1,z2,z3,z4,z134,z60,z8]),(0,[z1,z2,z597,z3,z4,z5,z8]),(0,[z1,z2,z3,z598,z4,z5,z8]),(0,[z1,z2,z3,z599,z4,z5,z8])]],
   [[(0,[z141,z1,z2,z3,z4,z5,z51]),(0,[z1,z96,z3,z4,z5,z8,z51])],[(0,[z1,z2,z3,z208,z35,z5,z8]),(1,[z1,z2,z3,z24,z218,z8])],[],[(0,[z1,z600,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z60,z10]),(0,[z1,z33,z2,z3,z63,z4,z5]),(0,[z1,z2,z73,z100,z4,z5,z8])],[(0,[z1,z2,z601,z3,z4,z5,z8]),(0,[z1,z28,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z19,z24,z4,z8])],[(1,[z1,z2,z3,z20,z4,z10]),(0,[z1,z2,z3,z34,z77,z5,z8])],[(0,[z1,z2,z602,z3,z4,z5,z8]),(0,[z126,z1,z2,z3,z4,z84,z8]),(0,[z1,z2,z3,z4,z5,z10,z6]),(0,[z603,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z604,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z605]),(0,[z1,z2,z132,z3,z4,z5,z64]),(0,[z1,z2,z3,z4,z5,z218,z8])],[(0,[z1,z2,z590,z3,z4,z5,z8])],[(0,[z1,z2,z421,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z606,z5,z8]),(1,[z1,z2,z3,z63,z5,z218])],[(0,[z1,z2,z324,z3,z121,z4,z5]),(0,[z1,z2,z232,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z464,z5,z8])],[(0,[z1,z2,z607,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z608,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z51]),(0,[z1,z2,z3,z4,z5,z10,z10]),(0,[z1,z2,z3,z226,z4,z94,z5])],[(0,[z1,z2,z32,z3,z63,z4,z5]),(0,[z55,z0,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z609,z8]),(0,[z1,z2,z3,z20,z20,z4,z8]),(0,[z1,z2,z3,z610,z4,z5,z8])],[(0,[z611,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z16,z355,z4,z5])],[(0,[z191,z1,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z5,z60,z8]),(0,[z1,z162,z2,z3,z16,z4,z5])],[(0,[z1,z612,z2,z3,z4,z5,z8]),(0,[z613,z1,z2,z3,z4,z5,z8]),(0,[z143,z1,z2,z3,z63,z4,z5]),(0,[z1,z2,z3,z119,z4,z5,z8])]],
   [[(0,[z1,z2,z614,z3,z4,z5,z8]),(0,[z1,z2,z3,z16,z525,z4,z5])],[(0,[z615,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z192,z4,z5,z8]),(1,[z1,z2,z3,z276,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z474]),(0,[z1,z2,z3,z4,z616,z5,z8]),(0,[z1,z2,z3,z4,z5,z617,z8])],[(0,[z1,z526,z2,z3,z4,z5,z8]),(0,[z1,z33,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z5,z585,z8])],[(0,[z1,z618,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z34,z167,z5,z8]),(0,[z1,z619,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z179,z5,z109]),(0,[z1,z2,z3,z16,z4,z5,z64])],[(0,[z620,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z577]),(0,[z1,z2,z3,z563,z4,z5,z8]),(0,[z621,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z8,z29])],[(0,[z1,z2,z3,z19,z4,z5,z51])],[],[(0,[z1,z2,z3,z4,z84,z85,z8]),(0,[z1,z90,z2,z3,z63,z4,z5]),(0,[z154,z1,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z155,z24,z4,z8])],[(0,[z122,z1,z2,z3,z142,z5,z8])],[(0,[z1,z2,z3,z326,z4,z5,z8]),(0,[z1,z2,z3,z25,z4,z5,z8]),(0,[z1,z2,z3,z622,z63,z4,z5])],[(0,[z1,z2,z3,z24,z4,z8,z79]),(0,[z1,z2,z3,z623,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z624,z8])],[(0,[z1,z2,z32,z3,z20,z4,z8]),(0,[z1,z2,z3,z157,z4,z208,z8])],[(0,[z1,z2,z3,z625,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z264,z8]),(0,[z1,z2,z3,z20,z4,z626,z8])],[(0,[z1,z2,z3,z16,z93,z4,z5]),(0,[z1,z2,z627,z3,z4,z5,z8])],[(0,[z143,z1,z2,z3,z20,z4,z8])],[(0,[z68,z1,z2,z3,z93,z5,z8]),(0,[z1,z3,z167,z4,z35,z5,z8]),(0,[z1,z2,z3,z4,z98,z5,z8])]],
   [[(0,[z628,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z629,z5,z8]),(0,[z1,z2,z159,z3,z25,z5,z8])],[(0,[z1,z2,z3,z4,z60,z85,z8]),(0,[z1,z2,z630,z3,z4,z5,z8])],[(0,[z113,z1,z2,z3,z118,z5,z8]),(0,[z1,z2,z631,z3,z4,z5,z8]),(0,[z1,z2,z3,z63,z4,z84,z5]),(0,[z1,z33,z2,z3,z4,z71,z8]),(0,[z1,z128,z2,z3,z16,z4,z5])],[(1,[z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z159,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z5,z8,z632])],[(0,[z1,z2,z633,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z78,z5,z10]),(0,[z1,z2,z3,z402,z4,z5,z8]),(0,[z1,z2,z3,z598,z20,z4,z8]),(0,[z1,z2,z3,z63,z4,z78,z5])],[(0,[z634,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z458]),(0,[z1,z2,z635,z3,z4,z5,z8]),(0,[z1,z90,z3,z4,z35,z5,z8]),(0,[z1,z2,z3,z4,z18,z85,z8])],[(0,[z636,z1,z2,z3,z4,z5,z8]),(0,[z637,z1,z2,z3,z4,z5,z8]),(0,[z1,z90,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z63,z4,z18,z5])],[(0,[z638,z1,z2,z3,z4,z5,z8]),(0,[z126,z191,z2,z3,z4,z5,z8]),(0,[z191,z1,z2,z3,z4,z84,z8]),(1,[z1,z2,z3,z4,z497,z5]),(0,[z1,z2,z3,z24,z4,z8,z26]),(0,[z1,z2,z3,z5,z8,z285,z26])],[(1,[z1,z2,z3,z4,z5,z508]),(0,[z1,z2,z3,z622,z20,z4,z8])],[(0,[z1,z2,z3,z4,z118,z5,z8]),(0,[z68,z1,z2,z3,z24,z4,z8]),(0,[z639,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z563,z4,z35,z5]),(0,[z1,z2,z530,z3,z16,z4,z5])],[(0,[z1,z2,z3,z4,z5,z640,z8]),(0,[z1,z28,z2,z156,z4,z5,z8])],[(0,[z113,z1,z32,z3,z4,z5,z8]),(1,[z1,z2,z3,z467,z4,z5]),(0,[z1,z2,z3,z4,z5,z417,z8])],[(0,[z1,z2,z3,z641,z4,z5,z8]),(0,[z642,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z8]),(0,[z1,z2,z3,z4,z125,z5,z8])],[],[(1,[z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z481,z4,z5,z8])],[(0,[z1,z2,z3,z4,z135,z5,z8]),(0,[z1,z2,z3,z4,z5,z102,z8]),(0,[z1,z2,z3,z4,z78,z5,z8])]],
   [[(1,[z1,z2,z324,z3,z4,z5]),(0,[z122,z1,z2,z3,z16,z4,z5]),(0,[z1,z33,z2,z3,z4,z5,z8])],[(0,[z1,z201,z3,z19,z4,z5,z8])],[],[(0,[z1,z2,z3,z24,z20,z5,z8]),(0,[z1,z2,z3,z24,z16,z4,z5]),(0,[z1,z2,z3,z24,z5,z218,z8]),(0,[z1,z2,z3,z16,z4,z134,z5])],[(0,[z544,z1,z2,z3,z16,z4,z5])],[(0,[z1,z2,z3,z24,z16,z5,z8])],[(0,[z1,z2,z3,z4,z84,z5,z51]),(0,[z0,z1,z2,z3,z24,z4,z8]),(1,[z1,z2,z3,z4,z464,z8]),(0,[z1,z2,z3,z4,z5,z8,z316]),(0,[z1,z2,z3,z643,z4,z5,z8]),(1,[z1,z2,z3,z16,z63,z5]),(0,[z1,z2,z3,z4,z5,z8,z644])],[(0,[z1,z2,z3,z4,z114,z5,z8]),(0,[z1,z2,z645,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z47,z5,z8]),(0,[z1,z2,z3,z4,z646,z5,z8]),(0,[z1,z2,z3,z4,z647,z5,z8]),(0,[z1,z2,z132,z3,z4,z5,z10]),(0,[z1,z2,z3,z63,z4,z77,z5])],[],[(0,[z68,z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z580,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z399]),(0,[z75,z1,z2,z121,z4,z5,z8]),(0,[z1,z2,z3,z34,z93,z5,z8]),(0,[z1,z128,z2,z3,z98,z5,z8]),(0,[z1,z2,z3,z4,z648,z5,z8])],[(0,[z126,z2,z3,z4,z84,z5,z8]),(0,[z0,z1,z2,z132,z3,z4,z5]),(0,[z1,z28,z156,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z510]),(0,[z1,z2,z3,z4,z649,z5,z8])],[(0,[z1,z2,z650,z3,z4,z5,z8]),(0,[z1,z2,z81,z3,z24,z4,z8]),(0,[z1,z2,z3,z4,z134,z5,z26])],[(0,[z1,z2,z3,z213,z4,z208,z5]),(1,[z1,z2,z3,z4,z5,z69]),(0,[z1,z2,z3,z4,z5,z308,z131]),(0,[z1,z2,z3,z4,z5,z71,z8]),(0,[z1,z128,z2,z3,z4,z18,z8]),(0,[z1,z2,z3,z63,z4,z5,z308]),(0,[z1,z2,z3,z24,z4,z109,z8])]],
   [[(0,[z145,z1,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z16,z4,z5,z6]),(0,[z1,z2,z3,z63,z167,z4,z5])],[(0,[z1,z2,z3,z4,z5,z51,z319]),(0,[z1,z2,z3,z63,z4,z94,z5]),(0,[z1,z2,z159,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z651,z8]),(0,[z1,z2,z3,z20,z4,z8,z26]),(1,[z1,z2,z3,z4,z5,z166])],[(0,[z191,z1,z2,z3,z4,z5,z171]),(0,[z1,z2,z3,z65,z4,z35,z5]),(0,[z1,z2,z3,z4,z5,z10,z652]),(1,[z1,z2,z3,z16,z20,z4])],[(1,[z68,z1,z2,z3,z24,z8]),(0,[z1,z2,z132,z3,z4,z5,z8])],[(0,[z1,z2,z3,z653,z4,z5,z8]),(0,[z1,z2,z3,z93,z94,z5,z8]),(0,[z1,z2,z3,z654,z4,z5,z8]),(0,[z1,z90,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z212,z51]),(1,[z1,z2,z3,z63,z4,z5])],[(0,[z1,z2,z156,z3,z16,z4,z5]),(0,[z1,z2,z3,z16,z4,z5,z10]),(0,[z1,z2,z37,z3,z433,z5,z8]),(0,[z1,z2,z3,z103,z24,z4,z8]),(1,[z1,z2,z3,z24,z16,z8]),(0,[z1,z2,z3,z4,z5,z8,z655])],[(0,[z1,z2,z3,z4,z5,z656,z8]),(0,[z1,z2,z3,z622,z4,z5,z8])],[(0,[z0,z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z657,z5,z8]),(0,[z1,z2,z73,z3,z24,z4,z8]),(0,[z1,z2,z159,z3,z125,z5,z8])],[(0,[z145,z1,z2,z3,z4,z47,z8]),(0,[z1,z2,z3,z4,z5,z8,z658]),(0,[z1,z2,z3,z4,z659,z5,z8]),(1,[z1,z2,z73,z94,z5,z8]),(0,[z1,z2,z3,z467,z63,z4,z5])],[(0,[z1,z2,z3,z167,z4,z5,z8])],[(0,[z1,z2,z232,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z577]),(0,[z1,z162,z3,z167,z4,z5,z8])],[(0,[z1,z201,z2,z3,z4,z5,z468]),(0,[z660,z1,z2,z3,z4,z5,z8])],[(0,[z1,z661,z2,z3,z4,z5,z8]),(0,[z1,z2,z662,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z84,z8]),(0,[z55,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z5,z8]),(1,[z143,z1,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z8,z652]),(0,[z1,z2,z663,z3,z4,z5,z8])],[(0,[z141,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z24,z4,z78,z8]),(0,[z1,z2,z3,z276,z16,z4,z5])],[(0,[z1,z664,z2,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z10,z8,z51])]],
   [[(0,[z1,z2,z3,z24,z4,z18,z8]),(0,[z1,z2,z3,z4,z665,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z666])],[(0,[z667,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z668,z5,z8]),(0,[z1,z2,z3,z4,z669,z5,z8]),(0,[z670,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z119,z4,z5])],[(0,[z113,z1,z2,z197,z4,z5,z8]),(1,[z1,z2,z3,z20,z4,z8]),(1,[z1,z2,z3,z4,z5,z200])],[(0,[z1,z2,z3,z24,z4,z8,z131])],[(1,[z1,z28,z156,z4,z5,z8]),(0,[z1,z2,z3,z16,z4,z5,z218])],[(0,[z1,z2,z3,z34,z4,z5,z51]),(0,[z1,z2,z3,z487,z4,z94,z8])],[(0,[z1,z2,z177,z3,z4,z5,z8]),(0,[z1,z671,z2,z3,z4,z5,z8])],[(1,[z1,z96,z3,z4,z5,z51]),(0,[z1,z2,z73,z3,z4,z5,z51]),(0,[z1,z672,z2,z3,z4,z5,z8]),(0,[z1,z2,z673,z3,z4,z5,z8])],[(0,[z141,z1,z2,z3,z4,z5,z8]),(0,[z122,z1,z2,z3,z135,z5,z8]),(0,[z1,z2,z3,z4,z5,z10,z8]),(0,[z1,z2,z3,z4,z5,z10,z26]),(0,[z1,z2,z132,z3,z63,z4,z5]),(1,[z1,z2,z3,z24,z20,z8]),(0,[z1,z2,z3,z20,z4,z109,z8])],[(0,[z1,z2,z3,z121,z24,z4,z8]),(0,[z122,z1,z2,z19,z4,z5,z8]),(0,[z1,z2,z3,z4,z77,z5,z51]),(0,[z1,z2,z3,z4,z5,z674,z8])],[(0,[z1,z2,z3,z63,z4,z5,z71]),(0,[z1,z2,z37,z4,z50,z5,z8]),(0,[z675,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z199,z8]),(1,[z1,z2,z132,z4,z5,z79])],[],[(1,[z0,z2,z3,z4,z5,z131]),(0,[z1,z2,z3,z4,z5,z8,z508]),(0,[z1,z2,z3,z16,z34,z4,z5]),(0,[z500,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z179,z5])],[(0,[z122,z272,z2,z3,z4,z5,z8]),(0,[z1,z2,z676,z3,z4,z5,z8]),(0,[z143,z1,z2,z3,z16,z4,z5])]],
   [[(0,[z1,z2,z3,z677,z4,z5,z8]),(0,[z1,z2,z3,z4,z257,z5,z51]),(0,[z1,z2,z3,z16,z34,z5,z8])],[(0,[z68,z1,z2,z3,z4,z5,z274]),(0,[z1,z2,z100,z34,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z678,z8]),(0,[z55,z1,z2,z3,z63,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z79]),(0,[z1,z2,z3,z24,z4,z77,z8])],[(0,[z1,z2,z3,z16,z4,z5,z60]),(0,[z1,z2,z3,z19,z4,z5,z10]),(0,[z1,z162,z2,z3,z4,z338,z8]),(0,[z1,z2,z173,z3,z4,z5,z8])],[(1,[z1,z2,z3,z343,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z8]),(0,[z1,z2,z159,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z679])],[(0,[z1,z2,z3,z16,z4,z35,z5])],[(0,[z1,z2,z3,z4,z5,z501,z8]),(0,[z145,z1,z2,z3,z4,z5,z124]),(1,[z526,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z109,z51]),(0,[z1,z2,z3,z16,z63,z4,z5])],[(0,[z1,z2,z3,z213,z4,z5,z8]),(0,[z680,z1,z2,z3,z4,z5,z8]),(0,[z186,z1,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z77,z5,z109,z8]),(0,[z1,z2,z3,z63,z4,z5,z109])],[(0,[z1,z2,z132,z3,z20,z4,z8]),(0,[z1,z2,z3,z20,z4,z78,z8]),(0,[z1,z2,z3,z16,z63,z5,z8])],[(0,[z681,z1,z2,z3,z4,z5,z8])],[(0,[z1,z28,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z24,z167,z4,z8])],[(0,[z150,z1,z32,z3,z4,z5,z8]),(0,[z1,z2,z3,z121,z4,z5,z51]),(0,[z1,z2,z3,z16,z4,z208,z5]),(0,[z1,z2,z3,z24,z4,z94,z8])],[(0,[z68,z1,z2,z3,z208,z5,z8]),(1,[z1,z2,z3,z24,z167,z8]),(0,[z1,z2,z3,z4,z137,z5,z8]),(0,[z1,z527,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z262,z4,z8]),(0,[z1,z2,z682,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z50,z64,z8])],[(1,[z1,z2,z3,z4,z5,z67]),(0,[z1,z2,z3,z20,z4,z8,z131]),(0,[z1,z2,z3,z19,z4,z5,z8]),(0,[z1,z3,z4,z18,z5,z71,z8])],[(1,[z145,z2,z121,z4,z5,z8]),(0,[z141,z1,z2,z3,z63,z4,z5]),(0,[z1,z2,z3,z4,z683,z5,z8]),(0,[z1,z2,z3,z684,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z26]),(0,[z1,z2,z3,z685,z4,z5,z8]),(0,[z1,z90,z2,z3,z4,z5,z49]),(0,[z1,z2,z3,z4,z5,z686,z8]),(0,[z1,z2,z3,z4,z585,z8,z92])]],
   [[(0,[z1,z2,z3,z196,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z300]),(0,[z1,z2,z3,z65,z4,z5,z8])],[(0,[z55,z1,z2,z159,z3,z4,z5]),(0,[z55,z1,z2,z3,z20,z4,z8]),(0,[z1,z687,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z63,z4,z374,z5])],[(0,[z1,z2,z3,z93,z4,z5,z51]),(0,[z1,z156,z3,z19,z4,z5,z8]),(0,[z1,z2,z3,z4,z78,z5,z26])],[(0,[z141,z1,z2,z3,z24,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z510]),(0,[z1,z2,z3,z688,z4,z5,z8]),(0,[z1,z2,z3,z222,z4,z5,z8])],[(0,[z1,z2,z232,z19,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z89]),(0,[z1,z2,z3,z4,z134,z5,z79])],[(0,[z1,z2,z3,z4,z5,z8,z69]),(0,[z1,z2,z3,z467,z4,z5,z8]),(0,[z1,z2,z3,z16,z20,z4,z8]),(0,[z1,z2,z3,z429,z5,z8,z26])],[(0,[z689,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z20,z610,z4,z8])],[(0,[z1,z2,z159,z3,z4,z5,z79]),(0,[z1,z2,z3,z20,z4,z8,z79]),(0,[z670,z1,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z5,z8,z166])],[],[],[(0,[z1,z201,z2,z3,z24,z4,z8]),(1,[z1,z2,z3,z13,z5,z8]),(0,[z1,z2,z690,z3,z4,z5,z8]),(0,[z1,z2,z3,z63,z4,z5,z85])],[(0,[z691,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z567,z3,z4,z5,z8]),(0,[z1,z2,z3,z20,z4,z77,z8]),(0,[z1,z2,z3,z63,z4,z5,z92]),(0,[z1,z2,z3,z4,z5,z8,z285])],[(0,[z1,z2,z3,z4,z94,z5,z51])],[(0,[z141,z1,z2,z3,z20,z4,z8]),(1,[z1,z2,z3,z4,z53,z8])],[(1,[z1,z2,z3,z4,z5,z348]),(0,[z692,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z693,z3,z4,z5,z8]),(0,[z694,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z63,z485,z4,z5])]],
   [[(0,[z145,z1,z2,z3,z4,z104,z8]),(0,[z1,z2,z695,z3,z4,z5,z8]),(1,[z122,z1,z19,z4,z5,z8])],[(0,[z1,z2,z696,z3,z4,z5,z8])],[(0,[z1,z2,z3,z195,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z626,z8])],[(0,[z0,z1,z2,z3,z4,z134,z5]),(0,[z1,z2,z3,z4,z5,z697,z8])],[(0,[z1,z2,z3,z4,z84,z5,z10]),(0,[z1,z2,z3,z19,z63,z4,z5])],[(0,[z698,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z23,z3,z4,z85,z8]),(0,[z1,z2,z3,z16,z4,z50,z5]),(0,[z1,z2,z3,z677,z20,z4,z8]),(0,[z1,z2,z3,z684,z63,z4,z5]),(0,[z1,z2,z3,z4,z64,z8,z26])],[(0,[z699,z1,z2,z3,z4,z5,z8]),(0,[z145,z1,z2,z3,z4,z5,z202]),(1,[z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z132,z3,z4,z5,z26])],[(0,[z1,z2,z3,z4,z18,z5,z51]),(0,[z1,z2,z630,z3,z16,z4,z5])],[(0,[z1,z2,z3,z34,z208,z5,z8]),(0,[z68,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z700,z8]),(0,[z1,z2,z3,z4,z184,z218,z8])],[(0,[z1,z2,z701,z3,z4,z5,z8]),(0,[z1,z2,z37,z3,z4,z85,z8]),(0,[z1,z2,z3,z4,z78,z8,z26])],[(1,[z1,z2,z3,z4,z501,z8]),(0,[z1,z90,z2,z3,z4,z5,z89])],[(0,[z1,z201,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z702,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z703,z8])],[(0,[z1,z2,z3,z704,z4,z5,z8]),(1,[z141,z1,z2,z3,z24,z8])],[(1,[z1,z2,z3,z270,z4,z5]),(0,[z1,z2,z3,z4,z705,z5,z8])],[],[(0,[z1,z2,z706,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z84,z5,z8]),(0,[z1,z162,z2,z3,z4,z330,z8]),(0,[z1,z2,z3,z4,z5,z10,z79])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z707,z4,z8]),(0,[z1,z2,z3,z708,z4,z5]),(0,[z1,z2,z3,z63,z5,z203]),(0,[z1,z2,z3,z709,z4,z5])],[(0,[z1,z2,z3,z195,z5,z8]),(0,[z1,z2,z3,z4,z5,z710]),(0,[z1,z2,z3,z222,z65,z4]),(0,[z1,z2,z3,z4,z711,z10]),(0,[z1,z2,z3,z20,z4,z712])],[(0,[z1,z2,z3,z4,z5,z713]),(0,[z0,z2,z3,z525,z4,z5]),(0,[z1,z2,z3,z4,z714,z5]),(0,[z1,z2,z3,z16,z4,z256]),(0,[z1,z2,z3,z4,z517,z64]),(0,[z1,z2,z3,z119,z77,z5])],[(0,[z1,z2,z715,z4,z5,z8]),(0,[z1,z2,z3,z63,z4,z104]),(0,[z1,z2,z3,z4,z8,z716]),(0,[z1,z2,z3,z24,z295,z8]),(0,[z717,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z20,z77,z8]),(0,[z1,z2,z165,z598,z4,z8])],[(0,[z1,z2,z3,z4,z718,z8]),(0,[z68,z2,z3,z24,z93,z8]),(0,[z1,z2,z3,z4,z503,z26]),(0,[z1,z2,z3,z4,z5,z719]),(0,[z1,z2,z23,z4,z720,z8])],[(0,[z1,z2,z3,z721,z5,z8]),(0,[z1,z2,z3,z25,z5,z308]),(0,[z1,z2,z3,z5,z722,z92])],[(0,[z1,z2,z723,z4,z5,z8]),(0,[z122,z1,z19,z4,z123,z8]),(0,[z1,z2,z3,z284,z167,z5]),(0,[z1,z553,z3,z4,z5,z51])],[(0,[z1,z194,z3,z4,z5,z124]),(0,[z526,z3,z19,z4,z5,z8]),(0,[z1,z2,z3,z16,z142,z5]),(0,[z1,z2,z3,z4,z5,z129]),(0,[z1,z2,z159,z4,z5,z136]),(0,[z1,z2,z3,z4,z724,z8])],[(0,[z1,z2,z197,z118,z5,z8]),(0,[z1,z2,z3,z4,z725,z8]),(0,[z2,z3,z726,z208,z5,z8]),(0,[z1,z2,z3,z20,z4,z163]),(0,[z1,z2,z3,z63,z438,z5]),(0,[z1,z2,z173,z3,z24,z16])],[(0,[z1,z2,z3,z727,z4,z8]),(0,[z1,z2,z3,z728,z5,z8]),(0,[z1,z2,z3,z4,z729,z8]),(0,[z2,z3,z4,z730,z5,z8])],[(0,[z1,z2,z3,z731,z4,z5]),(0,[z1,z2,z3,z4,z85,z264]),(0,[z1,z2,z4,z5,z308,z732])],[(0,[z1,z2,z3,z265,z63,z5]),(0,[z1,z2,z3,z63,z233,z5]),(0,[z1,z2,z3,z733,z5,z8]),(0,[z1,z2,z3,z119,z94,z5]),(0,[z1,z2,z3,z125,z256,z8])],[(0,[z1,z2,z3,z734,z4,z5]),(0,[z1,z2,z3,z54,z5,z124]),(0,[z571,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z4,z5,z735]),(0,[z1,z2,z3,z24,z522,z8]),(0,[z1,z2,z3,z4,z711,z8]),(0,[z1,z2,z3,z4,z736,z5]),(0,[z1,z2,z3,z4,z43,z64])],[(0,[z1,z600,z2,z3,z24,z8]),(0,[z1,z2,z3,z59,z24,z8]),(0,[z2,z3,z4,z730,z60,z8]),(0,[z1,z2,z3,z24,z4,z10]),(0,[z1,z2,z3,z4,z5,z737])],[(0,[z1,z2,z3,z20,z4,z468]),(0,[z1,z2,z3,z4,z738,z8]),(0,[z1,z2,z3,z4,z5,z739])],[(0,[z55,z2,z3,z523,z4,z5]),(0,[z122,z526,z19,z4,z5,z8]),(0,[z1,z2,z3,z16,z5,z363])]],
   [[(0,[z1,z2,z3,z4,z740,z8]),(0,[z1,z2,z3,z741,z4,z5]),(0,[z1,z2,z3,z304,z35,z8]),(0,[z1,z2,z3,z20,z606,z8])],[(0,[z1,z2,z3,z742,z5,z8]),(0,[z1,z2,z3,z24,z447,z8]),(0,[z1,z2,z3,z4,z184,z10])],[(0,[z1,z2,z3,z4,z743,z8]),(0,[z1,z2,z3,z744,z5,z8]),(0,[z1,z2,z3,z4,z745,z8]),(0,[z1,z2,z3,z24,z746,z8])],[(0,[z1,z2,z185,z63,z4,z5]),(0,[z1,z2,z3,z747,z4,z5]),(0,[z1,z162,z3,z24,z167,z8]),(0,[z1,z2,z3,z276,z20,z4]),(0,[z1,z2,z3,z4,z5,z748])],[(0,[z1,z3,z467,z52,z4,z5]),(0,[z1,z2,z3,z749,z4,z5])],[(0,[z113,z32,z3,z63,z4,z5]),(0,[z1,z2,z3,z4,z750,z8])],[(0,[z75,z2,z232,z16,z4,z5]),(0,[z1,z289,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z5,z751]),(0,[z1,z90,z3,z35,z5,z8]),(0,[z1,z2,z3,z24,z16,z71]),(0,[z1,z2,z3,z20,z77,z166]),(0,[z1,z2,z3,z91,z218,z8])],[(0,[z1,z2,z752,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z753]),(0,[z150,z201,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z754,z10]),(0,[z1,z2,z3,z16,z5,z386]),(0,[z1,z2,z3,z20,z4,z179])],[(0,[z1,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z755,z4,z5]),(0,[z1,z2,z3,z16,z4,z325]),(0,[z1,z33,z3,z63,z4,z71]),(0,[z1,z2,z3,z226,z4,z5]),(0,[z1,z2,z3,z756,z4,z5])],[(0,[z1,z2,z3,z757,z5,z8]),(0,[z1,z2,z3,z758,z343,z8]),(0,[z1,z2,z3,z4,z759,z8]),(0,[z1,z2,z3,z24,z563,z35]),(0,[z1,z2,z3,z24,z16,z167]),(0,[z1,z2,z3,z4,z5,z732])],[(0,[z1,z2,z3,z760,z5,z8]),(0,[z1,z2,z3,z4,z761,z8]),(0,[z1,z2,z3,z24,z541,z8]),(0,[z1,z2,z3,z762,z5,z51]),(0,[z1,z2,z3,z42,z5,z8])],[(0,[z1,z2,z3,z763,z5,z8]),(0,[z1,z2,z3,z4,z764,z8]),(0,[z1,z2,z3,z24,z456,z8]),(0,[z484,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z765,z4,z8]),(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z2,z3,z4,z9,z57]),(0,[z1,z2,z3,z4,z184,z8])],[(0,[z1,z201,z185,z4,z5,z8]),(0,[z1,z2,z767,z3,z4,z5]),(0,[z431,z2,z3,z4,z5,z176]),(0,[z1,z2,z3,z4,z78,z446])],[(0,[z1,z2,z3,z63,z118,z5]),(0,[z1,z177,z3,z16,z4,z5]),(0,[z1,z2,z3,z24,z135,z8]),(0,[z1,z2,z3,z4,z5,z768]),(0,[z1,z2,z73,z226,z94,z5]),(0,[z1,z2,z73,z24,z94,z8]),(0,[z1,z2,z81,z155,z4,z8]),(0,[z1,z248,z3,z276,z4,z5])],[(0,[z113,z769,z3,z4,z5,z8]),(0,[z1,z3,z770,z35,z5,z8]),(0,[z1,z2,z3,z326,z71,z8])]],
   [[(0,[z1,z771,z3,z4,z5,z8]),(0,[z1,z591,z3,z4,z71,z8]),(0,[z1,z2,z3,z746,z4,z8]),(0,[z1,z2,z3,z94,z5,z200])],[(0,[z1,z194,z3,z4,z104,z8]),(0,[z1,z2,z3,z24,z16,z18]),(0,[z1,z2,z159,z4,z5,z308])],[(0,[z150,z201,z3,z4,z5,z8]),(0,[z1,z2,z185,z20,z4,z8]),(0,[z1,z2,z3,z4,z114,z67]),(0,[z1,z2,z3,z772,z5,z8]),(0,[z1,z2,z3,z773,z4,z5]),(0,[z1,z2,z165,z4,z85,z8]),(0,[z1,z2,z3,z24,z16,z109])],[(0,[z1,z2,z3,z63,z4,z47]),(0,[z191,z1,z2,z3,z24,z16]),(0,[z1,z552,z3,z4,z71,z8]),(0,[z1,z2,z3,z4,z5,z774])],[(0,[z113,z32,z3,z20,z4,z8]),(0,[z1,z194,z3,z16,z4,z5]),(0,[z1,z2,z3,z534,z4,z5]),(0,[z1,z2,z3,z192,z98,z8]),(0,[z1,z2,z3,z775,z4,z8])],[(0,[z1,z2,z3,z776,z195,z8]),(0,[z68,z1,z2,z3,z157,z8]),(0,[z1,z2,z3,z24,z550,z8]),(0,[z1,z3,z4,z5,z404,z51]),(0,[z1,z2,z3,z4,z777,z51])],[(0,[z1,z2,z3,z4,z5,z250]),(0,[z1,z177,z3,z4,z47,z8]),(0,[z1,z2,z3,z54,z104,z8]),(0,[z1,z2,z3,z16,z54,z5]),(0,[z1,z2,z3,z4,z5,z778]),(0,[z1,z2,z3,z4,z5,z163]),(0,[z1,z2,z3,z4,z5,z779])],[(0,[z1,z194,z3,z4,z5,z202]),(0,[z1,z2,z3,z780,z5,z8]),(0,[z1,z2,z3,z24,z4,z510]),(0,[z1,z2,z3,z781,z4,z5]),(0,[z1,z2,z3,z326,z5,z508]),(0,[z1,z2,z3,z4,z782,z10]),(0,[z1,z2,z3,z783,z4,z5])],[(0,[z2,z177,z121,z4,z5,z8]),(0,[z1,z784,z3,z16,z4,z5])],[(0,[z1,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z24,z4,z69]),(0,[z1,z2,z3,z24,z116,z8]),(0,[z1,z2,z3,z16,z98,z5])],[(0,[z1,z2,z3,z4,z5,z785]),(0,[z1,z2,z3,z786,z142,z8])],[(0,[z1,z2,z3,z787,z5,z8]),(0,[z1,z2,z3,z788,z5,z8]),(0,[z141,z1,z2,z3,z157,z8]),(0,[z1,z2,z3,z4,z789,z5]),(0,[z1,z2,z3,z24,z4,z166])],[(0,[z1,z2,z3,z54,z5,z202]),(0,[z1,z2,z3,z4,z5,z790]),(0,[z1,z2,z3,z4,z5,z791]),(0,[z1,z2,z3,z34,z184,z8]),(0,[z1,z2,z792,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z793]),(0,[z1,z2,z3,z4,z794,z8]),(0,[z1,z2,z795,z3,z4,z5]),(0,[z1,z2,z3,z326,z5,z8]),(0,[z1,z2,z3,z467,z20,z4])],[(0,[z1,z2,z3,z796,z4,z5]),(0,[z55,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z20,z4,z228]),(0,[z1,z2,z3,z63,z5,z686])],[(0,[z1,z2,z3,z4,z797,z8]),(0,[z1,z2,z3,z13,z134,z8]),(0,[z1,z2,z3,z24,z35,z8]),(0,[z1,z2,z3,z4,z5,z474]),(0,[z1,z108,z3,z119,z4,z5])]],
   [[(0,[z1,z2,z3,z798,z5,z8]),(0,[z1,z248,z3,z4,z5,z10]),(0,[z1,z2,z3,z24,z270,z94]),(0,[z1,z2,z4,z720,z5,z8])],[(0,[z1,z2,z3,z799,z5,z8]),(0,[z1,z2,z3,z800,z5,z8]),(0,[z1,z2,z3,z4,z464,z51]),(0,[z1,z2,z3,z4,z585,z51]),(0,[z1,z2,z3,z16,z284,z5]),(0,[z1,z2,z3,z24,z569,z8]),(0,[z80,z1,z2,z3,z24,z16])],[(0,[z1,z2,z3,z4,z5,z801]),(0,[z1,z2,z324,z3,z20,z4]),(0,[z1,z2,z3,z802,z4,z8])],[(0,[z1,z2,z3,z4,z803,z8]),(0,[z1,z2,z3,z4,z5,z804]),(0,[z1,z2,z3,z4,z805,z8]),(0,[z1,z592,z3,z4,z5,z51]),(0,[z1,z2,z3,z16,z20,z34]),(0,[z1,z2,z3,z24,z4,z293])],[(0,[z1,z2,z3,z4,z5,z806]),(0,[z1,z2,z3,z24,z16,z208]),(0,[z1,z2,z3,z24,z99,z51]),(0,[z1,z2,z3,z4,z517,z10]),(0,[z1,z2,z3,z807,z5,z8])],[(0,[z1,z2,z3,z4,z5,z415]),(0,[z1,z2,z3,z24,z16,z85]),(0,[z1,z2,z808,z24,z4,z8]),(0,[z1,z2,z3,z24,z16,z355]),(0,[z1,z2,z3,z4,z91,z8])],[(0,[z1,z2,z3,z4,z809,z8]),(0,[z1,z2,z3,z810,z4,z8]),(0,[z1,z2,z3,z24,z414,z8]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z511,z2,z3,z4,z60,z8]),(0,[z1,z2,z3,z63,z4,z137]),(0,[z1,z2,z3,z119,z34,z5])],[(0,[z1,z2,z812,z4,z5,z8]),(0,[z251,z32,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z813]),(0,[z1,z2,z3,z4,z814,z5]),(0,[z1,z2,z3,z16,z326,z5]),(0,[z143,z1,z3,z24,z4,z10]),(0,[z1,z2,z3,z24,z16,z417])],[(0,[z150,z201,z3,z63,z4,z5]),(0,[z141,z2,z3,z262,z208,z8]),(0,[z1,z3,z815,z4,z5,z8]),(0,[z1,z2,z3,z816,z5,z8]),(0,[z1,z2,z3,z222,z63,z4]),(0,[z1,z2,z3,z24,z483,z8])],[(0,[z1,z2,z3,z16,z4,z501]),(0,[z141,z68,z2,z3,z24,z8]),(0,[z1,z2,z387,z4,z50,z8])],[(0,[z1,z2,z3,z4,z497,z50]),(0,[z1,z2,z3,z4,z5,z817]),(0,[z1,z2,z3,z818,z4,z5]),(0,[z1,z2,z3,z4,z134,z148])],[(0,[z1,z2,z3,z4,z425,z64])],[(0,[z1,z2,z3,z157,z167,z8]),(0,[z1,z2,z3,z4,z497,z26]),(0,[z1,z2,z3,z819,z4,z8]),(0,[z0,z2,z650,z3,z4,z5]),(0,[z1,z2,z3,z4,z464,z10]),(0,[z143,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z4,z585,z10]),(0,[z1,z2,z3,z24,z582,z8]),(0,[z1,z2,z3,z24,z643,z8])],[(0,[z1,z2,z3,z4,z5,z820]),(0,[z1,z2,z3,z821,z5,z8]),(0,[z1,z2,z3,z822,z4,z5]),(0,[z1,z2,z3,z4,z5,z823]),(0,[z1,z2,z3,z24,z4,z200])],[(0,[z1,z2,z3,z4,z5,z824]),(0,[z1,z2,z3,z825,z4,z8]),(0,[z1,z2,z3,z4,z497,z134]),(0,[z1,z2,z3,z4,z826,z8])],[(0,[z1,z28,z156,z24,z4,z8]),(0,[z1,z3,z4,z5,z768,z51]),(0,[z1,z2,z3,z4,z517,z8])]],
   [[(0,[z1,z2,z185,z4,z5,z8]),(0,[z1,z2,z3,z63,z295,z5]),(0,[z1,z2,z827,z3,z4,z5]),(0,[z1,z2,z3,z828,z5,z8]),(0,[z1,z2,z829,z3,z4,z5]),(0,[z1,z2,z3,z24,z16,z51]),(0,[z1,z2,z269,z3,z24,z16])],[(0,[z1,z2,z3,z195,z5,z67]),(0,[z1,z2,z3,z4,z5,z830]),(0,[z1,z2,z3,z831,z4,z5]),(0,[z1,z90,z3,z35,z5,z49]),(0,[z1,z2,z3,z4,z5,z832])],[(0,[z113,z32,z3,z4,z5,z8]),(0,[z1,z2,z3,z833,z4,z5]),(0,[z1,z96,z3,z24,z4,z51]),(0,[z1,z2,z3,z4,z51,z834]),(0,[z1,z230,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z5,z835]),(0,[z1,z2,z73,z304,z94,z8]),(0,[z1,z2,z3,z4,z5,z836])],[(0,[z1,z2,z837,z3,z4,z5]),(0,[z68,z1,z2,z3,z99,z5]),(0,[z1,z2,z3,z135,z123,z8]),(0,[z1,z2,z3,z838,z4,z8]),(0,[z1,z2,z3,z4,z839,z8]),(0,[z1,z2,z37,z4,z50,z11]),(0,[z1,z2,z159,z25,z5,z308]),(0,[z1,z2,z3,z16,z4,z840])],[(0,[z1,z177,z3,z4,z5,z124]),(0,[z1,z2,z841,z4,z5,z8]),(0,[z1,z526,z19,z4,z5,z8]),(0,[z1,z2,z3,z16,z77,z5])],[(1,[z32,z185,z4,z5,z8]),(0,[z1,z2,z3,z142,z123,z8]),(0,[z1,z2,z3,z842,z4,z8]),(0,[z1,z2,z73,z487,z94,z8])],[(0,[z1,z2,z23,z4,z85,z10]),(0,[z1,z2,z37,z63,z4,z50]),(0,[z1,z2,z132,z24,z4,z79]),(0,[z1,z2,z159,z20,z4,z308]),(0,[z1,z2,z3,z63,z20,z4])],[(0,[z150,z201,z3,z20,z4,z8]),(0,[z1,z2,z3,z16,z657,z5]),(0,[z1,z2,z3,z4,z843,z8]),(0,[z1,z2,z3,z4,z5,z844]),(0,[z1,z2,z3,z429,z20,z8])],[(0,[z0,z2,z3,z24,z4,z131]),(0,[z845,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z846]),(0,[z1,z2,z3,z847,z5,z8]),(0,[z1,z2,z3,z5,z218,z722])],[(0,[z141,z1,z2,z3,z99,z5]),(0,[z272,z2,z3,z4,z123,z8]),(0,[z1,z2,z3,z848,z5,z8]),(0,[z1,z128,z2,z3,z24,z16])],[(0,[z126,z2,z3,z481,z4,z8]),(0,[z1,z2,z633,z4,z85,z8]),(0,[z1,z2,z3,z24,z218,z10]),(0,[z1,z2,z3,z16,z5,z722])],[(0,[z1,z2,z3,z20,z4,z250]),(0,[z1,z2,z3,z4,z464,z458])],[(0,[z1,z2,z3,z4,z5,z228]),(0,[z1,z2,z3,z487,z42,z8])],[(0,[z1,z2,z3,z16,z94,z5]),(0,[z186,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z16,z585,z92])],[(0,[z2,z3,z4,z5,z849,z131]),(0,[z55,z1,z2,z3,z25,z5]),(0,[z850,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z20,z4,z51]),(0,[z1,z364,z3,z4,z5,z10])],[(0,[z1,z2,z851,z3,z4,z5]),(0,[z141,z2,z3,z24,z336,z8]),(0,[z1,z2,z3,z4,z852,z5]),(0,[z1,z531,z3,z4,z5,z10])]],
   [[(0,[z1,z2,z3,z853,z4,z8]),(0,[z1,z2,z3,z16,z441,z5]),(0,[z526,z2,z3,z24,z4,z8]),(0,[z854,z2,z3,z4,z5,z8]),(0,[z1,z28,z156,z4,z5,z51]),(0,[z1,z2,z3,z855,z25,z8])],[(0,[z1,z2,z3,z856,z5,z8]),(0,[z638,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z4,z5,z857]),(0,[z1,z2,z23,z4,z85,z8]),(0,[z1,z2,z3,z858,z4,z5])],[(0,[z1,z2,z3,z4,z859,z8]),(0,[z1,z2,z3,z65,z77,z5]),(0,[z1,z96,z2,z3,z24,z16]),(0,[z1,z2,z3,z8,z285,z235])],[(0,[z1,z2,z3,z4,z5,z860]),(0,[z1,z2,z587,z34,z5,z8]),(0,[z1,z2,z3,z63,z4,z123]),(0,[z1,z2,z3,z63,z487,z4]),(0,[z1,z2,z3,z861,z4,z5]),(0,[z1,z2,z269,z3,z4,z417])],[(1,[z177,z121,z4,z5,z8]),(0,[z862,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z20,z4,z474]),(0,[z1,z33,z2,z3,z24,z16]),(0,[z1,z2,z3,z24,z20,z51]),(0,[z410,z2,z3,z4,z5,z199]),(0,[z1,z2,z3,z4,z5,z316]),(0,[z1,z2,z3,z16,z25,z5]),(0,[z1,z2,z3,z119,z20,z4])],[(0,[z1,z2,z132,z654,z4,z5]),(1,[z2,z3,z4,z5,z849]),(0,[z1,z2,z3,z24,z4,z508]),(0,[z1,z2,z3,z24,z218,z8])],[(0,[z1,z2,z3,z4,z5,z863]),(0,[z1,z2,z3,z13,z85,z8]),(0,[z55,z2,z3,z4,z378,z5]),(0,[z1,z2,z3,z16,z5,z461]),(0,[z1,z2,z3,z864,z4,z8]),(0,[z1,z2,z73,z3,z24,z16])],[(0,[z1,z2,z3,z4,z5,z865])],[(0,[z1,z2,z3,z24,z4,z67])],[(0,[z1,z2,z185,z4,z501,z8]),(0,[z443,z1,z19,z4,z5,z8]),(0,[z145,z2,z121,z24,z4,z8]),(0,[z1,z2,z3,z866,z4,z5])],[(0,[z1,z2,z3,z24,z4,z300]),(0,[z1,z2,z3,z20,z4,z415]),(0,[z1,z2,z3,z867,z4,z5]),(0,[z1,z2,z3,z868,z5,z8]),(0,[z1,z2,z159,z3,z429,z5])],[(0,[z113,z32,z3,z4,z501,z8]),(0,[z1,z90,z3,z63,z35,z5]),(0,[z1,z2,z3,z65,z94,z5]),(0,[z1,z2,z3,z20,z442,z8])],[(0,[z2,z32,z185,z4,z5,z8]),(0,[z1,z2,z869,z3,z4,z5]),(0,[z1,z28,z156,z4,z5,z415]),(0,[z1,z90,z3,z35,z5,z89]),(0,[z1,z2,z3,z24,z16,z64]),(0,[z1,z2,z3,z63,z4,z724]),(0,[z1,z553,z3,z467,z4,z5])],[(0,[z1,z2,z3,z195,z501,z8]),(0,[z1,z870,z3,z4,z5,z8]),(0,[z1,z2,z3,z871,z4,z8]),(0,[z1,z2,z3,z99,z77,z5]),(0,[z1,z2,z3,z5,z51,z872]),(0,[z1,z2,z3,z24,z366,z8])],[(0,[z1,z177,z3,z4,z104,z8]),(0,[z1,z2,z3,z4,z5,z873]),(0,[z1,z2,z3,z24,z4,z89]),(0,[z1,z2,z3,z858,z42,z5]),(0,[z874,z2,z3,z24,z4,z8])],[(0,[z1,z2,z3,z343,z5,z51]),(0,[z141,z2,z3,z16,z208,z5]),(0,[z1,z2,z3,z4,z5,z875]),(1,[z1,z2,z3,z24,z226])]],
   [[(0,[z1,z2,z3,z4,z5,z876]),(0,[z1,z2,z3,z4,z5,z877]),(0,[z1,z2,z3,z4,z5,z878]),(0,[z1,z2,z3,z4,z581,z64])],[(0,[z1,z2,z3,z879,z5,z8]),(0,[z1,z2,z3,z880,z4,z8]),(0,[z1,z2,z3,z534,z262,z4]),(0,[z526,z2,z3,z4,z5,z51]),(0,[z1,z2,z3,z16,z304,z4]),(0,[z1,z2,z3,z881,z4,z5]),(0,[z1,z2,z159,z485,z4,z5]),(0,[z1,z2,z3,z24,z119,z8])],[(0,[z1,z2,z3,z882,z343,z8])],[(0,[z1,z2,z3,z429,z5,z131]),(0,[z1,z2,z3,z883,z4,z5]),(0,[z1,z2,z3,z884,z35,z8]),(0,[z1,z2,z3,z4,z885,z51]),(0,[z1,z2,z132,z4,z5,z652])],[(0,[z1,z177,z3,z4,z5,z202]),(0,[z1,z398,z3,z4,z5,z51]),(0,[z1,z2,z3,z63,z4,z338]),(0,[z1,z2,z3,z4,z51,z235])],[(0,[z1,z2,z3,z4,z754,z8]),(0,[z1,z2,z3,z4,z5,z886]),(0,[z1,z2,z3,z887,z4,z5]),(0,[z1,z2,z3,z276,z4,z5]),(0,[z1,z2,z3,z4,z5,z888])],[(0,[z1,z2,z3,z889,z98,z5]),(0,[z1,z2,z3,z99,z94,z5]),(0,[z1,z2,z3,z4,z5,z890]),(0,[z1,z2,z3,z24,z16,z189]),(0,[z1,z2,z3,z24,z4,z891])],[(0,[z1,z2,z3,z4,z5,z892]),(0,[z1,z2,z893,z4,z5,z8]),(0,[z1,z2,z3,z77,z133,z8]),(0,[z1,z2,z3,z4,z894,z5]),(0,[z1,z2,z3,z24,z167,z51]),(0,[z1,z2,z3,z24,z242,z8]),(0,[z1,z2,z16,z34,z94,z5]),(0,[z1,z2,z3,z895,z5,z8]),(0,[z1,z2,z3,z25,z5,z64])],[(0,[z1,z2,z3,z262,z4,z51]),(0,[z1,z2,z3,z896,z4,z5]),(0,[z1,z2,z3,z20,z4,z458]),(0,[z1,z2,z3,z897,z4,z5]),(0,[z1,z33,z3,z16,z4,z71]),(0,[z1,z2,z3,z24,z42,z8])],[(0,[z1,z2,z3,z24,z4,z348]),(0,[z1,z2,z3,z4,z898,z8]),(0,[z141,z2,z3,z213,z208,z5]),(0,[z191,z2,z3,z4,z497,z60]),(0,[z1,z2,z3,z24,z16,z60]),(0,[z1,z2,z81,z3,z24,z16])],[(0,[z1,z2,z899,z4,z5,z8]),(0,[z145,z2,z121,z4,z5,z51]),(0,[z1,z2,z3,z24,z5,z274]),(0,[z122,z1,z19,z24,z4,z8]),(0,[z1,z90,z3,z20,z35,z8]),(0,[z1,z2,z3,z4,z900,z5])],[(0,[z1,z2,z3,z118,z114,z8]),(0,[z1,z2,z3,z4,z5,z901]),(0,[z1,z2,z3,z902,z4,z8]),(0,[z1,z2,z3,z24,z239,z8])],[],[(0,[z1,z2,z3,z4,z903,z5]),(0,[z1,z2,z3,z4,z5,z904]),(0,[z1,z2,z3,z63,z5,z697])],[(0,[z113,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z4,z905,z8]),(0,[z1,z2,z3,z4,z906,z8]),(0,[z1,z422,z3,z4,z5,z10]),(0,[z1,z2,z229,z3,z24,z16])],[(0,[z1,z2,z3,z907,z5,z8]),(0,[z1,z2,z4,z5,z732,z79]),(0,[z1,z2,z3,z155,z24,z16])]],
   [[(0,[z1,z2,z3,z20,z118,z8]),(0,[z2,z908,z121,z4,z5,z8]),(0,[z1,z2,z3,z4,z909,z8]),(0,[z55,z2,z3,z24,z4,z6])],[(0,[z1,z2,z3,z910,z5,z8]),(0,[z1,z2,z3,z4,z911,z8]),(0,[z1,z2,z3,z4,z912,z8])],[(0,[z1,z2,z3,z563,z4,z5]),(0,[z1,z2,z3,z24,z65,z35]),(0,[z1,z2,z3,z24,z276,z167]),(0,[z1,z2,z3,z4,z913,z8])],[(0,[z1,z2,z3,z762,z5,z8]),(0,[z150,z201,z3,z4,z5,z348]),(0,[z1,z2,z3,z4,z5,z914]),(0,[z1,z2,z3,z915,z109,z8])],[(0,[z1,z2,z3,z916,z5,z8]),(0,[z1,z2,z3,z917,z4,z5]),(0,[z1,z2,z3,z918,z5,z8]),(0,[z1,z2,z3,z429,z78,z8])],[(0,[z1,z2,z3,z20,z4,z274]),(0,[z1,z2,z3,z919,z4,z5]),(0,[z1,z2,z3,z13,z5,z51]),(0,[z1,z2,z3,z4,z782,z8]),(0,[z1,z2,z3,z20,z915,z8])],[],[(0,[z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z920,z4,z8])],[(0,[z1,z2,z3,z16,z34,z5]),(0,[z1,z2,z269,z3,z4,z64]),(0,[z1,z2,z3,z20,z4,z921])],[(0,[z1,z194,z3,z54,z5,z8]),(0,[z1,z2,z3,z4,z53,z51]),(0,[z1,z2,z3,z304,z218,z8]),(0,[z1,z2,z3,z20,z4,z316]),(0,[z1,z2,z3,z922,z5,z183]),(0,[z1,z2,z173,z4,z5,z308]),(0,[z1,z2,z3,z5,z915,z8]),(0,[z1,z2,z3,z923,z4,z5])],[(0,[z1,z2,z3,z924,z4,z8]),(0,[z1,z2,z3,z4,z925,z5]),(0,[z1,z2,z3,z24,z4,z11])],[(0,[z1,z926,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z497,z5]),(0,[z526,z2,z3,z4,z5,z458]),(0,[z122,z1,z19,z4,z5,z51]),(0,[z1,z2,z3,z927,z4,z5])],[(0,[z1,z2,z3,z928,z5,z8])],[(0,[z1,z2,z3,z929,z118,z5]),(0,[z1,z2,z3,z4,z930,z8]),(0,[z1,z2,z3,z4,z931,z5])],[(0,[z1,z2,z3,z4,z5,z932]),(0,[z1,z2,z3,z4,z8,z933]),(0,[z1,z2,z3,z4,z777,z8]),(0,[z1,z2,z3,z934,z5,z10])],[(0,[z1,z2,z3,z5,z51,z285]),(0,[z1,z2,z3,z4,z935,z8])]],
   [[(0,[z1,z2,z185,z4,z5,z67]),(0,[z1,z2,z3,z936,z4,z5]),(0,[z1,z2,z3,z937,z4,z5]),(0,[z1,z2,z3,z938,z4,z8]),(0,[z1,z2,z3,z4,z939,z8]),(0,[z1,z2,z3,z4,z940,z5]),(0,[z1,z2,z3,z24,z63,z20])],[(0,[z201,z769,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z941]),(0,[z1,z2,z3,z295,z133,z8]),(0,[z68,z1,z2,z3,z24,z51]),(0,[z1,z2,z3,z13,z50,z8]),(0,[z1,z2,z100,z3,z24,z16]),(0,[z1,z2,z3,z24,z125,z8])],[(0,[z1,z2,z3,z4,z501,z250]),(0,[z113,z32,z3,z4,z5,z67]),(0,[z1,z2,z3,z24,z558,z8]),(0,[z1,z2,z3,z24,z563,z4]),(0,[z1,z2,z3,z192,z77,z8]),(0,[z1,z2,z3,z4,z5,z264]),(0,[z1,z2,z37,z4,z50,z183]),(0,[z1,z2,z3,z4,z517,z26])],[(0,[z1,z2,z3,z942,z4,z8]),(0,[z396,z2,z3,z4,z5,z131]),(0,[z1,z2,z3,z943,z5,z8])],[(0,[z1,z2,z324,z3,z4,z5]),(0,[z68,z2,z3,z63,z93,z5]),(0,[z55,z2,z3,z4,z5,z240])],[(0,[z1,z2,z3,z4,z501,z51]),(0,[z1,z944,z3,z4,z5,z8]),(0,[z1,z2,z3,z945,z5,z8]),(0,[z1,z2,z3,z946,z4,z5]),(0,[z1,z2,z3,z4,z5,z947]),(0,[z1,z2,z3,z63,z4,z91])],[(0,[z1,z2,z3,z4,z948,z8]),(0,[z191,z2,z3,z63,z4,z60]),(0,[z1,z2,z3,z4,z5,z458]),(0,[z1,z2,z3,z24,z4,z49]),(0,[z1,z2,z3,z65,z34,z5]),(0,[z1,z2,z3,z98,z5,z129]),(0,[z1,z2,z73,z94,z5,z51])],[(0,[z1,z2,z3,z4,z5,z949]),(0,[z1,z2,z3,z950,z4,z5]),(0,[z141,z1,z2,z3,z24,z51]),(0,[z680,z2,z3,z4,z60,z8]),(0,[z1,z2,z3,z951,z5,z8]),(0,[z1,z2,z3,z952,z5,z8]),(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z2,z190,z4,z85,z8])],[(0,[z1,z2,z3,z4,z78,z475]),(0,[z1,z2,z3,z24,z293,z109]),(0,[z1,z2,z3,z16,z5,z92]),(0,[z1,z2,z3,z4,z5,z954])],[(0,[z1,z2,z3,z4,z5,z955]),(0,[z1,z2,z3,z24,z16,z6]),(0,[z1,z2,z3,z956,z4,z8]),(0,[z1,z2,z3,z24,z685,z8]),(0,[z1,z2,z3,z24,z16,z77])],[(0,[z1,z2,z3,z4,z464,z8]),(0,[z1,z2,z3,z63,z4,z330]),(0,[z1,z2,z3,z4,z585,z8])],[(0,[z1,z2,z957,z4,z5,z8]),(0,[z1,z2,z3,z222,z34,z8]),(0,[z143,z1,z3,z4,z5,z768]),(0,[z1,z2,z3,z783,z24,z4])],[(0,[z68,z1,z2,z3,z24,z10]),(0,[z1,z2,z23,z16,z4,z85])],[(0,[z1,z2,z3,z4,z5,z958]),(0,[z1,z2,z3,z20,z4,z577]),(0,[z1,z2,z3,z24,z276,z4]),(0,[z1,z2,z3,z24,z99,z8]),(0,[z1,z2,z3,z4,z5,z959]),(0,[z1,z2,z3,z24,z52,z4])],[(0,[z1,z2,z3,z157,z63,z4]),(0,[z1,z2,z3,z960,z4,z5]),(0,[z1,z2,z3,z25,z5,z51]),(0,[z1,z2,z3,z24,z16,z10]),(0,[z406,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z4,z5,z961])],[(0,[z560,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z4,z5,z962]),(0,[z1,z2,z3,z4,z963,z5]),(0,[z1,z2,z3,z956,z135,z8]),(0,[z1,z815,z19,z4,z5,z8]),(0,[z1,z28,z156,z4,z5,z577]),(0,[z1,z2,z3,z884,z4,z8]),(0,[z1,z3,z119,z167,z4,z5]),(0,[z1,z2,z3,z270,z20,z4])]],
   [[(0,[z1,z2,z964,z3,z4,z8]),(0,[z1,z2,z3,z965,z5,z8]),(0,[z1,z2,z3,z4,z966,z8])],[(0,[z1,z2,z3,z99,z34,z5]),(0,[z1,z2,z73,z94,z5,z10]),(0,[z406,z1,z2,z3,z24,z8])],[(0,[z141,z1,z2,z3,z24,z10]),(0,[z1,z2,z3,z20,z295,z8]),(0,[z1,z2,z3,z4,z967,z8]),(0,[z1,z2,z3,z968,z5,z8]),(0,[z1,z2,z3,z4,z5,z969]),(0,[z1,z2,z3,z4,z970,z10])],[(0,[z1,z2,z3,z4,z5,z274])],[(0,[z1,z2,z3,z295,z5,z971]),(0,[z972,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z973]),(0,[z1,z2,z3,z4,z5,z974]),(0,[z1,z2,z23,z189,z4,z8]),(0,[z1,z2,z3,z16,z606,z5]),(0,[z1,z2,z3,z4,z975,z8])],[(0,[z1,z2,z3,z976,z4,z5]),(0,[z1,z2,z3,z4,z60,z510]),(0,[z1,z2,z3,z24,z649,z8]),(0,[z1,z2,z3,z24,z371,z8]),(0,[z1,z2,z3,z4,z5,z977]),(0,[z1,z90,z3,z119,z4,z5]),(0,[z1,z2,z3,z16,z4,z794])],[(0,[z1,z2,z3,z16,z4,z104]),(0,[z75,z2,z908,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z921]),(0,[z191,z2,z3,z295,z60,z8]),(0,[z1,z2,z3,z4,z978,z8]),(0,[z1,z2,z37,z16,z4,z50]),(0,[z1,z2,z3,z16,z20,z4]),(0,[z1,z2,z3,z24,z16,z16])],[(0,[z1,z2,z3,z4,z47,z51]),(0,[z1,z2,z979,z3,z4,z5]),(0,[z1,z2,z3,z4,z980,z8])],[(0,[z1,z2,z3,z63,z4,z5]),(0,[z1,z3,z4,z5,z768,z8])],[(0,[z1,z2,z3,z5,z8,z981]),(0,[z1,z2,z3,z25,z5,z10]),(0,[z1,z2,z3,z24,z16,z8]),(0,[z1,z2,z3,z16,z20,z92]),(0,[z1,z2,z3,z77,z8,z235])],[(0,[z1,z2,z3,z982,z4,z8]),(0,[z1,z2,z3,z983,z5,z8]),(0,[z1,z2,z159,z4,z5,z732])],[(0,[z1,z2,z984,z4,z5,z8]),(0,[z1,z2,z3,z4,z64,z183]),(0,[z1,z2,z3,z218,z985,z8]),(0,[z1,z2,z3,z16,z429,z5]),(0,[z1,z2,z3,z24,z16,z134])],[(0,[z1,z2,z3,z4,z5,z986]),(0,[z1,z2,z3,z20,z4,z10])],[(0,[z1,z2,z3,z4,z5,z987]),(0,[z1,z2,z3,z988,z4,z5]),(0,[z1,z2,z3,z4,z5,z989]),(0,[z1,z2,z3,z4,z990,z5]),(0,[z1,z2,z3,z24,z36,z8]),(0,[z1,z2,z3,z433,z5,z271]),(0,[z1,z2,z3,z16,z91,z8])],[(0,[z1,z177,z121,z4,z5,z8]),(0,[z145,z2,z908,z4,z5,z8]),(0,[z383,z2,z3,z4,z84,z8]),(0,[z1,z2,z3,z63,z135,z5]),(0,[z1,z28,z156,z4,z5,z10]),(0,[z1,z3,z24,z4,z10,z51]),(0,[z1,z2,z73,z63,z94,z5]),(0,[z1,z2,z3,z24,z16,z218]),(1,[z1,z2,z3,z16,z91])],[(0,[z1,z2,z32,z3,z24,z16]),(0,[z1,z2,z3,z4,z5,z991]),(0,[z1,z2,z3,z992,z4,z5]),(0,[z1,z2,z3,z4,z5,z993]),(0,[z1,z2,z81,z24,z34,z8]),(0,[z1,z2,z3,z63,z5,z218]),(0,[z1,z2,z3,z4,z8,z954])]],
   [[(0,[z1,z2,z3,z994,z5,z8]),(0,[z1,z2,z3,z995,z4,z8]),(0,[z1,z33,z3,z4,z71,z51])],[(0,[z1,z2,z3,z4,z996,z8]),(0,[z1,z2,z3,z4,z997,z8]),(0,[z1,z96,z3,z4,z5,z768]),(0,[z1,z2,z3,z99,z5,z92])],[(0,[z1,z2,z3,z24,z195,z8]),(0,[z1,z2,z998,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z849]),(0,[z511,z2,z3,z4,z5,z131]),(0,[z1,z2,z3,z24,z20,z10])],[(0,[z1,z2,z3,z999,z4,z8]),(0,[z1,z2,z3,z16,z4,z123]),(0,[z1,z2,z3,z222,z94,z8]),(0,[z1,z2,z3,z4,z1000,z10])],[(0,[z1,z2,z3,z24,z4,z124]),(0,[z611,z2,z3,z4,z5,z131]),(0,[z1,z2,z3,z65,z20,z4]),(0,[z1,z2,z3,z4,z53,z316]),(0,[z1,z2,z3,z25,z517,z8])],[(0,[z1,z2,z3,z1001,z4,z8]),(0,[z1,z2,z3,z4,z5,z1002]),(0,[z1,z2,z3,z4,z1003,z8]),(0,[z1,z2,z269,z3,z4,z44])],[(0,[z1,z2,z185,z16,z4,z5]),(0,[z1,z2,z3,z1004,z5,z8]),(0,[z1,z33,z3,z4,z71,z474]),(0,[z1,z2,z3,z24,z16,z94]),(0,[z1,z2,z3,z4,z5,z1005]),(0,[z1,z2,z3,z5,z8,z722])],[(0,[z1,z2,z3,z20,z4,z8]),(0,[z1,z2,z1006,z3,z4,z5]),(0,[z1,z2,z3,z1007,z4,z5]),(0,[z1,z2,z3,z4,z5,z1008]),(0,[z1,z2,z3,z20,z4,z264]),(0,[z1,z2,z3,z4,z5,z200])],[(0,[z113,z32,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z5,z1009]),(0,[z1,z2,z3,z4,z5,z1010]),(0,[z68,z1,z2,z3,z24,z274]),(0,[z1,z2,z3,z24,z112,z8])],[(0,[z1,z2,z3,z24,z130,z8]),(0,[z1,z28,z156,z4,z5,z8]),(0,[z1,z2,z3,z16,z702,z5])],[(0,[z1,z2,z3,z1011,z5,z8]),(0,[z1,z2,z3,z1012,z4,z8]),(0,[z1,z2,z3,z4,z5,z1013]),(0,[z1,z2,z3,z24,z226,z4]),(0,[z186,z2,z3,z336,z4,z8]),(0,[z1,z2,z841,z16,z4,z5])],[(0,[z299,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z4,z5,z577]),(0,[z1,z2,z3,z1014,z4,z5]),(0,[z1,z2,z3,z623,z63,z5])],[(0,[z1,z2,z3,z497,z295,z5]),(0,[z1,z2,z3,z1015,z4,z8]),(0,[z1,z2,z3,z4,z5,z1016]),(0,[z1,z2,z73,z733,z5,z8]),(0,[z1,z2,z3,z20,z4,z1017])],[(0,[z1,z2,z3,z4,z1018,z8]),(0,[z1,z2,z3,z4,z5,z1019]),(0,[z1,z2,z3,z343,z5,z10]),(0,[z1,z2,z159,z125,z5,z308]),(0,[z1,z2,z3,z16,z5,z442])],[(0,[z1,z2,z3,z4,z1000,z8]),(0,[z1,z2,z3,z24,z402,z16])],[(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z2,z3,z1021,z54,z8]),(0,[z526,z2,z3,z4,z5,z10]),(0,[z1,z90,z3,z52,z4,z5]),(0,[z1,z2,z3,z4,z1022,z8]),(0,[z1,z2,z3,z99,z20,z4]),(0,[z1,z2,z3,z24,z63,z34]),(0,[z1,z2,z3,z24,z4,z1023]),(0,[z1,z2,z3,z16,z149,z5])]],
   [[(0,[z1,z2,z3,z1024,z4,z5]),(0,[z1,z2,z3,z4,z1025,z8]),(0,[z1,z2,z3,z4,z5,z1026]),(0,[z1,z2,z3,z4,z1027,z8]),(0,[z1,z2,z645,z94,z5,z8]),(0,[z1,z2,z132,z4,z5,z79]),(0,[z1,z2,z3,z4,z5,z1028]),(0,[z1,z2,z3,z63,z20,z218])],[(0,[z1,z2,z3,z16,z118,z5]),(0,[z1,z2,z3,z13,z63,z5]),(0,[z1,z2,z3,z4,z5,z1029]),(0,[z1,z2,z3,z52,z20,z4])],[(0,[z1,z2,z3,z4,z5,z1030]),(0,[z1,z2,z3,z1031,z4,z5]),(0,[z1,z2,z3,z4,z179,z5]),(0,[z1,z2,z3,z63,z5,z285])],[(0,[z75,z2,z224,z4,z5,z8]),(0,[z211,z2,z3,z4,z5,z240]),(0,[z1,z2,z3,z598,z433,z8])],[(0,[z1,z2,z3,z929,z4,z5]),(0,[z1,z2,z1032,z3,z4,z5]),(0,[z1,z2,z3,z121,z24,z16]),(0,[z68,z1,z2,z3,z1033,z8]),(0,[z1,z2,z3,z16,z4,z338]),(0,[z1,z2,z3,z24,z246,z8]),(0,[z1,z2,z3,z4,z1034,z8]),(0,[z1,z1035,z3,z24,z4,z8]),(0,[z1,z2,z3,z24,z16,z102])],[(0,[z1,z2,z3,z429,z84,z8]),(0,[z1,z2,z3,z4,z78,z325]),(0,[z1,z2,z3,z24,z167,z10]),(0,[z1,z2,z3,z24,z109,z51]),(0,[z1,z2,z3,z125,z5,z51]),(0,[z1,z2,z808,z63,z4,z5])],[(0,[z1,z177,z3,z54,z5,z8]),(0,[z1,z2,z3,z16,z4,z47]),(0,[z1,z2,z3,z262,z4,z10]),(0,[z1,z2,z3,z157,z94,z8]),(0,[z1,z2,z3,z20,z4,z510]),(0,[z126,z2,z3,z4,z84,z51]),(0,[z1,z39,z3,z35,z5,z8]),(0,[z1,z2,z3,z24,z16,z119]),(0,[z1,z2,z3,z63,z4,z1036])],[(0,[z1,z2,z3,z4,z5,z1037]),(0,[z1,z2,z100,z24,z34,z8]),(0,[z1,z2,z3,z34,z5,z200]),(0,[z1,z2,z3,z1038,z433,z5]),(0,[z1,z2,z3,z1039,z5,z8]),(0,[z1,z2,z3,z16,z4,z1040]),(0,[z1,z2,z3,z429,z78,z26])],[(0,[z1,z2,z3,z343,z5,z8]),(0,[z145,z2,z121,z4,z5,z10]),(0,[z1,z2,z3,z1041,z5,z8]),(0,[z1,z2,z3,z20,z4,z69]),(0,[z1,z3,z20,z4,z10,z51]),(0,[z1,z2,z37,z4,z50,z271]),(0,[z1,z2,z3,z4,z517,z79])],[(0,[z1,z90,z3,z65,z35,z5]),(0,[z1,z2,z3,z4,z5,z1042]),(0,[z1,z2,z3,z4,z5,z1043]),(0,[z1,z2,z3,z24,z284,z4]),(0,[z681,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z24,z4,z183]),(0,[z1,z2,z3,z24,z16,z43])],[(0,[z526,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1044,z8]),(0,[z1,z2,z3,z1045,z5,z8]),(0,[z1,z2,z3,z4,z1046,z8]),(0,[z1,z2,z3,z142,z5,z51]),(0,[z1,z3,z4,z588,z5,z51]),(0,[z1,z2,z3,z20,z4,z166])],[(0,[z1,z2,z3,z1047,z4,z5]),(1,[z2,z3,z4,z730,z8]),(0,[z526,z28,z3,z4,z5,z8]),(0,[z1,z2,z580,z4,z5,z652])],[(0,[z1,z2,z3,z4,z885,z8])],[(0,[z1,z2,z3,z4,z1048,z8]),(0,[z1,z2,z3,z63,z4,z184])],[(0,[z2,z769,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z205]),(0,[z1,z2,z3,z4,z1049,z8]),(0,[z1,z110,z3,z35,z5,z8]),(0,[z1,z2,z3,z20,z346,z8]),(0,[z1,z2,z100,z34,z5,z101]),(0,[z1,z2,z3,z4,z5,z1050])],[(0,[z1,z2,z3,z1051,z5,z8]),(0,[z1,z2,z353,z3,z24,z8]),(0,[z1,z28,z156,z63,z4,z5]),(0,[z1,z2,z3,z4,z5,z1052]),(0,[z1,z2,z3,z4,z5,z508]),(0,[z1,z2,z3,z24,z494,z8])]],
   [[(0,[z1,z2,z3,z24,z167,z8]),(0,[z1,z2,z3,z16,z374,z5]),(0,[z1,z2,z3,z63,z4,z1053]),(0,[z1,z2,z3,z63,z4,z235])],[(0,[z1,z2,z3,z1054,z5,z8]),(0,[z1,z2,z3,z4,z5,z1055]),(0,[z1,z2,z3,z1056,z4,z5]),(0,[z596,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z4,z5,z1057]),(0,[z1,z2,z3,z1058,z5,z51]),(0,[z1,z2,z3,z24,z102,z8]),(0,[z1,z2,z3,z24,z315,z8])],[(0,[z1,z1059,z3,z4,z5,z8]),(0,[z526,z2,z3,z4,z464,z8]),(0,[z1,z2,z3,z467,z4,z5]),(0,[z1,z2,z159,z4,z5,z632]),(0,[z1,z2,z1060,z24,z4,z8]),(0,[z1,z2,z3,z20,z4,z293])],[(0,[z145,z2,z121,z4,z5,z8]),(0,[z141,z500,z2,z3,z24,z8]),(0,[z191,z2,z3,z336,z4,z8]),(0,[z1,z2,z3,z13,z5,z10])],[(0,[z1,z2,z3,z24,z4,z202]),(0,[z207,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z24,z884,z8]),(0,[z1,z2,z3,z4,z1061,z51])],[(0,[z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z20,z599,z8])],[(0,[z1,z201,z3,z119,z4,z5]),(0,[z1,z1062,z3,z4,z5,z8]),(0,[z126,z1,z2,z3,z13,z8]),(0,[z1,z2,z3,z4,z134,z397]),(0,[z143,z1,z3,z20,z4,z10]),(0,[z1,z2,z3,z24,z16,z429])],[(0,[z1,z2,z3,z13,z497,z5]),(0,[z1,z2,z3,z4,z53,z10])],[(0,[z141,z2,z3,z157,z208,z8]),(0,[z874,z2,z3,z4,z5,z8]),(0,[z1,z2,z567,z4,z5,z152])],[(0,[z1,z2,z185,z118,z5,z8]),(0,[z613,z2,z3,z4,z60,z8]),(0,[z1,z2,z3,z4,z134,z275]),(0,[z122,z1,z19,z4,z5,z10]),(0,[z1,z2,z3,z16,z4,z137]),(0,[z1,z2,z3,z24,z16,z29])],[(0,[z1,z2,z3,z4,z5,z1017]),(0,[z1,z2,z3,z4,z5,z1063]),(0,[z1,z2,z3,z1064,z4,z5])],[(0,[z113,z32,z3,z118,z5,z8]),(0,[z150,z201,z3,z16,z4,z5]),(0,[z1,z2,z3,z1065,z4,z5]),(0,[z1,z2,z3,z16,z41,z5]),(0,[z1,z2,z3,z1066,z142,z5]),(0,[z1,z2,z3,z24,z4,z56]),(0,[z1,z2,z3,z4,z5,z1067]),(0,[z1,z2,z3,z125,z517,z8]),(0,[z1,z2,z3,z24,z8,z285])],[(0,[z1,z2,z3,z1068,z4,z5]),(0,[z1,z2,z3,z4,z464,z300]),(0,[z1,z2,z3,z934,z5,z8]),(0,[z1,z2,z3,z4,z5,z1069]),(0,[z1,z2,z3,z20,z4,z200])],[(0,[z1,z2,z3,z4,z5,z1070]),(0,[z191,z2,z3,z4,z60,z51]),(0,[z1,z2,z3,z192,z4,z51]),(0,[z1,z2,z3,z4,z137,z101]),(0,[z1,z2,z893,z16,z4,z5]),(0,[z1,z2,z3,z16,z63,z5])],[(0,[z1,z28,z156,z20,z4,z8]),(0,[z1,z2,z3,z304,z226,z4])],[(0,[z1,z2,z3,z4,z104,z51]),(0,[z1,z2,z3,z1071,z4,z5]),(0,[z1,z2,z3,z4,z5,z1072]),(0,[z1,z2,z100,z34,z137,z8]),(0,[z1,z2,z3,z24,z4,z1073]),(0,[z1,z2,z630,z3,z24,z16])]],
   [[(0,[z526,z2,z3,z63,z4,z5]),(0,[z1,z2,z3,z1074,z4,z5]),(0,[z1,z3,z4,z5,z10,z768]),(0,[z1,z2,z3,z4,z1075,z8])],[(0,[z1,z2,z3,z4,z5,z1076]),(0,[z1,z96,z3,z20,z4,z51]),(0,[z1,z2,z3,z24,z705,z8]),(0,[z1,z1077,z3,z24,z4,z8]),(0,[z1,z2,z3,z24,z626,z8])],[(0,[z1,z32,z185,z4,z5,z8]),(0,[z1,z2,z3,z24,z697,z8]),(0,[z1,z2,z3,z4,z53,z8])],[(0,[z1,z2,z3,z4,z5,z348]),(0,[z1,z2,z3,z4,z501,z10]),(0,[z1,z2,z3,z1078,z4,z5]),(0,[z1,z2,z3,z16,z295,z5])],[(0,[z1,z2,z3,z4,z5,z510]),(0,[z1,z2,z3,z63,z4,z464]),(0,[z1,z2,z3,z4,z5,z1079]),(0,[z1,z2,z4,z50,z720,z8]),(1,[z1,z2,z3,z922,z5])],[(0,[z1,z2,z3,z1080,z4,z5]),(0,[z1,z2,z139,z3,z20,z4]),(0,[z1,z2,z3,z63,z262,z4]),(0,[z1,z2,z3,z1081,z4,z5]),(0,[z1,z2,z3,z94,z5,z101]),(0,[z1,z2,z132,z20,z4,z79]),(0,[z1,z2,z1082,z24,z4,z8]),(0,[z1,z2,z3,z24,z355,z8])],[(0,[z75,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z4,z5,z69]),(0,[z1,z2,z3,z4,z5,z1083]),(0,[z1,z548,z3,z4,z5,z51])],[(0,[z698,z32,z3,z4,z5,z8]),(0,[z1,z2,z1084,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1085]),(0,[z68,z1,z2,z3,z24,z16]),(0,[z0,z2,z3,z20,z4,z131]),(0,[z1,z2,z3,z4,z5,z1086]),(0,[z1,z2,z3,z4,z1087,z51])],[(0,[z637,z2,z232,z4,z5,z8]),(0,[z1,z2,z3,z24,z13,z8]),(0,[z1,z2,z701,z94,z5,z8]),(0,[z191,z2,z3,z4,z60,z10]),(0,[z1,z2,z3,z1088,z4,z5]),(0,[z122,z1,z19,z4,z5,z458]),(0,[z1,z2,z3,z4,z1089,z10]),(0,[z1,z2,z3,z4,z5,z1090]),(0,[z1,z2,z3,z4,z5,z166]),(0,[z1,z2,z3,z24,z16,z78])],[(0,[z145,z2,z121,z63,z4,z5]),(0,[z1,z2,z3,z4,z5,z1091])],[(0,[z68,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z4,z1092,z8]),(0,[z1,z33,z3,z402,z4,z8]),(0,[z1,z2,z3,z1093,z4,z5]),(0,[z1,z2,z3,z1094,z4,z5]),(0,[z1,z2,z3,z4,z9,z64]),(0,[z1,z2,z3,z24,z16,z50])],[(0,[z1,z2,z3,z24,z343,z8]),(0,[z0,z1,z2,z3,z4,z517]),(0,[z1,z2,z3,z24,z65,z4]),(0,[z1,z2,z3,z563,z192,z4]),(0,[z1,z2,z3,z4,z5,z1095]),(0,[z1,z2,z3,z1096,z4,z5])],[(0,[z122,z1,z19,z4,z464,z8]),(0,[z691,z1,z3,z4,z5,z10]),(0,[z1,z2,z34,z733,z5,z8]),(0,[z1,z2,z3,z24,z16,z26])],[(0,[z141,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z103,z24,z16]),(0,[z1,z2,z3,z4,z840,z8])],[(0,[z1,z2,z3,z4,z501,z8]),(0,[z145,z2,z324,z121,z4,z5]),(0,[z145,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z4,z187,z51]),(0,[z1,z2,z3,z4,z5,z1097]),(0,[z1,z2,z1098,z3,z4,z5]),(0,[z1,z2,z3,z802,z125,z8]),(0,[z1,z2,z3,z63,z20,z77])],[(0,[z1,z2,z197,z4,z114,z8]),(0,[z1,z2,z3,z4,z1099,z8]),(0,[z1,z3,z4,z5,z1100,z8]),(0,[z526,z2,z3,z20,z4,z8]),(0,[z1,z2,z3,z1101,z4,z8]),(0,[z1,z2,z73,z94,z5,z8]),(0,[z1,z2,z3,z270,z487,z4]),(0,[z1,z2,z3,z1102,z5,z8])]],
   [[(0,[z1,z259,z2,z3,z16,z5]),(0,[z1,z2,z3,z4,z5,z1103]),(0,[z141,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z4,z970,z8]),(0,[z1,z2,z3,z24,z433,z8]),(0,[z1,z2,z3,z4,z517,z183]),(0,[z1,z2,z3,z24,z15,z8]),(0,[z1,z2,z3,z4,z1104,z5])],[(0,[z1,z2,z3,z1105,z5,z8]),(0,[z1,z2,z3,z157,z34,z8]),(0,[z1,z2,z3,z4,z1106,z8]),(0,[z1,z2,z3,z4,z1107,z8]),(0,[z1,z2,z3,z24,z94,z51])],[(0,[z1,z2,z3,z4,z5,z1108]),(0,[z1,z2,z3,z4,z5,z849]),(0,[z1,z2,z567,z4,z5,z79]),(0,[z1,z2,z808,z4,z5,z8])],[(0,[z1,z2,z1109,z4,z5,z8]),(0,[z1,z2,z3,z213,z20,z4]),(0,[z1,z2,z3,z24,z507,z8]),(0,[z1,z2,z3,z798,z325,z8]),(0,[z1,z2,z3,z4,z1110,z8]),(0,[z1,z2,z3,z1111,z5,z8]),(0,[z1,z2,z3,z1112,z5,z8]),(0,[z1,z2,z3,z24,z119,z5])],[(0,[z1,z2,z3,z304,z167,z8]),(0,[z1,z2,z3,z20,z4,z508]),(0,[z143,z1,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z1113,z8])],[(0,[z1,z2,z3,z4,z47,z10]),(0,[z1,z2,z3,z24,z313,z8]),(1,[z1,z815,z4,z5,z8]),(0,[z1,z2,z3,z222,z4,z51]),(0,[z1,z147,z3,z4,z5,z51]),(0,[z1,z2,z3,z5,z1114,z183])],[(0,[z1,z527,z3,z24,z167,z8]),(0,[z1,z2,z3,z99,z63,z5]),(0,[z1,z2,z3,z94,z137,z8]),(0,[z1,z2,z3,z16,z487,z4]),(0,[z1,z2,z554,z4,z5,z79])],[(0,[z1,z2,z3,z20,z4,z67]),(0,[z1,z2,z3,z4,z1115,z8]),(1,[z1,z2,z3,z1116,z8]),(0,[z1,z2,z3,z4,z227,z51]),(0,[z1,z2,z3,z4,z1117,z8]),(0,[z1,z2,z3,z63,z242,z5]),(0,[z1,z2,z3,z24,z276,z10]),(0,[z1,z2,z3,z25,z5,z8]),(0,[z1,z2,z3,z16,z4,z1113])],[(0,[z145,z2,z121,z20,z4,z8]),(0,[z1,z2,z324,z3,z24,z4]),(0,[z1,z2,z3,z4,z127,z64]),(0,[z1,z2,z3,z270,z5,z218]),(0,[z1,z2,z3,z63,z42,z5]),(0,[z1,z2,z3,z20,z4,z1118])],[(0,[z1,z2,z3,z4,z5,z1119]),(0,[z1,z2,z3,z1120,z4,z5]),(0,[z1,z2,z3,z20,z4,z300]),(0,[z1,z90,z3,z192,z35,z8]),(0,[z1,z2,z3,z119,z4,z5]),(0,[z1,z2,z3,z1121,z4,z5]),(0,[z1,z2,z530,z3,z4,z424])],[(1,[z769,z3,z4,z5,z8]),(0,[z122,z1,z19,z63,z4,z5]),(0,[z1,z2,z3,z4,z1122,z5]),(0,[z1,z2,z3,z4,z1123,z5]),(0,[z1,z2,z3,z4,z5,z1124]),(0,[z1,z2,z269,z3,z429,z5])],[(0,[z1,z2,z3,z4,z1125,z8]),(0,[z1,z2,z662,z3,z24,z8]),(0,[z68,z1,z2,z3,z24,z69]),(0,[z1,z2,z3,z4,z1126,z8]),(0,[z1,z2,z3,z1127,z4,z5]),(0,[z1128,z2,z3,z4,z5,z8]),(0,[z1,z162,z3,z167,z5,z10]),(0,[z1,z2,z3,z98,z5,z51]),(0,[z1,z2,z3,z4,z1129,z5]),(0,[z1,z2,z3,z63,z4,z53])],[(0,[z1,z2,z3,z4,z1130,z8]),(0,[z1,z2,z3,z1116,z325,z8]),(0,[z1,z2,z3,z24,z63,z35]),(0,[z1,z2,z3,z284,z5,z298]),(0,[z1,z2,z3,z599,z4,z134])],[(0,[z1,z2,z1131,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1132]),(0,[z1,z2,z795,z3,z13,z5]),(0,[z1,z2,z3,z20,z4,z89]),(0,[z1,z2,z3,z4,z5,z1133])],[(0,[z1,z2,z3,z1134,z4,z5]),(0,[z1,z90,z3,z16,z35,z5]),(0,[z1,z2,z3,z1135,z4,z5]),(0,[z1,z33,z3,z4,z71,z10])],[(0,[z1,z2,z3,z1120,z135,z5]),(0,[z1,z96,z3,z4,z5,z51]),(0,[z1,z2,z3,z24,z4,z271])]],
   [[(0,[z1,z2,z3,z1136,z4,z5]),(0,[z1,z2,z3,z4,z47,z8]),(0,[z1,z2,z3,z4,z8,z1137]),(0,[z272,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z20,z135,z8]),(0,[z1,z2,z3,z4,z5,z1138]),(0,[z1,z2,z3,z4,z5,z49]),(0,[z1,z2,z73,z20,z94,z8]),(0,[z1,z2,z3,z24,z20,z8])],[(0,[z1,z2,z3,z1139,z4,z5]),(0,[z0,z1,z2,z3,z1116,z8]),(0,[z1,z2,z3,z1140,z4,z8]),(0,[z1,z2,z3,z42,z5,z271])],[(0,[z1,z2,z3,z118,z5,z250]),(0,[z1,z2,z3,z4,z227,z10]),(0,[z1,z2,z3,z4,z5,z1141]),(0,[z1,z2,z3,z1142,z5,z8]),(0,[z1,z2,z3,z99,z467,z5]),(0,[z1,z2,z3,z1143,z4,z5]),(0,[z1,z2,z3,z24,z336,z16])],[(0,[z1,z2,z3,z4,z5,z1144]),(0,[z1,z1145,z3,z4,z5,z8]),(0,[z1,z2,z3,z1146,z4,z8]),(0,[z1,z2,z3,z1147,z5,z8]),(0,[z1,z2,z3,z326,z18,z8]),(0,[z1,z2,z3,z304,z63,z4])],[(0,[z1,z2,z3,z1148,z5,z8])],[(0,[z1,z2,z3,z118,z5,z51]),(0,[z1,z2,z3,z4,z1149,z5]),(0,[z1,z2,z3,z24,z4,z171]),(0,[z0,z2,z3,z4,z5,z131]),(0,[z1,z2,z3,z1150,z4,z5])],[(0,[z1,z2,z3,z98,z5,z10]),(0,[z670,z1,z2,z3,z24,z8]),(0,[z95,z1,z3,z52,z4,z5]),(0,[z1,z2,z3,z429,z78,z5])],[(0,[z150,z769,z3,z4,z5,z8]),(0,[z1,z2,z3,z1151,z4,z8]),(0,[z1,z2,z3,z20,z42,z8])],[(0,[z1,z2,z3,z4,z5,z1152]),(0,[z1,z2,z3,z20,z4,z348])],[(0,[z1,z2,z3,z831,z54,z5]),(0,[z145,z2,z121,z343,z5,z8]),(1,[z2,z908,z4,z5,z8]),(0,[z122,z1,z19,z20,z4,z8]),(0,[z1,z2,z392,z94,z5,z8]),(0,[z342,z1,z2,z3,z24,z8])],[(0,[z1,z2,z3,z4,z626,z26])],[(0,[z1,z2,z3,z4,z5,z1153]),(0,[z443,z2,z121,z4,z5,z8]),(0,[z1,z2,z3,z4,z133,z51]),(0,[z1,z2,z3,z135,z5,z51]),(0,[z1,z2,z3,z160,z4,z64])],[(0,[z113,z32,z197,z4,z5,z8]),(0,[z1,z2,z3,z1154,z4,z8]),(0,[z526,z2,z3,z4,z5,z300]),(0,[z1,z2,z3,z4,z5,z1155]),(0,[z1,z2,z3,z4,z5,z1156])],[(0,[z1,z2,z3,z4,z5,z1157]),(0,[z1,z2,z3,z4,z5,z1158]),(0,[z1,z2,z3,z24,z487,z8]),(0,[z1,z2,z3,z63,z218,z235])],[(0,[z1,z2,z197,z195,z5,z8]),(0,[z141,z2,z3,z726,z5,z8]),(0,[z1,z2,z3,z4,z5,z1159])],[(0,[z1,z2,z3,z4,z5,z1160]),(0,[z1,z2,z3,z1161,z4,z8]),(0,[z1,z2,z3,z4,z5,z1162]),(0,[z1,z2,z3,z16,z5,z644]),(0,[z1,z2,z3,z4,z1053,z8])]],
   [[(0,[z1,z2,z3,z118,z5,z10]),(0,[z1,z2,z3,z1163,z4,z5]),(0,[z1,z2,z37,z610,z4,z8]),(0,[z406,z2,z3,z196,z4,z5])],[(0,[z161,z1,z2,z3,z24,z8]),(0,[z272,z2,z3,z4,z5,z51]),(0,[z1,z90,z3,z222,z35,z8]),(0,[z1,z2,z3,z24,z686,z8]),(0,[z1,z2,z3,z63,z125,z5])],[(0,[z1,z2,z3,z1164,z4,z5]),(0,[z1,z2,z3,z4,z8,z1165]),(0,[z1,z2,z3,z1166,z5,z8]),(0,[z1,z2,z3,z4,z5,z1167]),(0,[z1,z2,z3,z16,z5,z285])],[(0,[z75,z2,z232,z24,z4,z8]),(0,[z1,z2,z3,z13,z71,z8]),(0,[z0,z2,z3,z4,z5,z199]),(0,[z1,z2,z3,z52,z4,z5]),(0,[z1,z2,z3,z24,z109,z10]),(0,[z1,z2,z3,z125,z5,z10])],[(0,[z1,z2,z3,z4,z1168,z8]),(0,[z1,z2,z3,z727,z54,z8]),(0,[z1,z2,z3,z262,z4,z8]),(0,[z126,z2,z3,z4,z84,z10]),(0,[z1,z2,z3,z4,z5,z1169]),(0,[z1,z2,z3,z63,z4,z585])],[(0,[z1,z2,z3,z4,z5,z67]),(0,[z1,z2,z3,z4,z187,z274]),(0,[z1,z2,z3,z1170,z4,z8]),(0,[z1,z2,z3,z4,z78,z632])],[(0,[z1,z2,z3,z4,z5,z1171]),(0,[z1,z2,z3,z4,z133,z10]),(0,[z1,z2,z3,z135,z5,z10]),(0,[z1,z2,z3,z24,z488,z8]),(0,[z1,z2,z3,z4,z5,z1118]),(0,[z1,z2,z3,z20,z4,z1172]),(0,[z1,z2,z3,z16,z599,z5])],[(0,[z1,z2,z3,z4,z5,z300]),(0,[z1,z3,z4,z1173,z71,z8]),(0,[z1,z2,z3,z4,z5,z1174])],[(0,[z1,z2,z3,z1175,z4,z5]),(0,[z1,z2,z3,z1176,z4,z8]),(0,[z1,z2,z3,z142,z5,z10]),(0,[z1,z2,z3,z1177,z4,z8]),(0,[z1,z2,z3,z4,z1178,z5])],[(0,[z1,z2,z3,z4,z5,z1179]),(0,[z1,z2,z3,z24,z16,z131]),(0,[z1,z2,z3,z4,z10,z1180]),(0,[z1,z2,z3,z16,z304,z8]),(0,[z1,z2,z3,z20,z4,z11]),(0,[z1,z2,z3,z4,z78,z954])],[(0,[z1,z2,z3,z63,z4,z114]),(0,[z1,z2,z3,z4,z5,z1181]),(0,[z1,z2,z232,z3,z24,z16]),(1,[z1,z2,z3,z24,z274]),(0,[z1,z2,z3,z1182,z4,z5])],[(0,[z75,z177,z3,z4,z5,z8]),(0,[z1,z2,z3,z157,z213,z4]),(0,[z1,z2,z132,z3,z4,z325]),(0,[z1,z2,z3,z786,z4,z8]),(0,[z1,z2,z3,z4,z5,z89])],[(0,[z1,z2,z3,z24,z34,z51]),(0,[z1,z2,z3,z284,z20,z4])],[(0,[z1,z2,z3,z4,z5,z1183]),(0,[z1,z2,z3,z1184,z5,z8]),(0,[z1,z2,z3,z157,z534,z4]),(0,[z1,z2,z3,z1185,z5,z8]),(0,[z1,z2,z3,z4,z330,z163])],[(0,[z1,z2,z3,z1186,z5,z8]),(0,[z1,z2,z3,z1176,z135,z8]),(0,[z1,z2,z3,z125,z5,z8]),(0,[z1,z2,z173,z16,z34,z5]),(0,[z1,z2,z3,z24,z109,z8])],[(0,[z1,z2,z1187,z4,z5,z8]),(0,[z126,z2,z3,z4,z84,z8]),(0,[z561,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z24,z99,z5])]],
   [[(0,[z1,z2,z3,z1188,z4,z8]),(0,[z1,z2,z3,z167,z330,z8]),(0,[z1,z2,z1189,z24,z4,z8])],[(0,[z1,z2,z3,z950,z195,z5]),(0,[z1,z194,z3,z24,z4,z8]),(0,[z1,z2,z3,z1190,z4,z5]),(0,[z1,z2,z3,z4,z1191,z5]),(0,[z1,z2,z3,z13,z5,z8]),(0,[z1,z594,z3,z4,z5,z10]),(0,[z1,z2,z3,z1192,z4,z5]),(0,[z1,z2,z3,z24,z589,z8]),(0,[z1,z2,z3,z4,z369,z475]),(0,[z1,z2,z3,z16,z63,z20])],[(0,[z1,z2,z3,z4,z5,z1193]),(0,[z1,z2,z132,z4,z5,z294]),(0,[z1,z2,z3,z24,z16,z79]),(0,[z1,z2,z3,z24,z63,z4])],[(0,[z1,z2,z3,z4,z5,z1194]),(0,[z1,z2,z3,z24,z54,z8]),(0,[z1,z2,z3,z4,z5,z1195]),(0,[z1,z2,z3,z4,z5,z1196]),(0,[z1,z2,z3,z63,z4,z187]),(0,[z126,z2,z3,z4,z730,z8]),(0,[z1,z2,z3,z4,z5,z891]),(0,[z1,z2,z3,z16,z189,z5])],[(0,[z1,z2,z3,z5,z1197,z8]),(0,[z1,z2,z3,z4,z5,z1198]),(1,[z1,z2,z3,z24,z293])],[(0,[z1,z2,z197,z24,z4,z8]),(0,[z1,z2,z3,z63,z649,z5]),(0,[z1,z2,z3,z135,z5,z458]),(0,[z1,z2,z3,z20,z4,z49]),(0,[z1,z3,z4,z1173,z5,z8]),(0,[z1,z2,z3,z4,z5,z1199]),(0,[z1,z108,z2,z3,z24,z16])],[(0,[z122,z1,z19,z4,z5,z300]),(0,[z1,z2,z3,z24,z98,z8]),(0,[z1,z2,z3,z16,z304,z94])],[(0,[z122,z1,z19,z4,z5,z8]),(0,[z1,z2,z3,z142,z5,z458]),(0,[z1,z2,z3,z222,z16,z4]),(0,[z1,z2,z3,z1182,z42,z5])],[(0,[z1,z2,z3,z1200,z5,z8]),(0,[z1,z2,z3,z99,z35,z5]),(0,[z1,z2,z3,z4,z1201,z5]),(0,[z1,z2,z3,z4,z5,z1202]),(0,[z1,z2,z3,z1203,z4,z5]),(0,[z1,z2,z3,z16,z5,z1028]),(0,[z1,z2,z3,z16,z4,z91])],[(0,[z1,z2,z3,z1204,z4,z5]),(0,[z141,z2,z3,z208,z5,z51]),(0,[z191,z2,z3,z16,z4,z60]),(0,[z1,z2,z3,z135,z464,z8]),(0,[z1,z2,z3,z1205,z4,z8])],[(0,[z1,z2,z1206,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1207]),(0,[z1,z2,z3,z1058,z5,z8]),(0,[z1,z2,z100,z733,z5,z8])],[(0,[z272,z2,z3,z4,z5,z458]),(0,[z1,z2,z3,z142,z464,z8]),(0,[z1,z2,z3,z192,z4,z10]),(0,[z1,z584,z3,z4,z5,z10]),(0,[z1,z2,z3,z24,z16,z5])],[(0,[z1,z2,z3,z1208,z4,z5])],[(0,[z1,z2,z3,z4,z104,z10]),(0,[z1,z2,z3,z4,z1209,z5]),(0,[z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z16,z4,z330]),(0,[z1,z2,z3,z5,z8,z1210]),(0,[z1,z2,z3,z24,z703,z8])],[(0,[z1,z2,z3,z1211,z118,z5]),(0,[z1,z2,z3,z195,z114,z8]),(0,[z1,z2,z3,z4,z501,z67]),(0,[z1,z2,z1212,z3,z4,z5]),(0,[z1,z1035,z3,z4,z5,z8]),(0,[z191,z2,z3,z4,z205,z60]),(0,[z1,z3,z4,z5,z10,z51]),(0,[z1,z2,z37,z3,z24,z16]),(0,[z1,z2,z159,z4,z256,z308])],[(0,[z1,z2,z3,z4,z325,z51]),(0,[z272,z2,z3,z4,z464,z8]),(0,[z1,z2,z24,z34,z94,z8]),(0,[z1,z2,z3,z16,z91,z5])]],
   [[],[(0,[z1,z2,z3,z4,z8,z834])],[(0,[z1,z2,z3,z63,z195,z5]),(0,[z1,z194,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z133,z274]),(0,[z1,z2,z3,z4,z5,z1213]),(0,[z1,z2,z601,z4,z85,z8]),(0,[z1,z2,z3,z13,z20,z8]),(0,[z1,z162,z2,z3,z24,z16]),(0,[z1,z3,z119,z4,z5,z10]),(0,[z1,z2,z3,z77,z915,z8])],[(0,[z1,z2,z197,z4,z5,z250]),(0,[z1,z2,z3,z4,z5,z1214]),(0,[z526,z2,z156,z4,z5,z8]),(0,[z1,z2,z1215,z3,z4,z5])],[(0,[z1,z2,z3,z4,z1216,z5]),(0,[z1,z2,z3,z16,z4,z464]),(0,[z1,z2,z3,z4,z5,z1172]),(0,[z1,z2,z3,z4,z338,z163]),(0,[z1,z2,z3,z24,z326,z8]),(0,[z1,z2,z3,z270,z4,z5])],[(0,[z1,z2,z3,z4,z1217,z5]),(0,[z1,z2,z3,z4,z5,z1218]),(1,[z1,z2,z3,z16,z304]),(0,[z1,z2,z37,z433,z50,z8])],[(0,[z1,z2,z197,z4,z5,z51]),(0,[z1,z2,z3,z4,z1089,z8]),(0,[z1,z2,z3,z343,z47,z8]),(0,[z1,z2,z3,z4,z1219,z8]),(0,[z191,z2,z3,z4,z60,z8]),(0,[z1,z2,z3,z24,z265,z8]),(0,[z1,z2,z3,z192,z4,z8]),(0,[z1,z162,z3,z16,z167,z5]),(0,[z1,z2,z3,z4,z1220,z10]),(0,[z1,z3,z4,z547,z5,z10]),(0,[z1,z2,z3,z4,z5,z1221]),(0,[z1,z2,z3,z1222,z25,z8]),(0,[z544,z1,z2,z3,z24,z16])],[(0,[z1,z2,z3,z54,z5,z51]),(0,[z1,z2,z3,z4,z60,z183]),(0,[z1,z3,z4,z5,z10,z656]),(0,[z1,z2,z3,z4,z338,z51]),(0,[z1,z2,z3,z4,z5,z1223]),(0,[z1,z2,z3,z4,z1224,z8]),(0,[z1,z2,z132,z3,z24,z16]),(0,[z1,z2,z3,z855,z4,z8]),(0,[z1,z2,z1225,z24,z4,z8])],[(0,[z1,z2,z3,z4,z1226,z8]),(0,[z1,z2,z3,z4,z5,z1227]),(0,[z1,z2,z3,z4,z104,z8]),(0,[z500,z2,z3,z4,z84,z8]),(0,[z1,z2,z3,z24,z175,z8]),(0,[z1,z2,z3,z63,z112,z5])],[(0,[z544,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z1228,z5,z8]),(0,[z1,z2,z3,z1229,z5,z8]),(0,[z1,z2,z3,z1230,z4,z5]),(0,[z154,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z24,z160,z8]),(0,[z1,z2,z1231,z3,z20,z4])],[(0,[z1,z3,z276,z119,z4,z5]),(0,[z1,z2,z73,z270,z94,z5]),(0,[z1,z2,z3,z25,z5,z26])],[(0,[z1,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z24,z133,z8]),(0,[z395,z1,z2,z3,z24,z8]),(0,[z1,z2,z3,z4,z1232,z5])],[(0,[z1,z341,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z187,z10]),(0,[z1,z2,z3,z4,z1233,z8]),(0,[z1,z2,z81,z4,z50,z8])],[(0,[z1,z2,z3,z999,z195,z8]),(0,[z1,z3,z4,z5,z624,z10]),(0,[z1,z2,z3,z24,z449,z8])],[(0,[z1,z2,z3,z4,z5,z202]),(0,[z1,z2,z3,z1234,z4,z5]),(0,[z1,z3,z4,z5,z51,z236]),(0,[z1,z2,z3,z16,z20,z77]),(0,[z1,z2,z530,z3,z429,z8])],[(0,[z1,z2,z3,z1235,z5,z8]),(0,[z1,z2,z3,z24,z94,z10]),(0,[z1,z2,z440,z610,z4,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z1236]),(0,[z1,z2,z3,z4,z1237,z5]),(0,[z1,z2,z3,z4,z205,z5])],[(0,[z1,z2,z3,z20,z195,z8]),(0,[z1,z2,z3,z1238,z5,z8]),(0,[z145,z2,z121,z4,z47,z8]),(0,[z1,z2,z3,z4,z5,z1239]),(0,[z126,z2,z3,z63,z4,z84]),(0,[z1,z2,z3,z16,z135,z5]),(0,[z1,z2,z3,z24,z302,z8]),(0,[z1,z2,z3,z4,z1220,z8]),(0,[z1,z2,z3,z24,z164,z8]),(0,[z1,z2,z73,z16,z94,z5]),(0,[z1,z2,z3,z226,z77,z5])],[(0,[z1,z2,z3,z1240,z5,z8]),(0,[z1,z2,z3,z4,z1241,z8]),(0,[z1,z2,z3,z63,z4,z227]),(0,[z1,z2,z3,z4,z5,z1242]),(0,[z1,z2,z3,z24,z276,z16])],[(0,[z1,z2,z3,z20,z4,z124]),(0,[z1,z2,z3,z4,z5,z1243]),(0,[z1,z2,z3,z222,z4,z10]),(0,[z1,z2,z3,z4,z330,z228]),(0,[z1,z2,z3,z1244,z94,z5]),(0,[z1,z2,z3,z24,z4,z1245]),(0,[z1,z2,z3,z4,z78,z29])],[(0,[z1,z769,z3,z4,z5,z8]),(0,[z177,z3,z121,z4,z5,z8]),(0,[z1,z2,z3,z4,z1246,z5]),(0,[z1,z111,z3,z4,z5,z10]),(0,[z2,z3,z4,z5,z6,z849]),(0,[z1,z2,z3,z24,z657,z8]),(0,[z1,z2,z3,z4,z5,z1247])],[(0,[z1,z2,z1248,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1249]),(0,[z1,z2,z3,z213,z4,z5]),(0,[z191,z2,z3,z4,z60,z510]),(0,[z1,z2,z3,z24,z276,z8]),(0,[z1,z2,z3,z4,z5,z56]),(0,[z1,z2,z3,z24,z4,z101])],[(0,[z1,z2,z3,z20,z515,z8]),(0,[z1,z2,z3,z16,z270,z5]),(0,[z1,z2,z37,z42,z50,z8])],[(0,[z1,z2,z3,z1250,z118,z8]),(0,[z1,z2,z3,z4,z5,z1251]),(0,[z1,z2,z3,z4,z187,z8]),(0,[z1,z2,z3,z24,z142,z8]),(0,[z1252,z2,z3,z4,z5,z8]),(0,[z1,z2,z100,z63,z34,z5])],[(0,[z1,z2,z3,z1253,z4,z5]),(0,[z1,z2,z3,z4,z10,z235]),(0,[z1,z2,z3,z4,z5,z1254])],[(0,[z1,z2,z3,z65,z4,z5]),(0,[z1,z2,z3,z63,z4,z517]),(1,[z1,z2,z3,z24,z16])],[(0,[z1,z2,z3,z4,z5,z1255]),(0,[z1,z194,z3,z4,z5,z830]),(0,[z1,z2,z1256,z3,z4,z5]),(0,[z406,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z24,z63,z167]),(0,[z1,z2,z3,z4,z1173,z8]),(0,[z1,z138,z3,z4,z5,z10])],[(0,[z1,z2,z3,z1257,z4,z5]),(0,[z1,z1077,z3,z4,z5,z8]),(0,[z1,z2,z3,z157,z4,z51]),(0,[z1,z2,z3,z4,z5,z1258]),(0,[z1,z2,z3,z4,z1259,z5])],[(0,[z1,z2,z3,z1260,z4,z5]),(0,[z1,z2,z1261,z3,z4,z5]),(0,[z1,z661,z3,z35,z5,z8]),(0,[z1,z33,z3,z4,z71,z8]),(0,[z1,z2,z3,z5,z8,z872]),(0,[z1,z2,z3,z4,z1262,z51])],[(0,[z1,z2,z3,z4,z1263,z8]),(0,[z122,z1,z815,z4,z5,z8])],[(0,[z1,z2,z3,z222,z4,z8]),(0,[z1,z2,z3,z1264,z4,z5]),(0,[z1,z2,z3,z98,z5,z508]),(0,[z1,z2,z3,z1265,z4,z5]),(0,[z1,z2,z3,z5,z218,z166])],[(0,[z1,z2,z3,z4,z1266,z8]),(0,[z1,z2,z1082,z4,z5,z8]),(0,[z1,z2,z3,z4,z137,z316]),(0,[z1,z2,z3,z4,z5,z1267])]],
   [[(0,[z1,z2,z3,z4,z227,z8]),(0,[z1,z2,z3,z295,z5,z1268]),(0,[z1,z2,z3,z16,z5,z166])],[(0,[z1,z2,z3,z4,z5,z1269]),(0,[z1,z2,z3,z4,z5,z1270]),(0,[z1,z2,z3,z4,z5,z1271]),(0,[z1,z2,z3,z24,z25,z8])],[(0,[z1,z1272,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1273]),(0,[z1,z2,z3,z4,z339,z26]),(0,[z55,z2,z3,z20,z4,z6]),(0,[z1,z2,z3,z16,z346,z5]),(0,[z1,z2,z3,z746,z94,z8]),(0,[z1,z2,z3,z24,z293,z8])],[(0,[z1,z2,z3,z4,z5,z1274]),(0,[z1,z2,z908,z4,z5,z8]),(0,[z1,z1275,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z63,z109])],[(0,[z1,z2,z3,z343,z5,z124]),(0,[z1,z2,z3,z4,z5,z1276]),(0,[z1,z2,z3,z4,z1277,z5]),(0,[z1,z2,z3,z24,z4,z497]),(0,[z1,z2,z3,z99,z4,z5]),(0,[z1,z2,z3,z98,z5,z8]),(0,[z1,z2,z3,z63,z192,z4])],[(0,[z1,z2,z3,z1047,z195,z5]),(0,[z0,z2,z3,z4,z521,z5]),(0,[z1,z2,z3,z4,z5,z1278]),(0,[z1,z2,z3,z297,z20,z8])],[(0,[z150,z1,z2,z3,z24,z16]),(0,[z1,z2,z289,z3,z24,z8]),(0,[z1,z2,z3,z534,z94,z5]),(0,[z1,z2,z3,z24,z467,z167]),(0,[z1,z2,z3,z4,z257,z62]),(0,[z1,z2,z100,z20,z34,z8]),(0,[z1,z2,z24,z189,z34,z8]),(0,[z1,z2,z3,z4,z78,z679]),(0,[z1,z2,z3,z4,z521,z26]),(0,[z1,z2,z3,z4,z78,z26])],[(0,[z1,z2,z3,z4,z5,z1279]),(0,[z1,z2,z533,z3,z24,z8]),(0,[z1,z2,z1280,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1281]),(0,[z1,z2,z3,z4,z5,z1282]),(0,[z1,z2,z3,z16,z648,z5])],[(0,[z1,z2,z3,z4,z187,z69]),(0,[z1,z2,z3,z4,z730,z8]),(0,[z1,z2,z100,z34,z5,z51]),(0,[z1,z2,z3,z20,z4,z183]),(0,[z1,z2,z3,z4,z1283,z5])],[(0,[z526,z2,z3,z135,z5,z8]),(0,[z1,z2,z3,z276,z5,z363]),(0,[z1,z2,z3,z4,z5,z1284]),(0,[z1,z2,z229,z189,z4,z8]),(0,[z1,z2,z530,z3,z24,z16])],[(0,[z1,z2,z3,z4,z5,z1285]),(0,[z526,z2,z19,z4,z5,z8]),(0,[z1,z2,z3,z4,z338,z228]),(0,[z1,z2,z3,z4,z10,z1286])],[(0,[z1,z2,z3,z1065,z343,z5]),(0,[z526,z2,z3,z142,z5,z8]),(0,[z1,z2,z3,z24,z579,z8]),(0,[z1,z2,z3,z16,z20,z94])],[(0,[z1,z2,z3,z4,z5,z1287]),(0,[z141,z2,z3,z24,z208,z8]),(0,[z1,z2,z3,z1288,z4,z8]),(0,[z1,z2,z3,z4,z257,z26]),(0,[z1,z2,z530,z3,z24,z8])],[(0,[z2,z232,z908,z4,z5,z8]),(0,[z1,z2,z3,z20,z4,z205]),(0,[z1,z2,z3,z1289,z5,z8])],[(0,[z1,z2,z3,z118,z5,z8]),(0,[z1,z177,z3,z24,z4,z8]),(0,[z1,z2,z3,z1290,z4,z8]),(0,[z1,z2,z3,z4,z1291,z8]),(0,[z1,z2,z3,z433,z85,z8]),(0,[z1,z2,z3,z1292,z4,z8])],[(0,[z1,z2,z3,z4,z1293,z8]),(0,[z145,z2,z121,z4,z5,z124]),(0,[z1,z2,z3,z1294,z4,z5]),(0,[z272,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z16,z643,z5]),(1,[z1,z2,z3,z5,z722])]],
   [[(0,[z1,z177,z232,z4,z5,z8]),(0,[z1,z3,z4,z5,z51,z181]),(0,[z1,z2,z3,z16,z4,z184])],[(0,[z1,z2,z3,z4,z5,z124]),(0,[z1,z2,z3,z35,z330,z8]),(0,[z1,z2,z3,z24,z4,z1295])],[(0,[z1,z2,z3,z4,z134,z325]),(0,[z1,z28,z156,z16,z4,z5]),(0,[z1,z2,z3,z24,z226,z8])],[(0,[z1,z2,z3,z20,z4,z202]),(0,[z1,z2,z3,z4,z84,z510]),(0,[z1,z2,z3,z4,z330,z51]),(0,[z1,z2,z3,z5,z10,z285]),(0,[z1,z2,z3,z4,z5,z1296]),(0,[z1,z2,z3,z20,z125,z8]),(0,[z1,z2,z3,z16,z4,z235])],[(0,[z1,z2,z3,z4,z133,z8]),(0,[z1,z2,z255,z4,z5,z308]),(0,[z1,z2,z3,z135,z5,z8]),(0,[z1,z3,z4,z5,z651,z10])],[(0,[z1,z2,z3,z4,z5,z1297]),(0,[z1,z2,z3,z142,z5,z300]),(0,[z1,z2,z3,z1298,z5,z8]),(0,[z1,z2,z3,z4,z8,z1286]),(0,[z1,z2,z3,z4,z1299,z51]),(0,[z1,z223,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z8,z1300])],[(0,[z1,z2,z3,z758,z4,z8]),(0,[z1,z2,z3,z63,z4,z133]),(0,[z1,z2,z3,z24,z274,z8]),(0,[z1,z2,z3,z142,z5,z8]),(0,[z717,z2,z3,z24,z4,z8]),(0,[z1,z2,z3,z24,z4,z1301])],[(0,[z1,z2,z3,z4,z5,z1302]),(0,[z1,z2,z3,z4,z8,z1180]),(0,[z1,z2,z3,z4,z137,z51])],[(0,[z141,z2,z3,z534,z208,z5]),(0,[z1,z2,z3,z487,z77,z8])],[(0,[z32,z3,z185,z4,z5,z8]),(0,[z1,z2,z3,z4,z1303,z8]),(0,[z1,z2,z3,z16,z685,z5]),(0,[z1,z2,z3,z1304,z4,z5]),(1,[z1,z2,z3,z24,z119])],[(0,[z272,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z1305,z5,z8]),(0,[z1,z2,z3,z20,z4,z56]),(0,[z1,z2,z3,z24,z4,z129]),(0,[z1,z2,z4,z5,z1306,z51]),(0,[z1,z2,z3,z24,z34,z10]),(0,[z1,z2,z3,z20,z8,z285])],[(0,[z1,z2,z3,z63,z343,z5]),(0,[z1,z2,z3,z4,z123,z51])],[(0,[z1,z2,z3,z304,z270,z4]),(0,[z1,z2,z3,z391,z24,z16]),(0,[z1,z2,z3,z4,z5,z1023])],[(0,[z1,z2,z185,z4,z114,z8]),(0,[z1,z2,z3,z4,z134,z212]),(0,[z1,z2,z3,z1307,z5,z10]),(0,[z1,z2,z3,z16,z5,z29]),(0,[z1,z2,z3,z24,z8,z235])],[(0,[z1,z2,z3,z343,z104,z8]),(0,[z1,z2,z3,z1308,z4,z5]),(0,[z1,z2,z3,z1309,z4,z5]),(0,[z1,z2,z3,z284,z4,z5]),(0,[z1,z2,z3,z4,z330,z10]),(0,[z1,z2,z3,z677,z326,z8]),(0,[z1,z2,z3,z24,z292,z8]),(0,[z1,z2,z3,z5,z8,z285])],[(0,[z113,z32,z3,z4,z114,z8]),(0,[z1,z177,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z5,z171]),(0,[z1,z3,z52,z167,z4,z5]),(0,[z1,z2,z3,z1310,z4,z5]),(0,[z1,z2,z3,z4,z5,z1311]),(0,[z1,z2,z3,z24,z226,z94]),(0,[z1,z2,z3,z24,z16,z20])]],
   [[(0,[z1,z2,z3,z1312,z118,z8]),(0,[z1,z2,z3,z4,z1061,z8]),(0,[z1,z194,z3,z4,z5,z892]),(0,[z1,z2,z3,z4,z5,z1313]),(0,[z1,z2,z3,z63,z433,z5]),(0,[z1,z2,z3,z25,z5,z79])],[(0,[z1,z2,z1314,z4,z5,z8]),(0,[z1,z2,z345,z34,z5,z8]),(0,[z1,z2,z3,z24,z467,z4]),(0,[z1,z2,z3,z4,z78,z102])],[(0,[z1,z2,z3,z1315,z5,z8]),(0,[z1,z2,z3,z1316,z5,z8]),(0,[z542,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1317,z5,z8]),(0,[z1,z2,z3,z4,z5,z1318]),(0,[z1,z2,z3,z16,z5,z206])],[(0,[z1,z2,z3,z4,z1319,z8]),(0,[z1,z2,z3,z1320,z4,z8]),(0,[z1,z2,z3,z16,z4,z187]),(0,[z0,z1,z2,z3,z25,z5]),(0,[z526,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z134,z64])],[(0,[z1,z2,z3,z1321,z5,z8]),(0,[z1,z2,z3,z1322,z4,z8]),(0,[z1,z2,z3,z343,z5,z202]),(0,[z1,z2,z3,z842,z142,z8]),(1,[z1,z2,z3,z24,z276])],[(0,[z1,z2,z3,z4,z133,z69]),(0,[z122,z1,z19,z142,z5,z8]),(0,[z1,z2,z3,z1323,z4,z5]),(0,[z1,z2,z3,z5,z10,z1324]),(0,[z1,z2,z3,z284,z5,z218]),(0,[z1,z2,z3,z24,z34,z8])],[(0,[z1,z2,z3,z4,z123,z10]),(0,[z1,z3,z24,z402,z167,z8]),(0,[z1,z2,z3,z4,z5,z183])],[(0,[z1,z2,z3,z118,z501,z8]),(0,[z1,z2,z3,z1325,z4,z8]),(0,[z1,z2,z3,z4,z5,z1326]),(0,[z141,z2,z3,z208,z5,z10]),(0,[z1,z2,z3,z4,z5,z971]),(0,[z1,z2,z3,z20,z77,z51]),(0,[z500,z1,z2,z3,z24,z16])],[(0,[z1,z2,z1327,z3,z4,z5]),(0,[z1,z2,z3,z16,z262,z4]),(0,[z1,z2,z3,z4,z5,z1328]),(0,[z1,z2,z3,z4,z497,z325]),(0,[z1,z2,z3,z4,z325,z6]),(0,[z1,z2,z3,z4,z64,z424])],[(0,[z145,z2,z121,z4,z104,z8]),(0,[z1,z128,z3,z4,z18,z51]),(0,[z1,z2,z3,z4,z256,z51]),(0,[z1,z2,z3,z4,z1329,z8]),(0,[z1,z2,z37,z4,z720,z8]),(0,[z278,z1,z2,z3,z24,z8])],[(0,[z1,z177,z3,z4,z5,z10]),(0,[z1,z2,z3,z20,z343,z8]),(0,[z1,z2,z139,z3,z4,z5])],[(0,[z1,z259,z2,z3,z24,z8]),(0,[z1,z2,z1330,z3,z4,z5]),(0,[z1,z2,z3,z13,z8,z26]),(0,[z55,z2,z509,z3,z4,z5]),(0,[z1,z2,z3,z4,z1331,z8]),(0,[z1,z2,z3,z276,z284,z5]),(0,[z1,z2,z173,z34,z5,z8]),(0,[z1,z2,z3,z429,z64,z8])],[(0,[z32,z121,z19,z4,z5,z8]),(0,[z150,z664,z3,z4,z5,z8]),(0,[z145,z2,z121,z16,z4,z5]),(0,[z1,z96,z3,z119,z4,z5]),(0,[z1,z2,z3,z1332,z4,z5]),(0,[z1,z2,z3,z24,z203,z51]),(0,[z1,z2,z3,z20,z4,z1282])],[(0,[z1,z2,z1333,z4,z5,z8]),(0,[z1,z2,z3,z157,z16,z4]),(0,[z1,z2,z3,z1334,z5,z8]),(0,[z1,z2,z3,z4,z325,z10]),(0,[z1,z2,z3,z433,z5,z51]),(0,[z1,z2,z3,z4,z5,z1335]),(0,[z1,z2,z3,z4,z5,z1336]),(0,[z1,z2,z3,z103,z4,z102])],[(0,[z1,z2,z3,z1250,z4,z8]),(0,[z1,z2,z3,z4,z1337,z8])],[(0,[z145,z2,z121,z4,z5,z202]),(0,[z1,z2,z1060,z4,z5,z8]),(0,[z1,z2,z3,z326,z5,z129]),(0,[z1,z2,z3,z63,z4,z256]),(0,[z1,z2,z3,z4,z1338,z8])]],
   [[(0,[z1,z2,z3,z4,z1339,z8]),(0,[z1,z194,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z227,z131]),(0,[z272,z2,z3,z63,z4,z5]),(0,[z1,z2,z3,z1340,z4,z5]),(0,[z143,z1,z3,z52,z4,z5]),(0,[z1,z2,z3,z5,z8,z1324]),(0,[z1,z2,z3,z5,z8,z1341])],[(0,[z1,z2,z3,z534,z34,z5]),(0,[z1,z2,z3,z4,z5,z1342]),(1,[z1,z2,z3,z4,z954])],[(0,[z141,z2,z3,z208,z5,z8]),(0,[z1,z2,z3,z213,z262,z4]),(0,[z191,z2,z3,z13,z60,z8]),(0,[z1,z2,z3,z1116,z4,z8]),(0,[z1,z2,z3,z4,z5,z1343]),(0,[z1,z2,z3,z16,z193,z5]),(0,[z1,z2,z3,z1344,z5,z8])],[(0,[z1,z2,z3,z1345,z4,z5]),(0,[z1,z2,z3,z4,z1087,z8]),(0,[z1,z2,z100,z34,z5,z316]),(0,[z1,z2,z1346,z3,z4,z5])],[(0,[z1,z2,z197,z4,z5,z10]),(0,[z1,z1347,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z256,z10]),(0,[z1,z2,z321,z4,z5,z79])],[(0,[z1,z2,z3,z54,z5,z10]),(0,[z1,z2,z3,z1348,z4,z5]),(0,[z1,z2,z3,z20,z40,z8]),(0,[z1,z2,z3,z4,z123,z458]),(0,[z1,z2,z3,z284,z35,z5]),(0,[z1,z2,z3,z4,z338,z10]),(0,[z1,z2,z4,z720,z85,z8])],[(0,[z1,z2,z3,z4,z1349,z8]),(0,[z1,z2,z3,z24,z486,z8]),(0,[z1,z2,z321,z426,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1350]),(0,[z1,z2,z3,z4,z5,z1351])],[(0,[z1,z2,z3,z4,z5,z1352]),(0,[z1,z2,z3,z4,z325,z8])],[(0,[z1,z2,z3,z1353,z4,z5]),(0,[z1,z2,z3,z4,z1354,z5]),(0,[z1,z2,z3,z24,z4,z163]),(0,[z1,z2,z3,z433,z50,z8])],[(0,[z113,z32,z185,z4,z5,z8]),(0,[z1,z90,z3,z770,z5,z8]),(0,[z207,z2,z3,z481,z4,z8])],[(0,[z1,z32,z3,z119,z4,z5]),(0,[z1,z2,z3,z936,z54,z5]),(0,[z1,z2,z3,z1355,z4,z5]),(0,[z1,z2,z3,z4,z5,z1356]),(0,[z1,z2,z3,z4,z5,z1357]),(0,[z1,z2,z815,z4,z5,z8]),(0,[z1,z2,z3,z1358,z4,z5]),(0,[z1,z90,z2,z3,z24,z16]),(0,[z1,z2,z3,z24,z270,z4]),(0,[z1,z2,z3,z16,z42,z5]),(0,[z1,z2,z3,z24,z16,z525]),(0,[z1,z2,z1231,z3,z4,z5])],[(0,[z1,z2,z185,z195,z5,z8]),(0,[z1,z2,z3,z4,z47,z124]),(0,[z1,z2,z3,z13,z205,z5]),(0,[z1,z2,z3,z1359,z4,z8]),(0,[z1,z28,z815,z4,z5,z8]),(0,[z1,z2,z590,z4,z5,z169]),(0,[z1,z2,z3,z4,z1360,z8]),(0,[z1,z2,z3,z4,z5,z1073]),(1,[z1,z2,z3,z915,z8])],[(0,[z1,z2,z3,z1361,z5,z8]),(0,[z122,z1,z19,z16,z4,z5]),(0,[z1,z2,z3,z24,z94,z8])],[(0,[z113,z32,z3,z195,z5,z8]),(0,[z1,z1362,z3,z4,z5,z8]),(0,[z389,z2,z3,z4,z5,z131]),(0,[z1,z2,z3,z276,z77,z5]),(0,[z1,z2,z3,z16,z4,z53]),(0,[z1,z2,z3,z20,z4,z271])],[(0,[z1,z2,z197,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z468]),(0,[z1,z784,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1363]),(0,[z272,z2,z3,z20,z4,z8]),(1,[z1,z2,z3,z24,z99]),(0,[z1,z58,z3,z677,z4,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z1364]),(0,[z1,z2,z3,z4,z5,z1365])],[(0,[z1,z2,z1366,z3,z5,z8]),(0,[z1,z2,z3,z1367,z5,z8]),(0,[z1,z2,z3,z4,z134,z417])],[(0,[z1,z600,z2,z3,z16,z5]),(0,[z1,z2,z3,z4,z5,z1368]),(0,[z1,z2,z3,z1205,z125,z8]),(0,[z1,z2,z3,z103,z4,z29])],[(0,[z75,z2,z232,z63,z4,z5]),(0,[z1,z2,z3,z1369,z4,z5]),(0,[z1,z2,z3,z24,z65,z8]),(0,[z1,z2,z3,z226,z20,z4])],[(0,[z283,z32,z3,z4,z5,z8]),(0,[z1,z2,z3,z1370,z4,z5]),(0,[z1,z2,z3,z20,z4,z171]),(0,[z1,z2,z3,z887,z142,z5]),(0,[z1,z2,z3,z16,z246,z5]),(1,[z1,z2,z4,z720,z8])],[(0,[z1,z2,z3,z63,z4,z325])],[(0,[z1,z2,z3,z4,z114,z250]),(0,[z1,z2,z1371,z3,z5,z8]),(0,[z1,z2,z3,z4,z5,z1372]),(0,[z0,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z4,z8,z235]),(0,[z506,z2,z3,z523,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1373]),(0,[z1,z2,z3,z276,z94,z5]),(0,[z1,z2,z100,z16,z34,z5])],[(0,[z1,z2,z3,z4,z1374,z8]),(0,[z1,z2,z3,z4,z1375,z5]),(1,[z1,z3,z4,z5,z768]),(0,[z1,z2,z37,z4,z50,z51]),(0,[z1,z2,z3,z24,z438,z8]),(0,[z1,z248,z2,z3,z24,z16]),(0,[z1,z2,z3,z24,z4,z179])],[(0,[z1,z2,z3,z4,z114,z51]),(0,[z150,z201,z3,z4,z5,z468]),(0,[z1,z2,z3,z157,z4,z10]),(0,[z1,z2,z3,z1376,z5,z8]),(0,[z1,z2,z3,z1377,z5,z8]),(0,[z1,z2,z3,z16,z4,z517]),(0,[z1,z2,z3,z24,z362,z8])],[(0,[z1,z2,z3,z4,z5,z1378]),(0,[z2,z3,z908,z4,z5,z8]),(0,[z1,z2,z3,z1379,z4,z5]),(0,[z1,z2,z3,z4,z5,z1380]),(0,[z1,z2,z4,z733,z5,z8])],[(0,[z1,z177,z3,z63,z4,z5]),(0,[z1,z2,z3,z24,z233,z8]),(0,[z1,z2,z3,z770,z5,z8]),(0,[z1,z2,z3,z4,z5,z1381]),(0,[z1,z2,z3,z16,z304,z5])],[(0,[z1,z2,z3,z4,z1382,z8]),(0,[z1,z557,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z5,z1383]),(0,[z1384,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1385])],[(0,[z1,z2,z3,z4,z5,z1386]),(0,[z88,z201,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1387,z8]),(0,[z55,z2,z3,z4,z5,z849]),(0,[z1,z28,z2,z3,z24,z16]),(0,[z1,z2,z3,z270,z125,z5]),(0,[z1,z2,z3,z24,z610,z8])],[(0,[z1,z2,z3,z118,z5,z67]),(0,[z681,z2,z3,z208,z5,z8]),(0,[z1,z2,z3,z24,z16,z34]),(0,[z1,z2,z132,z3,z429,z5])],[(0,[z1,z2,z3,z24,z213,z4]),(1,[z1,z2,z733,z5,z8]),(0,[z1,z2,z3,z622,z4,z78])]],
   [[(0,[z1,z1388,z3,z4,z5,z8]),(0,[z1,z2,z3,z13,z16,z5]),(0,[z1,z2,z3,z1389,z4,z8]),(0,[z1,z2,z3,z4,z1390,z8]),(0,[z1,z2,z3,z24,z179,z109]),(0,[z1,z2,z1189,z63,z4,z5]),(0,[z1,z2,z3,z4,z134,z44])],[(0,[z1,z194,z3,z63,z4,z5]),(0,[z1,z2,z3,z24,z534,z4]),(0,[z1,z2,z3,z1391,z4,z5]),(0,[z126,z1,z2,z3,z24,z16]),(0,[z122,z1,z2,z3,z24,z16]),(0,[z1,z2,z3,z946,z326,z5]),(0,[z1,z2,z3,z16,z315,z5])],[(0,[z75,z2,z232,z20,z4,z8]),(0,[z1,z2,z3,z4,z1392,z8])],[(0,[z1,z2,z185,z24,z4,z8]),(0,[z1,z2,z3,z63,z54,z5]),(0,[z1,z2,z3,z1393,z4,z5]),(0,[z333,z1,z3,z4,z5,z10]),(0,[z1,z2,z3,z429,z63,z5]),(0,[z1,z2,z3,z429,z134,z5])],[(0,[z1,z2,z3,z157,z4,z8]),(0,[z1,z2,z3,z13,z18,z8]),(0,[z1,z2,z159,z3,z4,z325]),(0,[z1,z2,z3,z4,z1394,z8]),(0,[z1,z2,z3,z16,z192,z4]),(0,[z1,z2,z3,z1395,z4,z5]),(0,[z1,z2,z3,z16,z125,z5])],[(0,[z1,z2,z197,z63,z4,z5]),(0,[z113,z32,z3,z24,z4,z8]),(0,[z1,z2,z3,z4,z5,z1396]),(0,[z1,z2,z3,z16,z558,z5]),(0,[z1,z2,z3,z4,z1040,z8]),(0,[z1,z2,z3,z4,z497,z85]),(0,[z1,z2,z3,z1397,z5,z8]),(0,[z1,z2,z3,z94,z184,z8]),(0,[z1,z2,z3,z103,z4,z26])],[(0,[z1,z2,z3,z135,z5,z300]),(0,[z1,z2,z3,z1398,z5,z8]),(0,[z1,z2,z3,z63,z98,z5]),(0,[z1,z2,z100,z34,z5,z10])],[(0,[z561,z2,z3,z93,z5,z8]),(0,[z273,z2,z3,z4,z84,z8]),(0,[z1,z2,z3,z16,z4,z585])],[(0,[z1,z2,z3,z1211,z4,z5]),(0,[z1,z2,z3,z4,z5,z1399]),(0,[z1,z2,z3,z4,z1400,z5]),(0,[z1,z2,z156,z3,z24,z16]),(0,[z1,z2,z3,z4,z1401,z10]),(0,[z1,z2,z3,z4,z1402,z8])],[(0,[z1,z2,z3,z4,z5,z1403]),(0,[z1,z2,z3,z295,z5,z51])],[(0,[z1,z2,z3,z4,z303,z212]),(0,[z1,z2,z3,z429,z5,z51])],[(0,[z1,z2,z3,z776,z4,z8]),(0,[z279,z2,z121,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1404]),(0,[z191,z1,z2,z3,z13,z8]),(0,[z1,z2,z3,z4,z1405,z5]),(0,[z1,z2,z3,z16,z487,z94]),(0,[z1,z2,z530,z3,z4,z43])],[(0,[z1,z2,z3,z4,z47,z202]),(0,[z1,z2,z3,z4,z1406,z8]),(0,[z1,z2,z3,z4,z1407,z5]),(0,[z272,z2,z3,z4,z5,z300]),(0,[z1,z2,z3,z4,z1408,z8]),(0,[z1,z2,z3,z24,z382,z8]),(0,[z1,z2,z3,z4,z5,z271]),(0,[z1,z2,z723,z24,z4,z8]),(0,[z1,z2,z630,z355,z4,z5])],[(0,[z1,z2,z3,z16,z4,z114]),(0,[z1,z2,z1409,z4,z5,z8]),(0,[z1410,z2,z3,z4,z5,z8]),(0,[z1,z2,z282,z485,z4,z5])],[(0,[z1,z2,z3,z24,z118,z8]),(0,[z1,z2,z37,z4,z50,z264]),(0,[z1,z2,z3,z5,z8,z1114])],[(0,[z1,z2,z3,z882,z4,z8]),(0,[z1,z3,z24,z167,z35,z8]),(0,[z1,z2,z3,z24,z4,z228]),(0,[z1,z2,z3,z4,z5,z101])]],
   [[(0,[z1,z194,z3,z20,z4,z8]),(0,[z1,z2,z3,z4,z5,z1411]),(0,[z1,z2,z3,z4,z1412,z8]),(0,[z1,z2,z3,z304,z4,z51]),(0,[z1,z2,z3,z4,z517,z308]),(0,[z1,z2,z3,z63,z4,z1075]),(1,[z1,z2,z3,z429,z78])],[(0,[z1,z2,z185,z4,z5,z250]),(0,[z1,z2,z3,z4,z1413,z8]),(0,[z1,z2,z3,z1414,z4,z5]),(0,[z1,z2,z3,z4,z5,z1415])],[(0,[z1,z2,z3,z20,z54,z8]),(0,[z1,z2,z3,z1416,z4,z8]),(0,[z1,z2,z3,z65,z192,z4]),(0,[z1,z2,z3,z622,z4,z374])],[(0,[z113,z32,z3,z4,z5,z250]),(0,[z1,z2,z3,z4,z1417,z8]),(0,[z1,z2,z3,z4,z5,z1418]),(0,[z1,z2,z3,z5,z1419,z51]),(0,[z1,z2,z3,z487,z4,z51]),(0,[z1,z2,z3,z24,z298,z10]),(0,[z1,z2,z3,z4,z1401,z8]),(0,[z1,z2,z520,z94,z5,z8]),(0,[z1,z2,z3,z24,z24,z16]),(0,[z389,z2,z3,z684,z4,z5])],[(0,[z1,z2,z185,z4,z5,z51]),(0,[z1,z2,z197,z20,z4,z8]),(0,[z1,z2,z3,z63,z326,z5]),(0,[z1,z3,z52,z4,z5,z51]),(0,[z1,z2,z3,z24,z4,z739]),(0,[z1,z2,z3,z393,z24,z16])],[(0,[z1,z2,z3,z195,z5,z250]),(0,[z191,z2,z3,z4,z730,z8]),(0,[z1,z2,z3,z4,z5,z1420]),(0,[z1,z2,z3,z20,z98,z8]),(0,[z1,z2,z3,z4,z137,z10]),(0,[z1,z2,z3,z4,z8,z1421])],[(0,[z113,z32,z3,z4,z5,z51]),(0,[z1,z2,z3,z16,z4,z133]),(0,[z1,z2,z3,z77,z5,z274]),(0,[z1,z2,z3,z24,z311,z8]),(0,[z122,z1,z19,z135,z5,z8]),(0,[z1,z2,z1422,z4,z5,z51]),(0,[z1,z2,z3,z1423,z5,z10]),(0,[z1,z2,z3,z4,z134,z954])],[(0,[z1,z2,z3,z4,z5,z1424]),(0,[z1,z2,z3,z4,z5,z1425])],[(0,[z1,z2,z3,z195,z5,z51]),(0,[z1,z2,z3,z1426,z5,z8]),(0,[z0,z2,z3,z4,z325,z131]),(0,[z1,z2,z3,z16,z371,z5]),(0,[z1,z2,z3,z222,z563,z4]),(0,[z1,z2,z3,z1427,z5,z8]),(0,[z1,z1272,z3,z16,z4,z5])],[(0,[z409,z2,z3,z4,z84,z8]),(0,[z526,z2,z3,z4,z123,z8]),(0,[z1,z2,z3,z63,z160,z5])],[(0,[z1,z2,z3,z1428,z5,z8]),(0,[z1,z2,z1429,z3,z4,z5]),(0,[z1,z2,z3,z4,z293,z5])],[(0,[z1,z177,z3,z343,z5,z8]),(0,[z1,z2,z3,z157,z35,z8]),(0,[z1,z2,z3,z889,z4,z5]),(0,[z1,z2,z3,z1307,z5,z8]),(0,[z1,z2,z3,z1430,z5,z8])],[(0,[z115,z1,z19,z4,z5,z8]),(0,[z1,z201,z2,z3,z24,z16]),(0,[z1,z2,z3,z1431,z4,z8]),(0,[z1,z2,z3,z1432,z4,z5]),(0,[z1,z2,z3,z4,z5,z1433]),(0,[z1,z2,z3,z4,z330,z8]),(0,[z1,z33,z3,z4,z71,z56]),(0,[z1,z2,z3,z4,z1434,z8]),(0,[z1,z2,z3,z432,z20,z8])],[(0,[z2,z3,z4,z726,z5,z8]),(0,[z1,z2,z3,z4,z5,z1435]),(0,[z1,z3,z4,z5,z51,z428]),(0,[z1,z2,z3,z4,z5,z1436])],[(0,[z1,z2,z3,z1033,z4,z8]),(0,[z1,z2,z3,z4,z1437,z5]),(0,[z1,z2,z3,z4,z1438,z8]),(0,[z1,z2,z3,z4,z1299,z8]),(0,[z1,z2,z3,z24,z298,z8]),(0,[z379,z1,z2,z3,z24,z8])],[(0,[z1,z2,z3,z4,z725,z51]),(0,[z1,z2,z3,z34,z5,z101]),(0,[z154,z1,z3,z402,z4,z8]),(0,[z1,z2,z3,z20,z4,z1380]),(0,[z1,z2,z173,z332,z4,z5])]],
   [[(0,[z75,z2,z232,z4,z5,z8]),(0,[z1,z2,z3,z1439,z5,z8]),(0,[z1,z2,z3,z4,z137,z8]),(0,[z1,z2,z3,z16,z36,z5]),(0,[z1,z2,z3,z4,z5,z1440]),(0,[z1,z2,z159,z3,z24,z16]),(0,[z1,z2,z3,z149,z4,z26])],[(0,[z1,z194,z3,z343,z5,z8]),(0,[z1,z2,z3,z1423,z5,z8])],[(0,[z1,z2,z1441,z3,z4,z8]),(0,[z1,z2,z159,z61,z4,z5]),(0,[z1,z2,z3,z1432,z135,z5]),(1,[z1,z2,z3,z24,z65]),(0,[z1,z2,z3,z276,z34,z5]),(0,[z1,z2,z3,z20,z433,z8])],[(0,[z1,z2,z3,z195,z5,z10]),(0,[z1,z2,z4,z5,z1306,z8]),(0,[z1,z2,z3,z297,z16,z5]),(0,[z1,z2,z3,z20,z326,z8]),(0,[z1,z2,z3,z24,z623,z8]),(0,[z1,z2,z3,z24,z4,z878])],[(0,[z1,z2,z3,z1021,z4,z8]),(0,[z1,z2,z3,z4,z104,z124]),(0,[z1,z2,z3,z24,z16,z93]),(0,[z1,z2,z3,z4,z123,z8]),(0,[z1,z2,z3,z1442,z4,z8]),(0,[z1,z2,z3,z24,z546,z8]),(0,[z1,z2,z3,z4,z1443,z5]),(0,[z1,z2,z3,z24,z323,z8])],[(0,[z1,z2,z3,z16,z195,z5]),(0,[z1,z2,z3,z16,z313,z5]),(0,[z1,z2,z3,z20,z77,z10])],[(0,[z1,z2,z3,z1444,z5,z8]),(0,[z1,z2,z3,z4,z5,z1445]),(0,[z1,z2,z3,z4,z1036,z8]),(0,[z1,z2,z3,z1446,z5,z8])],[(0,[z1,z2,z3,z1447,z4,z5]),(1,[z526,z19,z4,z5,z8]),(0,[z1,z2,z3,z63,z142,z5]),(0,[z1,z2,z3,z24,z276,z5]),(0,[z1,z2,z3,z4,z1448,z8]),(0,[z1,z2,z159,z24,z4,z308]),(0,[z1,z2,z3,z24,z16,z308]),(0,[z1,z2,z3,z622,z4,z626])],[(0,[z1,z177,z3,z4,z5,z8]),(0,[z150,z201,z3,z24,z4,z8]),(0,[z1,z2,z3,z24,z598,z8]),(0,[z1,z2,z269,z3,z16,z5])],[(0,[z769,z32,z3,z4,z5,z8]),(0,[z1,z2,z3,z1449,z5,z8]),(0,[z1,z2,z3,z24,z677,z8]),(0,[z1,z2,z23,z3,z24,z16]),(0,[z1,z2,z3,z24,z119,z4])],[(0,[z1,z2,z3,z16,z515,z5]),(0,[z1,z2,z3,z4,z5,z1450]),(0,[z1,z2,z3,z1451,z4,z8]),(0,[z1,z2,z3,z4,z1452,z8])],[(0,[z1,z2,z3,z4,z5,z1453]),(0,[z1,z1454,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1295]),(0,[z1,z2,z690,z4,z50,z8]),(0,[z1,z2,z3,z4,z5,z1455]),(0,[z1,z2,z3,z433,z5,z10])],[(0,[z1,z2,z3,z24,z4,z250]),(0,[z1,z2,z3,z4,z5,z1456]),(0,[z145,z194,z121,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1457]),(0,[z1,z2,z3,z4,z954,z26])],[(0,[z1,z2,z3,z4,z1458,z8]),(0,[z395,z2,z3,z208,z5,z8]),(0,[z1,z2,z3,z4,z5,z1459]),(0,[z1,z90,z3,z35,z5,z51]),(0,[z1,z2,z3,z4,z720,z8]),(0,[z1,z2,z1189,z4,z5,z8]),(0,[z1,z2,z3,z4,z64,z954])],[(0,[z1,z194,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1460,z8]),(0,[z141,z2,z3,z336,z5,z8]),(0,[z1,z2,z3,z4,z5,z1461])],[(0,[z1,z2,z197,z4,z5,z67]),(0,[z1,z1462,z3,z4,z5,z8]),(0,[z1,z33,z3,z4,z1173,z8]),(0,[z1,z2,z3,z24,z4,z51]),(0,[z1,z2,z3,z99,z5,z319]),(0,[z1,z2,z3,z16,z575,z5]),(0,[z1,z2,z3,z24,z63,z218])]],
   [[(0,[z150,z2,z185,z4,z5,z8]),(0,[z1,z2,z1463,z3,z4,z5]),(0,[z191,z2,z3,z4,z60,z171]),(0,[z272,z2,z3,z16,z4,z5]),(0,[z1,z2,z3,z4,z5,z1301]),(0,[z1,z2,z3,z34,z137,z8]),(0,[z1,z2,z3,z24,z985,z8]),(0,[z1,z2,z530,z3,z4,z134])],[(0,[z145,z2,z121,z54,z5,z8]),(0,[z1,z2,z3,z42,z5,z51]),(0,[z1,z2,z3,z63,z25,z5])],[(0,[z1,z2,z3,z24,z65,z5]),(0,[z1,z2,z676,z4,z50,z8]),(0,[z1,z2,z3,z4,z256,z8]),(0,[z1,z2,z3,z293,z77,z5])],[(0,[z1,z2,z3,z54,z5,z8]),(0,[z1,z2,z3,z24,z1033,z8]),(0,[z1,z2,z3,z24,z435,z8]),(0,[z1,z2,z3,z4,z338,z8]),(0,[z1,z2,z3,z4,z184,z51]),(0,[z1,z2,z3,z77,z5,z1028])],[(0,[z1,z2,z3,z4,z1464,z8]),(0,[z145,z2,z139,z121,z4,z5]),(0,[z126,z2,z3,z16,z4,z84]),(0,[z1,z2,z3,z20,z4,z101]),(0,[z1,z2,z3,z24,z293,z5])],[(0,[z1,z2,z3,z1465,z4,z5]),(0,[z1,z2,z3,z1466,z4,z5]),(0,[z1,z2,z3,z16,z4,z227]),(0,[z1,z2,z3,z24,z4,z474]),(0,[z1,z2,z3,z24,z203,z8])],[(0,[z1,z2,z1467,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1468]),(0,[z55,z1,z2,z3,z4,z517]),(0,[z1,z2,z3,z20,z142,z8]),(0,[z1,z2,z3,z433,z5,z8]),(0,[z1,z2,z3,z433,z5,z264])],[(0,[z1,z2,z1469,z3,z4,z5]),(0,[z1,z3,z4,z770,z5,z8]),(0,[z1,z2,z3,z24,z63,z94])],[(0,[z1,z2,z3,z4,z1470,z8]),(0,[z1,z90,z3,z35,z5,z10])],[(0,[z150,z201,z3,z4,z5,z51]),(0,[z1,z2,z3,z1471,z5,z8]),(0,[z1,z2,z590,z4,z5,z308])],[(0,[z1,z2,z3,z4,z5,z1472]),(0,[z1,z2,z3,z922,z50,z5])],[(0,[z1,z2,z3,z4,z1473,z8]),(0,[z1474,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z24,z4,z415]),(0,[z1,z2,z3,z1475,z4,z8]),(0,[z1,z2,z3,z24,z16,z35]),(0,[z1,z2,z3,z24,z429,z8]),(0,[z1,z2,z3,z16,z485,z5])],[(0,[z1,z2,z3,z4,z5,z1476]),(0,[z141,z2,z3,z63,z208,z5]),(0,[z1,z2,z3,z1477,z4,z5]),(0,[z431,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z42,z5,z10]),(0,[z1,z2,z3,z4,z1478,z8]),(0,[z1,z2,z81,z34,z5,z8]),(0,[z1,z2,z3,z4,z915,z8]),(0,[z1,z2,z3,z4,z5,z1479])],[(0,[z122,z272,z19,z4,z5,z8]),(0,[z1,z2,z3,z1480,z4,z8]),(0,[z1,z2,z3,z4,z5,z1481])],[(0,[z1,z2,z1482,z4,z5,z8]),(0,[z1,z2,z139,z3,z24,z4]),(0,[z1,z2,z3,z4,z1483,z8]),(0,[z1,z2,z3,z4,z5,z1484]),(0,[z1,z2,z3,z1485,z4,z5]),(0,[z1,z281,z3,z4,z5,z51]),(0,[z1,z2,z3,z1244,z4,z5]),(0,[z1,z2,z132,z4,z5,z732]),(0,[z1,z2,z3,z5,z285,z166])],[(0,[z1,z2,z3,z1486,z4,z5]),(0,[z1,z221,z3,z4,z5,z51]),(0,[z1,z2,z3,z4,z5,z1487])]],
   [[(0,[z1,z2,z3,z4,z5,z1268]),(0,[z1,z2,z3,z20,z25,z8])],[(0,[z1,z2,z3,z1488,z4,z8]),(0,[z1489,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z534,z20,z4]),(0,[z1490,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z16,z494,z5])],[(0,[z1,z2,z3,z4,z5,z1491]),(0,[z1,z2,z3,z20,z4,z497]),(0,[z1,z2,z1492,z3,z4,z5]),(0,[z1,z2,z3,z226,z487,z4])],[(0,[z1,z2,z3,z1493,z4,z5]),(0,[z1,z2,z3,z4,z104,z202]),(0,[z1,z2,z1225,z4,z5,z8]),(0,[z1,z2,z3,z1494,z4,z5]),(0,[z1,z2,z3,z326,z5,z51]),(0,[z1,z2,z3,z24,z226,z5]),(0,[z1,z2,z3,z1495,z4,z5])],[(0,[z1,z2,z1496,z4,z5,z8]),(0,[z1,z2,z421,z4,z5,z136]),(0,[z1,z2,z3,z24,z4,z264])],[(0,[z1,z2,z3,z4,z1497,z5]),(0,[z1,z2,z3,z24,z35,z51]),(0,[z1,z2,z37,z4,z50,z10]),(0,[z1,z2,z3,z24,z454,z8]),(0,[z1,z2,z3,z922,z4,z5]),(0,[z1,z2,z3,z4,z374,z26])],[(0,[z1,z2,z3,z4,z114,z10]),(0,[z1,z2,z3,z42,z5,z264]),(0,[z1,z2,z1346,z3,z24,z4]),(0,[z1,z2,z3,z20,z4,z1498])],[(0,[z1,z2,z3,z4,z1499,z8]),(0,[z283,z2,z121,z4,z5,z8]),(0,[z1,z2,z3,z1093,z98,z5]),(0,[z1,z2,z3,z4,z1262,z8]),(0,[z1,z2,z3,z922,z5,z8]),(0,[z1,z2,z3,z24,z4,z836])],[(0,[z1,z2,z3,z1500,z4,z8]),(0,[z1,z2,z3,z24,z4,z458]),(0,[z1,z2,z3,z4,z5,z1501])],[(0,[z1,z2,z3,z1312,z4,z8])],[(0,[z1,z2,z197,z4,z501,z8]),(0,[z1,z2,z3,z1502,z4,z5]),(0,[z141,z2,z3,z20,z208,z8]),(0,[z1,z90,z3,z24,z35,z8]),(0,[z1,z2,z3,z1503,z4,z8])],[(0,[z1,z2,z3,z4,z5,z1504]),(0,[z1,z2,z3,z653,z24,z8]),(0,[z1,z2,z3,z24,z8,z461]),(0,[z1,z2,z3,z4,z91,z51]),(0,[z1,z2,z3,z24,z491,z8]),(0,[z1,z2,z3,z4,z5,z712])],[(0,[z1,z177,z3,z20,z4,z8]),(0,[z1,z2,z3,z563,z20,z4])],[(0,[z2,z3,z4,z5,z849,z8]),(0,[z1,z2,z3,z1505,z4,z8]),(0,[z1,z2,z159,z4,z517,z308]),(0,[z1,z2,z3,z16,z350,z5])],[(0,[z1,z2,z3,z326,z5,z10]),(0,[z1,z2,z3,z1506,z4,z8]),(0,[z1,z2,z3,z24,z149,z8]),(0,[z1,z2,z3,z332,z24,z16])]],
   [[(0,[z1,z177,z3,z4,z5,z1132]),(0,[z1,z2,z3,z4,z1507,z8]),(0,[z1,z2,z3,z4,z5,z1508]),(0,[z1,z2,z3,z4,z1509,z8]),(0,[z1,z2,z3,z1203,z433,z5]),(1,[z1,z2,z4,z5,z732]),(0,[z1,z2,z3,z4,z5,z1245]),(0,[z1,z2,z3,z78,z285,z26])],[(0,[z1,z2,z3,z24,z35,z10]),(0,[z1,z3,z4,z5,z703,z10]),(0,[z1,z2,z3,z16,z5,z305]),(0,[z1,z2,z37,z4,z50,z8])],[(0,[z1,z2,z3,z4,z114,z8]),(0,[z1510,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1511,z8]),(0,[z1,z2,z3,z4,z1512,z5]),(0,[z1,z2,z3,z332,z24,z8]),(0,[z1,z2,z3,z4,z5,z722])],[(0,[z1,z2,z3,z429,z5,z6]),(0,[z1,z2,z3,z426,z25,z5])],[(0,[z1,z2,z3,z24,z535,z8]),(0,[z1,z2,z3,z4,z5,z1513]),(0,[z1,z58,z3,z4,z71,z8]),(0,[z1,z2,z3,z821,z5,z51]),(0,[z1,z2,z100,z34,z5,z8]),(0,[z1,z2,z3,z16,z705,z5]),(0,[z1,z2,z3,z25,z256,z8]),(0,[z1,z2,z3,z923,z20,z4])],[(0,[z1,z2,z197,z16,z4,z5]),(0,[z1,z2,z3,z4,z5,z1514]),(0,[z1,z2,z1515,z3,z4,z5]),(0,[z1,z2,z3,z1516,z5,z8]),(0,[z1,z2,z3,z4,z84,z183]),(0,[z1,z2,z450,z4,z5,z79]),(0,[z1,z2,z3,z4,z5,z1517]),(0,[z1,z2,z3,z24,z99,z4]),(0,[z670,z2,z3,z210,z4,z8]),(0,[z1,z2,z3,z20,z77,z200]),(0,[z544,z2,z3,z525,z4,z5])],[(0,[z1,z177,z3,z4,z5,z1144]),(0,[z1,z2,z3,z24,z4,z274]),(0,[z1,z2,z3,z205,z295,z5]),(0,[z1,z2,z3,z4,z517,z51]),(0,[z1,z2,z3,z24,z915,z8])],[(0,[z1,z2,z3,z726,z5,z8]),(0,[z1,z2,z3,z295,z5,z10]),(0,[z1,z2,z3,z467,z5,z203]),(0,[z1,z2,z3,z4,z91,z10]),(0,[z1,z2,z3,z4,z1518,z5]),(0,[z1,z2,z3,z155,z16,z5]),(0,[z1,z2,z3,z4,z78,z183]),(0,[z1,z2,z387,z4,z5,z308])],[(0,[z1,z2,z3,z1519,z5,z8]),(0,[z1,z2,z3,z1520,z4,z8]),(0,[z1,z2,z3,z4,z325,z131]),(0,[z1,z2,z3,z429,z5,z10]),(0,[z1,z2,z733,z94,z5,z8])],[(0,[z1,z2,z3,z4,z5,z468]),(0,[z1,z2,z3,z63,z4,z501]),(0,[z1,z194,z3,z4,z47,z8]),(0,[z251,z1,z19,z4,z5,z8]),(0,[z1,z2,z3,z24,z16,z84]),(0,[z272,z2,z3,z135,z5,z8]),(0,[z1,z2,z3,z20,z4,z129]),(0,[z1,z2,z3,z4,z985,z8]),(0,[z1,z2,z3,z4,z1521,z5])],[(0,[z1,z2,z3,z1522,z4,z5]),(0,[z1,z2,z3,z4,z839,z51]),(0,[z396,z2,z3,z4,z5,z399]),(0,[z1,z2,z3,z24,z4,z316]),(0,[z1,z2,z3,z4,z5,z1523])],[(0,[z272,z2,z3,z142,z5,z8])],[(0,[z1,z2,z3,z4,z1524,z5]),(0,[z1,z2,z3,z99,z167,z5])],[(0,[z1,z2,z3,z1525,z4,z5]),(0,[z1,z2,z3,z1526,z4,z5])],[(0,[z1,z2,z3,z54,z47,z8]),(0,[z1,z2,z3,z16,z343,z5]),(0,[z1,z2,z3,z4,z5,z1527]),(0,[z1,z2,z3,z1127,z13,z5]),(0,[z1,z2,z3,z24,z192,z8]),(0,[z1,z2,z3,z4,z843,z51]),(0,[z1,z2,z3,z304,z4,z10])],[(0,[z1,z28,z219,z4,z5,z8]),(0,[z1,z2,z3,z1066,z4,z5]),(0,[z1,z2,z3,z16,z1244,z5]),(0,[z1,z2,z3,z4,z53,z101]),(0,[z1,z2,z3,z1038,z4,z5]),(0,[z1,z2,z3,z24,z479,z8]),(0,[z1,z2,z3,z20,z4,z737])]],
   [[(0,[z1,z2,z3,z4,z5,z1528]),(0,[z1,z2,z3,z1529,z4,z8]),(0,[z1,z2,z3,z1530,z4,z5]),(0,[z1,z2,z3,z848,z5,z51])],[(0,[z1,z2,z3,z1234,z343,z5]),(0,[z1,z2,z3,z487,z4,z10]),(0,[z1,z2,z100,z34,z53,z8]),(0,[z1,z2,z3,z16,z432,z5]),(0,[z1,z2,z3,z24,z16,z4]),(0,[z1,z2,z3,z20,z4,z1479]),(0,[z1,z2,z3,z429,z4,z78])],[(0,[z1,z2,z185,z4,z5,z10]),(0,[z1,z2,z3,z295,z5,z8]),(0,[z1,z90,z3,z563,z35,z5]),(0,[z1,z2,z3,z4,z50,z264])],[(0,[z1,z337,z156,z4,z5,z8]),(0,[z1,z2,z3,z1531,z5,z8]),(0,[z1,z2,z3,z16,z433,z5]),(0,[z1,z2,z3,z429,z5,z8])],[(0,[z113,z32,z3,z4,z5,z10]),(0,[z1,z2,z4,z1532,z5,z8]),(0,[z68,z1,z2,z3,z24,z63]),(0,[z1,z2,z132,z355,z4,z5]),(0,[z1,z2,z3,z24,z16,z92])],[(0,[z1,z2,z3,z4,z5,z1498]),(0,[z1,z2,z3,z1121,z326,z5]),(0,[z1,z527,z2,z3,z24,z16])],[(0,[z1,z2,z3,z1533,z4,z5]),(0,[z1,z2,z3,z4,z5,z1534]),(0,[z1,z2,z3,z4,z1535,z5]),(0,[z670,z2,z3,z4,z60,z8]),(0,[z207,z1,z2,z3,z13,z8]),(0,[z1,z2,z3,z1116,z5,z8]),(0,[z1,z2,z3,z4,z123,z300]),(0,[z1,z2,z3,z4,z5,z1536]),(0,[z1,z156,z815,z4,z5,z8]),(0,[z1,z2,z3,z16,z426,z5]),(0,[z1,z2,z4,z5,z732,z8]),(0,[z1,z2,z3,z24,z16,z63]),(0,[z1,z2,z3,z63,z184,z218])],[(0,[z1,z1537,z3,z4,z5,z8]),(0,[z1,z2,z3,z429,z60,z8])],[(0,[z1,z2,z3,z1538,z5,z8]),(0,[z1,z2,z3,z4,z1539,z8]),(0,[z1,z2,z3,z1540,z4,z8]),(0,[z1,z2,z3,z19,z24,z16]),(0,[z1,z2,z23,z4,z85,z51]),(0,[z1,z2,z3,z16,z91,z92])],[(0,[z145,z177,z121,z4,z5,z8]),(0,[z1,z2,z3,z16,z40,z5]),(0,[z1,z2,z3,z304,z4,z8]),(0,[z1,z2,z3,z4,z5,z1541]),(0,[z1,z2,z23,z63,z4,z85])],[(0,[z1,z2,z3,z4,z1542,z8]),(0,[z141,z1,z2,z3,z24,z63]),(0,[z1,z2,z3,z63,z5,z722])],[(0,[z1,z3,z4,z1543,z5,z8]),(0,[z1,z2,z3,z4,z5,z1544])],[(0,[z1,z2,z3,z4,z1545,z5]),(0,[z1,z2,z3,z5,z1419,z8]),(0,[z1,z2,z3,z24,z493,z8]),(0,[z1,z2,z3,z24,z218,z51]),(0,[z1,z2,z3,z487,z4,z8]),(0,[z1,z2,z3,z4,z5,z1546]),(0,[z1,z2,z3,z4,z5,z1547])],[(0,[z1,z2,z3,z4,z5,z1548]),(0,[z1,z2,z3,z4,z1549,z5]),(0,[z2,z3,z4,z84,z730,z8]),(0,[z1,z2,z3,z4,z5,z1550]),(0,[z1,z2,z3,z4,z5,z1551]),(0,[z1,z2,z3,z4,z5,z1552]),(0,[z1,z2,z3,z16,z449,z5]),(0,[z1,z2,z3,z1222,z4,z8]),(0,[z500,z2,z3,z393,z4,z8])],[(0,[z1,z2,z3,z24,z4,z577]),(0,[z1,z2,z16,z355,z34,z5]),(0,[z1,z2,z3,z4,z5,z1553]),(0,[z1,z2,z3,z24,z196,z16])],[(0,[z1,z2,z1422,z4,z5,z8]),(0,[z2,z3,z4,z1554,z5,z8]),(0,[z1,z2,z3,z4,z1555,z8]),(0,[z1,z2,z3,z24,z4,z1016])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 476) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 476).take 476) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 952).take 473) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1425).take 185) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1610)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [476, 476, 473, 185] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 84).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 84).take 84).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 168).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 240).take 86).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 326).take 78).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 404).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 486).take 26).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [84, 84, 72, 86, 78, 82, 26] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_nil pcend)))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_38593

theorem PEqualNP.Outside.L_meta_38593 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 4008241384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 4008241384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38593.solve