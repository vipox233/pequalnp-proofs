import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39815

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
  Nat.testBit (4008372970 * 2 ^ 32 + 4007714944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000050a1530e1c37#64 ++ 0x00002850a9870e1b#64 ++ 0xe689f3e3f71e3c7f#64 ++ 0xf344f9f1fb8f1e3f#64 : BitVec 256),
   (0x0232c58cc362c58b#64 ++ 0x811962c661b162c5#64 ++ 0xff76cd9ccbe3c78f#64 ++ 0xffbb66ce65f1e3c7#64 : BitVec 256),
   (0x05850a170c016adc#64 ++ 0x02c2850b8600b56e#64 ++ 0xed870e1f0c03ffff#64 ++ 0x76c3870f8601ffff#64 : BitVec 256),
   (0x09d80fe00db40760#64 ++ 0x04ec07f006da03b0#64 ++ 0xfbf80fe00ffc07f0#64 ++ 0xfdfc07f007fe03f8#64 : BitVec 256),
   (0x11eff0000edbb000#64 ++ 0x08f7f800076dd800#64 ++ 0xd3fff0000ffff801#64 ++ 0xe9fff80007fffc00#64 : BitVec 256),
   (0x21ffaf5aa0000000#64 ++ 0x10ffd7ad50000000#64 ++ 0xbdfffffff0000001#64 ++ 0xdefffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000000a151040c37 0x00000050a882061b 0x240003e3f000047e 0x120001f1f800023f

def z1 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xff76cd9ccbe3c78f 0xffbb66ce65f1e3c7

def z2 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z3 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z4 : W := mkw 0x11efa0000cd1a000 0x08f7d0000668d000 0x1176000008e1c000 0x08bb00000470e000

def z5 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xd3fff0000ffff801 0xe9fff80007fffc00

def z6 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xbdfffffff0000001 0xdefffffff8000000

def z7 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0xe689f3e3f71e3c7f 0xf344f9f1fb8f1e3f

def z8 : W := mkw 0x21efaa5aa0000000 0x10f7d52d50000000 0x048ff27ff0000001 0x0247f93ff8000000

def z9 : W := mkw 0x0a0040a44ff6c7eb 0x8500205227fb63f5 0x420000000fffc7fe 0x2100000007ffe3ff

def z10 : W := mkw 0x0000000000000000 0x0000000000000000 0xa400c180c0000001 0xd20060c060000000

def z11 : W := mkw 0x0000000000000000 0x0000000000000000 0xe080020004000470 0x7040010002000238

def z12 : W := mkw 0x0000000100000814 0x000000008000040a 0xe481020304023c7f 0x7240810182011e3f

def z13 : W := mkw 0x0000000400004088 0x0000000200002044 0xed060c1c0803c78f 0x7683060e0401e3c7

def z14 : W := mkw 0x0222c00cc242c08b 0x8111600661216045 0x0406c01cc003c00f 0x0203600e6001e007

def z15 : W := mkw 0x01ffaf4000000000 0x00ffd7a000000000 0xb9ffffe000000001 0xdcfffff000000000

def z16 : W := mkw 0x0000000100000814 0x000000008000040a 0x0081020304003870 0x0040810182001c38

def z17 : W := mkw 0x05850a130c012a54 0x02c285098600952a 0xe481020304023c7f 0x7240810182011e3f

def z18 : W := mkw 0x19ffffe15fffbf77 0x0cfffff0afffdfbb 0xffffffe3ffffffff 0xfffffff1ffffffff

def z19 : W := mkw 0x21ffff5bf20a1817 0x10ffffadf9050c0b 0xbdfffffff002380f 0xdefffffff8011c07

def z20 : W := mkw 0x0022c00002428000 0x0011600001214000 0xd376c0000be3c001 0xe9bb600005f1e000

def z21 : W := mkw 0x05850a130c012a54 0x02c285098600952a 0x0081020304003870 0x0040810182001c38

def z22 : W := mkw 0x05cd0a170c916adc 0x02e6850b8648b56e 0xffff0e1f0fffffff 0xffff870f87ffffff

def z23 : W := mkw 0x000050a0530e1423 0x0000285029870a11 0x0208f1e0f31c0000 0x810478f0798e0000

def z24 : W := mkw 0x05850a160c0162c8 0x02c2850b0600b164 0x09060c1c0801c380 0x0483060e0400e1c0

def z25 : W := mkw 0x000000a001040420 0x0000005000820210 0xe28803e0071c0470 0xf14401f0038e0238

def z26 : W := mkw 0x0232c5acc366c5ab 0x811962d661b362d5 0xfffecffccfffc7ff 0xffff67fe67ffe3ff

def z27 : W := mkw 0x20100f5aa0000000 0x100807ad50000000 0xac89fffff0000001 0xd644fffff8000000

def z28 : W := mkw 0x000050a5530e5cbf 0x00002852a9872e5f 0xef8fffffff1fffff 0xf7c7ffffff8fffff

def z29 : W := mkw 0x15effa130edbba54 0x0af7fd09876ddd2a 0xd3fff2030ffff871 0xe9fff90187fffc38

def z30 : W := mkw 0x000000000c012000 0x0000000006009000 0x400000000c03f800 0x200000000601fc00

def z31 : W := mkw 0x01c80a000c900240 0x00e4050006480120 0xfbf80e000ffc07f0 0xfdfc070007fe03f8

def z32 : W := mkw 0x0000408043020403 0x0000204021810201 0xe600c180c302040f 0xf30060c061810207

def z33 : W := mkw 0x0232850c8060c188 0x81194286403060c4 0x19760c1c08e1c380 0x0cbb060e0470e1c0

def z34 : W := mkw 0x0000000150000817 0x00000000a800040b 0x04000003f000000e 0x02000001f8000007

def z35 : W := mkw 0x09c80a600c940260 0x04e40530064a0130 0x00880260041c0070 0x00440130020e0038

def z36 : W := mkw 0x21ffaf5ea0004088 0x10ffd7af50002044 0xfdfffffff803c78f 0xfefffffffc01e3c7

def z37 : W := mkw 0x020000040060c188 0x81000002003060c4 0x0000000008e1c380 0x000000000470e1c0

def z38 : W := mkw 0x05850a160c0162c8 0x02c2850b0600b164 0xe9860e1c0c01c7f0 0x74c3070e0600e3f8

def z39 : W := mkw 0x19dd3fe00dbd3760 0x0cee9ff006de9bb0 0xfbf93fe00ffc3ff0 0xfdfc9ff007fe1ff8

def z40 : W := mkw 0x07854a974f63efdf 0x83c2a54ba7b1f7ef 0xef870e1f0fe3ffff 0x77c3870f87f1ffff

def z41 : W := mkw 0x04000a1700004adc 0x0200050b8000256e 0x2c000e1f000007fe 0x1600070f800003ff

def z42 : W := mkw 0x106af00002da9000 0x08357800016d4800 0x1278f00003fc0000 0x893c780001fe0000

def z43 : W := mkw 0x127af58cc3fad58b 0x893d7ac661fd6ac5 0xff7efd9ccbffc78f 0xffbf7ece65ffe3c7

def z44 : W := mkw 0x09900fe00d240760 0x04c807f0069203b0 0xe9800fe00c0007f0 0x74c007f0060003f8

def z45 : W := mkw 0x0232d5add36eddbf 0x81196ad6e9b76edf 0xffffffffffffffff 0xffffffffffffffff

def z46 : W := mkw 0x29ffaf5aacb00340 0x14ffd7ad565801a0 0xbdfffffff8e00381 0xdefffffffc7001c0

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0xa489f3e3f0000001 0xd244f9f1f8000000

def z48 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xfffffffffbe3c78f 0xfffffffffdf1e3c7

def z49 : W := mkw 0x20100ffbf1040c37 0x100807fdf882061b 0x2c000ffff000047e 0x160007fff800023f

def z50 : W := mkw 0x25ffaf5bac012a54 0x12ffd7add600952a 0xbdfffffff4003871 0xdefffffffa001c38

def z51 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x1676c19cc3e3c00f 0x8b3b60ce61f1e007

def z52 : W := mkw 0x11effa000edbb240 0x08f7fd00076dd920 0xfbfffe000ffffff1 0xfdffff0007fffff8

def z53 : W := mkw 0x05855ab75f0f7eff 0x02c2ad5baf87bf7f 0xef8fffffff1fffff 0xf7c7ffffff8fffff

def z54 : W := mkw 0x09d85fe15fbe1f77 0x04ec2ff0afdf0fbb 0xfff9ffe3fffe3fff 0xfffcfff1ffff1fff

def z55 : W := mkw 0x1bffffeccffff7eb 0x8dfffff667fffbf5 0xfffffffccfffffff 0xfffffffe67ffffff

def z56 : W := mkw 0x207aa548a0000000 0x103d52a450000000 0xb4f9f3e3f0000001 0xda7cf9f1f8000000

def z57 : W := mkw 0x19ffff400efbb340 0x0cffffa0077dd9a0 0xdbfffc000ffffb81 0xedfffe0007fffdc0

def z58 : W := mkw 0x100050000edbb000 0x08002800076dd800 0x420000000ffff800 0x2100000007fffc00

def z59 : W := mkw 0x0000408043020403 0x0000204021810201 0xe689f3e3f302040f 0xf344f9f1f9810207

def z60 : W := mkw 0x040000050c016adc 0x020000028600b56e 0xed060c1c0c03ffff 0x7683060e0601ffff

def z61 : W := mkw 0x21cd2a5220000000 0x10e6952910000000 0x0089326330000000 0x0044993198000000

def z62 : W := mkw 0x040000170000489c 0x0200000b8000244e 0x0400001f0000000e 0x0200000f80000007

def z63 : W := mkw 0x13fff58ccffbf58b 0x89fffac667fdfac5 0xfffffd9ccfffff8f 0xfffffece67ffffc7

def z64 : W := mkw 0x2027a01aa0000000 0x1013d00d50000000 0x0407f01ff0000001 0x0203f80ff8000000

def z65 : W := mkw 0x29ffaffaadb40760 0x14ffd7fd56da03b0 0xfffffffffffc07f1 0xfffffffffffe03f8

def z66 : W := mkw 0x0232d5acd36ed5ab 0x81196ad669b76ad5 0xff7efdfcfbffc78f 0xffbf7efe7dffe3c7

def z67 : W := mkw 0x31ffff5aaedbb000 0x18ffffad576dd800 0xfffffffffffff801 0xfffffffffffffc00

def z68 : W := mkw 0x0848006000940020 0x04240030004a0010 0x00080060001c0000 0x00040030000e0000

def z69 : W := mkw 0x19d85fe00fffb760 0x0cec2ff007ffdbb0 0xfbf80fe00ffffff0 0xfdfc07f007fffff8

def z70 : W := mkw 0x11eff0211edfb834 0x08f7f8108f6fdc1a 0xd3fff2633ffff871 0xe9fff9319ffffc38

def z71 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x12f803e007fc0070 0x897c01f003fe0038

def z72 : W := mkw 0x05850a130c012a54 0x02c285098600952a 0xe9810e030c003ff0 0x74c0870186001ff8

def z73 : W := mkw 0x00005000020a1000 0x0000280001050800 0xe689f3e3f71e3801 0xf344f9f1fb8f1c00

def z74 : W := mkw 0x07b7cf9ecf63e7cb 0x83dbe7cf67b1f3e5 0xff76cd9ccbe3c78f 0xffbb66ce65f1e3c7

def z75 : W := mkw 0x000000a151040c37 0x00000050a882061b 0x000000000000047e 0x000000000000023f

def z76 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x99fffc1c00000001 0xccfffe0e00000000

def z77 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x19760c1c00000000 0x0cbb060e00000000

def z78 : W := mkw 0x21fffffbf30e1c37 0x10fffffdf9870e1b 0xfffffffff71e3c7f 0xfffffffffb8f1e3f

def z79 : W := mkw 0x25ffaf5fac016adc 0x12ffd7afd600b56e 0xfdf70e1f0c03ffff 0x7efb870f8601ffff

def z80 : W := mkw 0x21ffff5aa20a1000 0x10ffffad51050800 0xfffffffff71e3801 0xfffffffffb8f1c00

def z81 : W := mkw 0x20100f5aa0000000 0x100807ad50000000 0x08000c1c00000000 0x0400060e00000000

def z82 : W := mkw 0x01850a1200000000 0x00c2850900000000 0xad870e1f00000001 0x56c3870f80000000

def z83 : W := mkw 0x207aa548a0000000 0x103d52a450000000 0x1078f1e0f0000000 0x883c78f078000000

def z84 : W := mkw 0x0032c58003628500 0x001962c001b14280 0xfb76cd800be3c781 0xfdbb66c005f1e3c0

def z85 : W := mkw 0x0232858cc120458b 0x811942c6609022c5 0xbd76cd9cc000078f 0xdebb66ce600003c7

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0xa481020300000001 0x5240810180000000

def z87 : W := mkw 0x09d80f400cb00340 0x04ec07a0065801a0 0x19700c0008e00380 0x0cb80600047001c0

def z88 : W := mkw 0x00005001520a1817 0x00002800a9050c0b 0x0401f003f002380f 0x0200f801f8011c07

def z89 : W := mkw 0x00005000020a1000 0x0000280001050800 0xc289f000071e3801 0xe144f800038f1c00

def z90 : W := mkw 0x0210058cc120458b 0x810802c6609022c5 0x2c000d9cc000078e 0x160006ce600003c7

def z91 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x42000000071e3c7e 0x21000000038f1e3f

def z92 : W := mkw 0x20100f5aa0000000 0x100807ad50000000 0x2c000ffff0000000 0x160007fff8000000

def z93 : W := mkw 0x00001021100c1834 0x0000081088060c1a 0x00000000041c3870 0x00000000020e1c38

def z94 : W := mkw 0x2027a01aa0000000 0x1013d00d50000000 0x0006001c00000000 0x0003000e00000000

def z95 : W := mkw 0x0022c00002428000 0x0011600001214000 0x1270c00003e00000 0x8938600001f00000

def z96 : W := mkw 0x2237e59ee362c58b 0x911bf2cf71b162c5 0xff77fd9ffbe3c78f 0xffbbfecffdf1e3c7

def z97 : W := mkw 0x080000a00db40760 0x0400005006da03b0 0x420000000ffc07f0 0x2100000007fe03f8

def z98 : W := mkw 0x040500170001689c 0x0202800b8000b44e 0x0407001f0003f80f 0x0203800f8001fc07

def z99 : W := mkw 0x15effa170edbfadc 0x0af7fd0b876dfd6e 0xfffffe1f0fffffff 0xffffff0f87ffffff

def z100 : W := mkw 0x106af0000edbb000 0x08357800076dd800 0x5278f0000ffff800 0xa93c780007fffc00

def z101 : W := mkw 0x19ffffe00fffb760 0x0cfffff007ffdbb0 0xfbffffe00ffffff1 0xfdfffff007fffff8

def z102 : W := mkw 0x0010058001200500 0x000802c000900280 0xfb700d800be00780 0xfdb806c005f003c0

def z103 : W := mkw 0x01fa8f4880000000 0x00fd47a440000000 0xbdfecffcc0000001 0xdeff67fe60000000

def z104 : W := mkw 0x01cd00000c912000 0x00e6800006489000 0xd3ff00000ffff801 0xe9ff800007fffc00

def z105 : W := mkw 0x0ddd0ff70db56ffc 0x06ee87fb86dab7fe 0xffff0fff0fffffff 0xffff87ff87ffffff

def z106 : W := mkw 0x018500000c012000 0x00c2800006009000 0xc18700000c03f801 0x60c380000601fc00

def z107 : W := mkw 0x207aaf5aa0000000 0x103d57ad50000000 0x3c78fffff0000000 0x9e3c7ffff8000000

def z108 : W := mkw 0x21ffaffbf1040c37 0x10ffd7fdf882061b 0xbdfffffff000047f 0xdefffffff800023f

def z109 : W := mkw 0x207af5e8f30e1423 0x103d7af479870a11 0x1278f1e0f31c0000 0x893c78f0798e0000

def z110 : W := mkw 0x080000200c940260 0x04000010064a0130 0x00000000041c0070 0x00000000020e0038

def z111 : W := mkw 0x21dd2f5aa0000000 0x10ee97ad50000000 0x2c893ffff0000000 0x16449ffff8000000

def z112 : W := mkw 0x11eff0a15fdfbc37 0x08f7f850afefde1b 0xd3fff0000ffffc7f 0xe9fff80007fffe3f

def z113 : W := mkw 0x23ffefdae3628503 0x91fff7ed71b14281 0xbffffffff3e00001 0xdffffffff9f00000

def z114 : W := mkw 0x0bfacfeccff6c7eb 0x85fd67f667fb63f5 0xfffecffccfffc7ff 0xffff67fe67ffe3ff

def z115 : W := mkw 0x11cd70000edbb000 0x08e6b800076dd800 0x428930000ffff800 0x2144980007fffc00

def z116 : W := mkw 0x0010058401204588 0x000802c2009022c4 0xff760d9c0be3c78f 0xffbb06ce05f1e3c7

def z117 : W := mkw 0x021005add1244dbf 0x810802d6e89226df 0x2c000ffff00007fe 0x160007fff80003ff

def z118 : W := mkw 0x15effab75fdffeff 0x0af7fd5bafefff7f 0xffffffffffffffff 0xffffffffffffffff

def z119 : W := mkw 0x09d80f400cb00340 0x04ec07a0065801a0 0xb9f80fe008e00380 0xdcfc07f0047001c0

def z120 : W := mkw 0x000050a0030e1420 0x0000285001870a10 0xe289f3e0071e3c71 0xf144f9f0038f1e38

def z121 : W := mkw 0x09c800a00db40760 0x04e4005006da03b0 0xd3f800000ffc07f0 0xe9fc000007fe03f8

def z122 : W := mkw 0x0dcd0a770c956afc 0x06e6853b864ab57e 0xed8f0e7f0c1fffff 0x76c7873f860fffff

def z123 : W := mkw 0x0a7ac5ecc3f6c5ab 0x853d62f661fb62d5 0xff7ecdfccbffc78f 0xffbf66fe65ffe3c7

def z124 : W := mkw 0x08580fe001b40760 0x042c07f000da03b0 0x3a780fe003fc07f0 0x9d3c07f001fe03f8

def z125 : W := mkw 0x040500170c016adc 0x0202800b8600b56e 0x4407001f0c03ffff 0x2203800f8601ffff

def z126 : W := mkw 0x01efa00000000000 0x00f7d00000000000 0x1176000000000000 0x08bb000000000000

def z127 : W := mkw 0x08100fe001240760 0x040807f0009203b0 0x28000fe0000007f0 0x140007f0000003f8

def z128 : W := mkw 0x1027f000024bb000 0x0813f8000125d800 0x0007f0000003f801 0x0003f8000001fc00

def z129 : W := mkw 0x0000400002020000 0x0000200001010000 0xc200c00003020001 0xe100600001810000

def z130 : W := mkw 0x0032850880000000 0x0019428440000000 0x1070c180c0000000 0x883860c060000000

def z131 : W := mkw 0x0022800000000000 0x0011400000000000 0x9176c00000000001 0xc8bb600000000000

def z132 : W := mkw 0x11fff5088edbb000 0x08fffa84476dd800 0xfffffd9ccffff801 0xfffffece67fffc00

def z133 : W := mkw 0x01c800000c900000 0x00e4000006480000 0xd3f800000ffc0000 0xe9fc000007fe0000

def z134 : W := mkw 0x040000050c016adc 0x020000028600b56e 0x400000000c03fffe 0x200000000601ffff

def z135 : W := mkw 0x01800a000c000240 0x00c0050006000120 0x09000c0008000380 0x04800600040001c0

def z136 : W := mkw 0x25ffaf5fac016adc 0x12ffd7afd600b56e 0xfdfffffffc03ffff 0xfefffffffe01ffff

def z137 : W := mkw 0x287aa5e8a1b40520 0x143d52f450da0290 0x1278f1e0f3fc0000 0x893c78f079fe0000

def z138 : W := mkw 0x000000050000489c 0x000000028000244e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z139 : W := mkw 0x05850a130c012a54 0x02c285098600952a 0xc18702030c03f871 0x60c381018601fc38

def z140 : W := mkw 0x11eff0a15fdfbc37 0x08f7f850afefde1b 0xf7fff3e3fffffc7f 0xfbfff9f1fffffe3f

def z141 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x5b700c000ffc07f0 0x2db8060007fe03f8

def z142 : W := mkw 0x09c80a600c940260 0x04e40530064a0130 0xe9880e600c1c07f0 0x74c40730060e03f8

def z143 : W := mkw 0x0232c588c3628503 0x811962c461b14281 0x1270c180c3e00000 0x893860c061f00000

def z144 : W := mkw 0x0010050000000000 0x0008028000000000 0xb9700d8000000000 0xdcb806c000000000

def z145 : W := mkw 0x11cd30000c993000 0x08e69800064c9800 0x00893000041c3800 0x00449800020e1c00

def z146 : W := mkw 0x29ffaffaa1b40520 0x14ffd7fd50da0290 0xbffffffff3fc0001 0xdffffffff9fe0000

def z147 : W := mkw 0x01d80f4000000000 0x00ec07a000000000 0xb9f80fe000000000 0xdcfc07f000000000

def z148 : W := mkw 0x0032850880000000 0x0019428440000000 0xbdfffffff0000001 0xdefffffff8000000

def z149 : W := mkw 0x000040844302448b 0x0000204221812245 0xef06cd9ccb03c78f 0xf78366ce6581e3c7

def z150 : W := mkw 0x09d80f400cb00340 0x04ec07a0065801a0 0xdbf80c000ffc0380 0xedfc060007fe01c0

def z151 : W := mkw 0x05855ab35f0f3e77 0x02c2ad59af879f3b 0xe689f3e3f71e3c7f 0xf344f9f1fb8f1e3f

def z152 : W := mkw 0x085805e001b40520 0x042c02f000da0290 0x127801e003fc0000 0x893c00f001fe0000

def z153 : W := mkw 0x03b2cf8ccf62c7cb 0x81d967c667b163e5 0xfff6cf9ccfe3c7ff 0xfffb67ce67f1e3ff

def z154 : W := mkw 0x11efb0000cd9b000 0x08f7d800066cd800 0x11ff30000cfdf800 0x08ff9800067efc00

def z155 : W := mkw 0x05851a371c0d7afc 0x02c28d1b8e06bd7e 0xed8f3e7f3c1fffff 0x76c79f3f9e0fffff

def z156 : W := mkw 0x000000a151040c37 0x00000050a882061b 0xe68803e3f71c047e 0xf34401f1fb8e023f

def z157 : W := mkw 0x0232850c8060c188 0x81194286403060c4 0xfd760c1c08e3c78f 0x7ebb060e0471e3c7

def z158 : W := mkw 0x0000000000000000 0x0000000000000000 0x240003e3f0000000 0x120001f1f8000000

def z159 : W := mkw 0x01a7c0000e43a000 0x00d3e0000721d000 0xd3f7c0000fe3f801 0xe9fbe00007f1fc00

def z160 : W := mkw 0x22100fdee120458b 0x910807ef709022c5 0x2c000ffff000078e 0x160007fff80003c7

def z161 : W := mkw 0x11c850000edbb000 0x08e42800076dd800 0xd3f800000ffff800 0xe9fc000007fffc00

def z162 : W := mkw 0x0000000100000814 0x000000008000040a 0x4000000004023c7e 0x2000000002011e3f

def z163 : W := mkw 0x0dcd0a730c952a74 0x06e68539864a953a 0x00890263041c3870 0x00448131820e1c38

def z164 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x49060c1c0c03fffe 0x2483060e0601ffff

def z165 : W := mkw 0x01efa00000000000 0x00f7d00000000000 0x91fff00000000001 0xc8fff80000000000

def z166 : W := mkw 0x21d80f5aa0000000 0x10ec07ad50000000 0xbdf80ffff0000000 0xdefc07fff8000000

def z167 : W := mkw 0x0000000000000000 0x0000000000000000 0xd37000000be00000 0xe9b8000005f00000

def z168 : W := mkw 0x15eff0050edbfadc 0x0af7f802876dfd6e 0xd3fff0000fffffff 0xe9fff80007ffffff

def z169 : W := mkw 0x3027f01aa24bb000 0x1813f80d5125d800 0x0407f01ff003f801 0x0203f80ff801fc00

def z170 : W := mkw 0x21ffefdae3020403 0x10fff7ed71810201 0xfffffffff302040f 0xfffffffff9810207

def z171 : W := mkw 0x08100fe001240760 0x040807f0009203b0 0xfb700fe00be007f0 0xfdb807f005f003f8

def z172 : W := mkw 0x0032850880000000 0x0019428440000000 0xbd76cd9cc0000001 0xdebb66ce60000000

def z173 : W := mkw 0x23ffefdee362c58b 0x91fff7ef71b162c5 0xfffffffffbe3c78f 0xfffffffffdf1e3c7

def z174 : W := mkw 0x106ff00002dbb000 0x0837f800016dd800 0x127ff00003fff801 0x893ff80001fffc00

def z175 : W := mkw 0x040000050001689c 0x020000028000b44e 0x000000000003f80e 0x000000000001fc07

def z176 : W := mkw 0x140050050edbfadc 0x0a002802876dfd6e 0x420000000ffffffe 0x2100000007ffffff

def z177 : W := mkw 0x0000008001000400 0x0000004000800200 0xe200018003000400 0xf10000c001800200

def z178 : W := mkw 0x04050a1700016adc 0x0202850b8000b56e 0x2c070e1f0003ffff 0x1603870f8001ffff

def z179 : W := mkw 0x31ffff5aa24bb000 0x18ffffad5125d800 0xbdfffffff003f801 0xdefffffff801fc00

def z180 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x537600000ffff800 0x29bb000007fffc00

def z181 : W := mkw 0x0000000400004088 0x0000000200002044 0x400000000803c78e 0x200000000401e3c7

def z182 : W := mkw 0x040000040c0162c8 0x020000020600b164 0x000000000801c380 0x000000000400e1c0

def z183 : W := mkw 0x000000a001040420 0x0000005000820210 0x200003e000000470 0x100001f000000238

def z184 : W := mkw 0x11eff0015edbb817 0x08f7f800af6ddc0b 0xd7fff003fffff80f 0xebfff801fffffc07

def z185 : W := mkw 0x04005ab7530e5eff 0x02002d5ba9872f7f 0xee89fffff71e3fff 0xf744fffffb8f1fff

def z186 : W := mkw 0x0032c50882428000 0x0019628441214000 0xff76cd9ccbe3c001 0xffbb66ce65f1e000

def z187 : W := mkw 0x0022c08043428403 0x0011604021a14201 0xf776c180cbe3c40f 0xfbbb60c065f1e207

def z188 : W := mkw 0x0637c59fc363ed9f 0x831be2cfe1b1f6cf 0xff77cd9fcbe3ff8f 0xffbbe6cfe5f1ffc7

def z189 : W := mkw 0x0000100000081000 0x0000080000040800 0x00893000041c3800 0x00449800020e1c00

def z190 : W := mkw 0x2027a01aa0000000 0x1013d00d50000000 0xa48ff3fff0000001 0xd247f9fff8000000

def z191 : W := mkw 0x01800a040c0042c8 0x00c0050206002164 0xed860e1c0c03c7ff 0x76c3070e0601e3ff

def z192 : W := mkw 0x23ffef5ee242c08b 0x91fff7af71216045 0xbdfffffff003c00f 0xdefffffff801e007

def z193 : W := mkw 0x00005080430a1403 0x0000284021850a01 0xe689f180c71e3c0f 0xf344f8c0638f1e07

def z194 : W := mkw 0x05b78f1f8c016adc 0x02dbc78fc600b56e 0xfdf7cf9fcc03ffff 0xfefbe7cfe601ffff

def z195 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x3d760ffff0000000 0x1ebb07fff8000000

def z196 : W := mkw 0x09d85fe15fbe1f77 0x04ec2ff0afdf0fbb 0xfbf80fe00ffe3ffe 0xfdfc07f007ff1fff

def z197 : W := mkw 0x0bfa8f4c8cf0c3c8 0x85fd47a6467861e4 0x19760c1c08e1c380 0x0cbb060e0470e1c0

def z198 : W := mkw 0x11efa0000cd1a000 0x08f7d0000668d000 0xd3fe00000ffdc000 0xe9ff000007fee000

def z199 : W := mkw 0x0000000000000000 0x0000000000000000 0xe40000000002040f 0x7200000000010207

def z200 : W := mkw 0x17ffff9fcffbffdf 0x8bffffcfe7fdffef 0xffffff9fcfffffff 0xffffffcfe7ffffff

def z201 : W := mkw 0x13eff00ccedbf08b 0x89f7f806676df845 0xd7fff01ccffff80f 0xebfff80e67fffc07

def z202 : W := mkw 0x01d80f400c000240 0x00ec07a006000120 0xf9f80fe00c0007f0 0xfcfc07f0060003f8

def z203 : W := mkw 0x09d80fe10db40f74 0x04ec07f086da07ba 0xfff90fe30ffe3fff 0xfffc87f187ff1fff

def z204 : W := mkw 0x100000000cd1a000 0x080000000668d000 0x0000000008e1c000 0x000000000470e000

def z205 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xed8ffffffc03ffff 0xf6c7fffffe01ffff

def z206 : W := mkw 0x080000a001b40520 0x0400005000da0290 0x0200000003fc0000 0x0100000001fe0000

def z207 : W := mkw 0x01eff000020a1000 0x00f7f80001050800 0xd3fff000071e3801 0xe9fff800038f1c00

def z208 : W := mkw 0x01800a000c000240 0x00c0050006000120 0xe9800e000c0007f0 0x74c00700060003f8

def z209 : W := mkw 0x2037af5aa0000000 0x101bd7ad50000000 0x2c07fffff0000001 0x1603fffff8000000

def z210 : W := mkw 0x1027f0a1534fbc37 0x0813f850a9a7de1b 0xe68ff3e3f71ffc7f 0xf347f9f1fb8ffe3f

def z211 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfff9ffe3fffc07f1 0xfffcfff1fffe03f8

def z212 : W := mkw 0x040000050c016adc 0x020000028600b56e 0xe48102030c03ffff 0x724081018601ffff

def z213 : W := mkw 0x01d80fc001200500 0x00ec07e000900280 0xfbf80fe00be00780 0xfdfc07f005f003c0

def z214 : W := mkw 0x04000a1700004adc 0x0200050b8000256e 0xed060e1f0803c7ff 0x7683070f8401e3ff

def z215 : W := mkw 0x0222c00cc242c08b 0x8111600661216045 0xed06cc1cc803c78f 0x7683660e6401e3c7

def z216 : W := mkw 0x0032858881200500 0x001942c440900280 0xff76cd9ccbe00781 0xffbb66ce65f003c0

def z217 : W := mkw 0x000000a151040c37 0x00000050a882061b 0xa489f3e3f000047f 0xd244f9f1f800023f

def z218 : W := mkw 0x15855a170edbfadc 0x0ac2ad0b876dfd6e 0xef870e1f0fffffff 0x77c3870f87ffffff

def z219 : W := mkw 0x0032850880000000 0x0019428440000000 0x19760c1c00000000 0x0cbb060e00000000

def z220 : W := mkw 0x31ffaf5aacd1a000 0x18ffd7ad5668d000 0xbdfffffff8e1c001 0xdefffffffc70e000

def z221 : W := mkw 0x0a7ac5e8c3f68523 0x853d62f461fb4291 0x1278c1e0c3fc0000 0x893c60f061fe0000

def z222 : W := mkw 0x01800a000c000240 0x00c0050006000120 0x0080020004000070 0x0040010002000038

def z223 : W := mkw 0x187af5e003fe9520 0x0c3d7af001ff4a90 0x1278f1e003fc0000 0x893c78f001fe0000

def z224 : W := mkw 0x13fff5addffffdbf 0x89fffad6effffedf 0xffffffffffffffff 0xffffffffffffffff

def z225 : W := mkw 0x00001021100c1834 0x0000081088060c1a 0xa489f3e3f41c3871 0xd244f9f1fa0e1c38

def z226 : W := mkw 0x020040844362c58b 0x8100204221b162c5 0x420000000be3c78e 0x2100000005f1e3c7

def z227 : W := mkw 0x31effa522edbb000 0x18f7fd29176dd800 0xd3fff2633ffff801 0xe9fff9319ffffc00

def z228 : W := mkw 0x080050a15fbe1f77 0x04002850afdf0fbb 0x420000000ffe3ffe 0x2100000007ff1fff

def z229 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x12f9f00007fc3800 0x897cf80003fe1c00

def z230 : W := mkw 0x11a7f0000e4bb000 0x08d3f8000725d800 0xc187f0000c03f801 0x60c3f8000601fc00

def z231 : W := mkw 0x0d950ff70d256ffc 0x06ca87fb8692b7fe 0xed870fff0c03ffff 0x76c387ff8601ffff

def z232 : W := mkw 0x09d85fe00fbe1760 0x04ec2ff007df0bb0 0xfbf9ffe00ffe3ff1 0xfdfcfff007ff1ff8

def z233 : W := mkw 0x0d850ab70db56ffc 0x06c2855b86dab7fe 0xef870e1f0fffffff 0x77c3870f87ffffff

def z234 : W := mkw 0x0022d000024a9000 0x0011680001254800 0xd3fff0000ffff801 0xe9fff80007fffc00

def z235 : W := mkw 0x0010050000200100 0x0008028000100080 0x19700c0008e00380 0x0cb80600047001c0

def z236 : W := mkw 0x31eff01aaedbb000 0x18f7f80d576dd800 0xd7fff01ffffff801 0xebfff80ffffffc00

def z237 : W := mkw 0x19eff0a00fffb760 0x0cf7f85007ffdbb0 0xd3fff0000ffffff1 0xe9fff80007fffff8

def z238 : W := mkw 0x13fff50c8efbf188 0x89fffa86477df8c4 0xdbfffc1c0ffffb81 0xedfffe0e07fffdc0

def z239 : W := mkw 0x29ffaffaadb40760 0x14ffd7fd56da03b0 0xfbfe0ffc0ffc07f0 0xfdff07fe07fe03f8

def z240 : W := mkw 0x11efb0000c993000 0x08f7d800064c9800 0x91fff000041c3801 0xc8fff800020e1c00

def z241 : W := mkw 0x25ffaf5eac0162c8 0x12ffd7af5600b164 0x19760c1c0801c380 0x0cbb060e0400e1c0

def z242 : W := mkw 0x180050a00fffb760 0x0c00285007ffdbb0 0x420000000ffffff0 0x2100000007fffff8

def z243 : W := mkw 0x0000000100000814 0x000000008000040a 0x240002030000047e 0x120001018000023f

def z244 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x197efdfcf0000000 0x8cbf7efe78000000

def z245 : W := mkw 0x01efa00000000000 0x00f7d00000000000 0xb5fff3e3f0000001 0xdafff9f1f8000000

def z246 : W := mkw 0x07b7cf9fcf63efdf 0x83dbe7cfe7b1f7ef 0xfff7cf9fcfe3ffff 0xfffbe7cfe7f1ffff

def z247 : W := mkw 0x05850ab70d056efc 0x02c2855b8682b77e 0xef8f0fff0f1fffff 0xf7c787ff878fffff

def z248 : W := mkw 0x2bffeffeeff6c7eb 0x95fff7ff77fb63f5 0xffffffffffffc7ff 0xffffffffffffe3ff

def z249 : W := mkw 0x1022d0000edbb000 0x08116800076dd800 0xd376c0000ffff801 0xe9bb600007fffc00

def z250 : W := mkw 0x04000a170c016adc 0x0200050b8600b56e 0x6c000e1f0c03fffe 0x3600070f8601ffff

def z251 : W := mkw 0x0bfadfeddffedfff 0x85fd6ff6efff6fff 0xffffffffffffffff 0xffffffffffffffff

def z252 : W := mkw 0x106aa00000d08000 0x0835500000684000 0x1070000000e00000 0x0838000000700000

def z253 : W := mkw 0x05855a170e0b7adc 0x02c2ad0b8705bd6e 0xef8ffe1f0f1fffff 0xf7c7ff0f878fffff

def z254 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x5b760c1c0be3c78e 0x2dbb060e05f1e3c7

def z255 : W := mkw 0x085805e001b40520 0x042c02f000da0290 0xfb780de00bfc0780 0xfdbc06f005fe03c0

def z256 : W := mkw 0x19fff5e00fffb520 0x0cfffaf007ffda90 0xd3fff1e00ffff801 0xe9fff8f007fffc00

def z257 : W := mkw 0x09800aa00db40760 0x04c0055006da03b0 0xeb800e000ffc07f0 0x75c0070007fe03f8

def z258 : W := mkw 0x0000100110081814 0x0000080088040c0a 0x0001300330003800 0x0000980198001c00

def z259 : W := mkw 0x040050a55f0f7eff 0x02002852af87bf7f 0x420000000f1ffffe 0x21000000078fffff

def z260 : W := mkw 0x01c800000c900000 0x00e4000006480000 0x1170000008e00000 0x08b8000004700000

def z261 : W := mkw 0x0000408143020c17 0x00002040a181060b 0xe681c383c7023c7f 0xf340e1c1e3811e3f

def z262 : W := mkw 0x00005081530a1c17 0x00002840a9850e0b 0xe601f183f3023c0f 0xf300f8c1f9811e07

def z263 : W := mkw 0x05850a130c012a54 0x02c285098600952a 0xad870e1f04003871 0x56c3870f82001c38

def z264 : W := mkw 0x0232d5a8d36e9523 0x81196ad469b74a91 0x1278f1e0f3fc0000 0x893c78f079fe0000

def z265 : W := mkw 0x0232c588c3628503 0x811962c461b14281 0xf670c180c3e2040f 0xfb3860c061f10207

def z266 : W := mkw 0x20328f5aa0000000 0x101947ad50000000 0xbd76cffff0000001 0xdebb67fff8000000

def z267 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xf7fff3e3fffff801 0xfbfff9f1fffffc00

def z268 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x408102030c03fffe 0x204081018601ffff

def z269 : W := mkw 0x100050a15fdfbc37 0x08002850afefde1b 0xe689f3e3fffffc7f 0xf344f9f1fffffe3f

def z270 : W := mkw 0x07a7ca1fce43eadf 0x83d3e50fe721f56f 0xed87ce1fcc03ffff 0x76c3e70fe601ffff

def z271 : W := mkw 0x0022c0040242c088 0x0011600201216044 0xff76cc1c0be3c78f 0xffbb660e05f1e3c7

def z272 : W := mkw 0x000000a001040420 0x0000005000820210 0x42000000071c0470 0x21000000038e0238

def z273 : W := mkw 0x0200408043628503 0x8100204021b14281 0x0200000003e00000 0x0100000001f00000

def z274 : W := mkw 0x09d80fe001240760 0x04ec07f0009203b0 0xb9f80fe0000007f0 0xdcfc07f0000003f8

def z275 : W := mkw 0x15cd3a130c993a54 0x0ae69d09864c9d2a 0x00893203041c3870 0x00449901820e1c38

def z276 : W := mkw 0x0000000000000000 0x0000000000000000 0xe9000c0008000780 0x74800600040003c0

def z277 : W := mkw 0x081005a00db40760 0x040802d006da03b0 0xfb700d800ffc07f0 0xfdb806c007fe03f8

def z278 : W := mkw 0x00000a0000000240 0x0000050000000120 0x28000e00000007f0 0x14000700000003f8

def z279 : W := mkw 0x21ffaf5aac000240 0x10ffd7ad56000120 0xfdfffffffc0007f1 0xfefffffffe0003f8

def z280 : W := mkw 0x0000000100000814 0x000000008000040a 0xe489f3e3f4023c7f 0xf244f9f1fa011e3f

def z281 : W := mkw 0x000000a101040c34 0x000000508082061a 0xe68903e3071e3c7f 0xf34481f1838f1e3f

def z282 : W := mkw 0x207af5e9f30e1c37 0x103d7af4f9870e1b 0xf6f9f3e3f71e3c7f 0xfb7cf9f1fb8f1e3f

def z283 : W := mkw 0x2232cfdee362c58b 0x911967ef71b162c5 0xff76cffffbe3c78f 0xffbb67fffdf1e3c7

def z284 : W := mkw 0x21efaa5220000000 0x10f7d52910000000 0x91fff26330000001 0xc8fff93198000000

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z286 : W := mkw 0x20000a5220000000 0x1000052910000000 0x0000026330000000 0x0000013198000000

def z287 : W := mkw 0x0032850c80004088 0x0019428640002044 0xfd76cd9cc803c78f 0xfebb66ce6401e3c7

def z288 : W := mkw 0x0632c58dcf63efdf 0x831962c6e7b1f7ef 0xff76cd9ccfe3ffff 0xffbb66ce67f1ffff

def z289 : W := mkw 0x09d80f600cb40360 0x04ec07b0065a01b0 0x19f80e600cfc03f0 0x0cfc0730067e01f8

def z290 : W := mkw 0x0405001600016088 0x0202800b0000b044 0x0006001c0001c000 0x0003000e0000e000

def z291 : W := mkw 0x02100588c1200503 0x810802c460900281 0x00000180c0000000 0x000000c060000000

def z292 : W := mkw 0x21ffaf5aac012000 0x10ffd7ad56009000 0xfdfffffffc03f801 0xfefffffffe01fc00

def z293 : W := mkw 0x085805e00db40760 0x042c02f006da03b0 0x527801e00ffc07f0 0xa93c00f007fe03f8

def z294 : W := mkw 0x01850a1200000000 0x00c2850900000000 0xad8ffffff0000001 0xd6c7fffff8000000

def z295 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0xe600c180c71e3c7f 0xf30060c0638f1e3f

def z296 : W := mkw 0x04000ab751044eff 0x0200055ba882277f 0x2c000ffff00007fe 0x160007fff80003ff

def z297 : W := mkw 0x00005000020a1000 0x0000280001050800 0x0208f000031c0000 0x81047800018e0000

def z298 : W := mkw 0x227ae5c8e3628503 0x913d72e471b14281 0x1278f1e0f3e00000 0x893c78f079f00000

def z299 : W := mkw 0x25ffaf5eac0162c8 0x12ffd7af5600b164 0xbdfffffff801c381 0xdefffffffc00e1c0

def z300 : W := mkw 0x0000000000000000 0x0000000000000000 0x0401f003f0000001 0x0200f801f8000000

def z301 : W := mkw 0x04000a1300000a54 0x020005098000052a 0x0000020300000070 0x0000010180000038

def z302 : W := mkw 0x0232c50cc262c18b 0x81196286613160c5 0x1d76cc1cc8e3c38f 0x0ebb660e6471e1c7

def z303 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x39700fe008e007f0 0x1cb807f0047003f8

def z304 : W := mkw 0x106af00002da9000 0x08357800016d4800 0xd37ef0000bffc001 0xe9bf780005ffe000

def z305 : W := mkw 0x0c100ff701244ffc 0x060807fb809227fe 0x2c000fff000007fe 0x160007ff800003ff

def z306 : W := mkw 0x118550000edbb000 0x08c2a800076dd800 0xc38700000ffff801 0x61c3800007fffc00

def z307 : W := mkw 0x0405001300012814 0x020280098000940a 0x0001000300003800 0x0000800180001c00

def z308 : W := mkw 0x106af0a153de9c37 0x08357850a9ef4e1b 0xf6f9f3e3f7fe3c7f 0xfb7cf9f1fbff1e3f

def z309 : W := mkw 0x04055017520b789f 0x0202a80ba905bc4f 0x0407f01ff003f80f 0x0203f80ff801fc07

def z310 : W := mkw 0x09d805e00db40520 0x04ec02f006da0290 0xd3f801e00ffc0000 0xe9fc00f007fe0000

def z311 : W := mkw 0x21efa01aa0000000 0x10f7d00d50000000 0x95fff01ff0000001 0xcafff80ff8000000

def z312 : W := mkw 0x25a7aa1fac016adc 0x12d3d50fd600b56e 0xed87fe1ffc03ffff 0x76c3ff0ffe01ffff

def z313 : W := mkw 0x040500170001689c 0x0202800b8000b44e 0xe487021f0403fc7f 0x7243810f8201fe3f

def z314 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x0d070c1f0803fb8f 0x0683860f8401fdc7

def z315 : W := mkw 0x0222c08cc342c48b 0x8111604661a16245 0xe606c19cc303c40f 0xf30360ce6181e207

def z316 : W := mkw 0x11cd30000c993000 0x08e69800064c9800 0xc18f30000c1ff801 0x60c79800060ffc00

def z317 : W := mkw 0x07b78f1e8c61e3c8 0x83dbc78f4630f1e4 0x19760c1c08e1c380 0x0cbb060e0470e1c0

def z318 : W := mkw 0x15a7fa170e4bfadc 0x0ad3fd0b8725fd6e 0xed87fe1f0c03ffff 0x76c3ff0f8601ffff

def z319 : W := mkw 0x05854a974f036edf 0x02c2a54ba781b76f 0xef87cf9fcf03ffff 0xf7c3e7cfe781ffff

def z320 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x1d77fc1ff0000001 0x0ebbfe0ff8000000

def z321 : W := mkw 0x00005001520a1817 0x00002800a9050c0b 0xe481f203f4023c7f 0x7240f901fa011e3f

def z322 : W := mkw 0x11eff0804fdbb403 0x08f7f84027edda01 0xf7fff180cffffc0f 0xfbfff8c067fffe07

def z323 : W := mkw 0x01c850000e9a1000 0x00e42800074d0800 0xd3f9f0000ffe3801 0xe9fcf80007ff1c00

def z324 : W := mkw 0x1027a0000041a000 0x0813d0000020d000 0x000600000001c000 0x000300000000e000

def z325 : W := mkw 0x000010a1110c1c34 0x0000085088860e1a 0xe28933e3371c3c70 0xf14499f19b8e1e38

def z326 : W := mkw 0x21dd2f5220000000 0x10ee97a910000000 0xb9f93fe330000000 0xdcfc9ff198000000

def z327 : W := mkw 0x018550a15f0f3c37 0x00c2a850af879e1b 0xe78ff3e3ff1ffc7f 0xf3c7f9f1ff8ffe3f

def z328 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0xe6810203071e3c7f 0x73408101838f1e3f

def z329 : W := mkw 0x25ffffffff0f7eff 0x12ffffffff87bf7f 0xffffffffff1fffff 0xffffffffff8fffff

def z330 : W := mkw 0x21ffaffaa1040420 0x10ffd7fd50820210 0xfffffffff71c0471 0xfffffffffb8e0238

def z331 : W := mkw 0x09dd0ff20db40760 0x04ee87f906da03b0 0xffff0fff0ffc07f1 0xffff87ff87fe03f8

def z332 : W := mkw 0x020040844362c58b 0x8100204221b162c5 0xe600c180cbe3c78f 0xf30060c065f1e3c7

def z333 : W := mkw 0x31ffaf5aacd1a000 0x18ffd7ad5668d000 0x19760c1c08e1c000 0x0cbb060e0470e000

def z334 : W := mkw 0x00005001520a1817 0x00002800a9050c0b 0x000000000002380e 0x0000000000011c07

def z335 : W := mkw 0x0010058001200500 0x000802c000900280 0x1270018003e00000 0x893800c001f00000

def z336 : W := mkw 0x020040044242c08b 0x8100200221216045 0x000000000003c00e 0x000000000001e007

def z337 : W := mkw 0x05850a1700004adc 0x02c2850b8000256e 0xad870e1f000007ff 0x56c3870f800003ff

def z338 : W := mkw 0x19ffafe00df5a760 0x0cffd7f006fad3b0 0xfbfe0fe00ffdc7f0 0xfdff07f007fee3f8

def z339 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x4601f003f71e3c7f 0x2300f801fb8f1e3f

def z340 : W := mkw 0x23ffefdee362c58b 0x91fff7ef71b162c5 0xff76cd9ccbe3c78f 0xffbb66ce65f1e3c7

def z341 : W := mkw 0x1427f017024bf89c 0x0a13f80b8125fc4e 0x0407f01f0003f80f 0x0203f80f8001fc07

def z342 : W := mkw 0x24100f5fa0004adc 0x120807afd000256e 0x2c000ffff00007fe 0x160007fff80003ff

def z343 : W := mkw 0x29d80ffaadb40760 0x14ec07fd56da03b0 0xfff80ffffffc07f0 0xfffc07fffffe03f8

def z344 : W := mkw 0x00001021100c1834 0x0000081088060c1a 0xe4893263341e3c7f 0x724499319a0f1e3f

def z345 : W := mkw 0x207aa548a0000000 0x103d52a450000000 0xbd7efdfcf0000001 0xdebf7efe78000000

def z346 : W := mkw 0x00001021100c1834 0x0000081088060c1a 0x00893263341c3870 0x004499319a0e1c38

def z347 : W := mkw 0x000000000c000240 0x0000000006000120 0x400000000c0007f0 0x20000000060003f8

def z348 : W := mkw 0x0232d58cc36ad58b 0x81196ac661b56ac5 0xfffffd9ccfffff8f 0xfffffece67ffffc7

def z349 : W := mkw 0x01c800000c900000 0x00e4000006480000 0x00880000041c0000 0x00440000020e0000

def z350 : W := mkw 0x05a7ca170e43eadc 0x02d3e50b8721f56e 0xfff7ce1f0fe3ffff 0xfffbe70f87f1ffff

def z351 : W := mkw 0x0dd80ff70db44ffc 0x06ec07fb86da27fe 0xfff80fff0ffc07fe 0xfffc07ff87fe03ff

def z352 : W := mkw 0x01855ab3530e1c37 0x00c2ad59a9870e1b 0xef8ffffff71e3c7f 0xf7c7fffffb8f1e3f

def z353 : W := mkw 0x11effa120edbb000 0x08f7fd09076dd800 0xfffffe1f0ffff801 0xffffff0f87fffc00

def z354 : W := mkw 0x0210050c80204188 0x81080286401020c4 0x08000c1c00000380 0x0400060e000001c0

def z355 : W := mkw 0x2227e01ee242c08b 0x9113f00f71216045 0x0407f01ff003c00f 0x0203f80ff801e007

def z356 : W := mkw 0x31ffff5aaedbb000 0x18ffffad576dd800 0xdbfffc1c0ffff801 0xedfffe0e07fffc00

def z357 : W := mkw 0x01850a1200000000 0x00c2850900000000 0x0081020300000000 0x0040810180000000

def z358 : W := mkw 0x020000844120458b 0x81000042209022c5 0x000000000000078e 0x00000000000003c7

def z359 : W := mkw 0x19cd3a600c9d3260 0x0ce69d30064e9930 0x00893260041c3870 0x00449930020e1c38

def z360 : W := mkw 0x01d85fe1530e1c37 0x00ec2ff0a9870e1b 0xfff9ffe3f71e3c7f 0xfffcfff1fb8f1e3f

def z361 : W := mkw 0x20105ffbf30e1c37 0x10082ffdf9870e1b 0xee89fffff71e3c7f 0xf744fffffb8f1e3f

def z362 : W := mkw 0x11fff5800ffbb500 0x08fffac007fdda80 0xfbfffd800fffff81 0xfdfffec007ffffc0

def z363 : W := mkw 0x0858054000b00100 0x042c02a000580080 0x1070000000e00000 0x0838000000700000

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0xa08803e000000000 0xd04401f000000000

def z365 : W := mkw 0x2048204020000000 0x1024102010000000 0x0008306030000000 0x0004183018000000

def z366 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x2c810e1f04003ffe 0x1640870f82001fff

def z367 : W := mkw 0x23ffafdee120458b 0x91ffd7ef709022c5 0xbdfffffff000078f 0xdefffffff80003c7

def z368 : W := mkw 0x2027f0bbf30e1c37 0x1013f85df9870e1b 0xe68ff3fff71e3c7f 0xf347f9fffb8f1e3f

def z369 : W := mkw 0x307af548a2da9000 0x183d7aa4516d4800 0x1278f1e0f3fc0000 0x893c78f079fe0000

def z370 : W := mkw 0x000000a001040420 0x0000005000820210 0xe689f3e3f71c0471 0xf344f9f1fb8e0238

def z371 : W := mkw 0x09d81fe11dbc1f74 0x04ec0ff08ede0fba 0xfbf93fe33ffc3ff0 0xfdfc9ff19ffe1ff8

def z372 : W := mkw 0x01900f800d200740 0x00c807c0069003a0 0xfbf00f800fe007f0 0xfdf807c007f003f8

def z373 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x19ff3e7f30000000 0x0cff9f3f98000000

def z374 : W := mkw 0x31ffff5aa2da9000 0x18ffffad516d4800 0xbffffffff3fc0001 0xdffffffff9fe0000

def z375 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x660003e3f71e3c7e 0x330001f1fb8f1e3f

def z376 : W := mkw 0x106af0a053de9423 0x0835785029ef4a11 0x1278f1e0f3fc0000 0x893c78f079fe0000

def z377 : W := mkw 0x11cd70000e9b3000 0x08e6b800074d9800 0xc289f000071e3801 0xe144f800038f1c00

def z378 : W := mkw 0x0000000400004088 0x0000000200002044 0x2c000c1c0000078e 0x1600060e000003c7

def z379 : W := mkw 0x01cd200000000000 0x00e6900000000000 0x0089300000000000 0x0044980000000000

def z380 : W := mkw 0x100010000c993000 0x08000800064c9800 0x00000000041c3800 0x00000000020e1c00

def z381 : W := mkw 0x29faafe8adb40760 0x14fd57f456da03b0 0xfbf8ffe0fffc07f0 0xfdfc7ff07ffe03f8

def z382 : W := mkw 0x1027f000024bb000 0x0813f8000125d800 0xd377f0000be3f801 0xe9bbf80005f1fc00

def z383 : W := mkw 0x1027f0000edbb000 0x0813f800076dd800 0x4207f0000ffff801 0x2103f80007fffc00

def z384 : W := mkw 0x0005001200000000 0x0002800900000000 0x0407001f00000001 0x0203800f80000000

def z385 : W := mkw 0x0ddd0f570cb16bdc 0x06ee87ab8658b5ee 0xfdf70e1f0ce3ffff 0x7efb870f8671ffff

def z386 : W := mkw 0x0232c588c3628503 0x811962c461b14281 0xfb70cd80cbe00780 0xfdb866c065f003c0

def z387 : W := mkw 0x0232858c8160c588 0x811942c640b062c4 0xfb760d9c0be1c780 0xfdbb06ce05f0e3c0

def z388 : W := mkw 0x0222c08cc362c58b 0x8111604661b162c5 0x4606c01ccbe3c78f 0x2303600e65f1e3c7

def z389 : W := mkw 0x28100ffaa1240760 0x140807fd509203b0 0x2c000ffff00007f0 0x160007fff80003f8

def z390 : W := mkw 0x09ffafe00db40760 0x04ffd7f006da03b0 0xfbffffe00ffc07f1 0xfdfffff007fe03f8

def z391 : W := mkw 0x0232c58dc362cd9f 0x811962c6e1b166cf 0xfff7cf9fcfe3ffff 0xfffbe7cfe7f1ffff

def z392 : W := mkw 0x0022d0a1534e9c37 0x00116850a9a74e1b 0xf7fff3e3fffffc7f 0xfbfff9f1fffffe3f

def z393 : W := mkw 0x21cd2a5220000000 0x10e6952910000000 0xad8f3e7f30000001 0x56c79f3f98000000

def z394 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x1b76cd9ccbe1c380 0x8dbb66ce65f0e1c0

def z395 : W := mkw 0x05850a160c0162c8 0x02c2850b0600b164 0xc9870c1c0c03fb81 0x64c3860e0601fdc0

def z396 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x0487021f0403f87f 0x0243810f8201fc3f

def z397 : W := mkw 0x080000a00db40760 0x0400005006da03b0 0xe28803e00ffc07f0 0xf14401f007fe03f8

def z398 : W := mkw 0x29ffaf7aac940260 0x14ffd7bd564a0130 0xbdfffffff41c0071 0xdefffffffa0e0038

def z399 : W := mkw 0x11eff00002da9000 0x08f7f800016d4800 0x93fff00003fc0001 0xc9fff80001fe0000

def z400 : W := mkw 0x1232d58ccffbf58b 0x89196ac667fdfac5 0xff76cd9ccfffff8f 0xffbb66ce67ffffc7

def z401 : W := mkw 0x100050000edbb000 0x08002800076dd800 0xc289f0000ffff801 0xe144f80007fffc00

def z402 : W := mkw 0x020040844362c58b 0x8100204221b162c5 0xef060c1c0be3c78f 0x7783060e05f1e3c7

def z403 : W := mkw 0x0210458cc362c58b 0x810822c661b162c5 0x6e000d9ccbe3c78e 0x370006ce65f1e3c7

def z404 : W := mkw 0x09d80f400cb00340 0x04ec07a0065801a0 0xf9f00e000ce007f0 0x7cf80700067003f8

def z405 : W := mkw 0x09c81a611c9c1a74 0x04e40d308e4e0d3a 0x00893263341c3870 0x004499319a0e1c38

def z406 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xbd76cd9cc0000001 0xdebb66ce60000000

def z407 : W := mkw 0x0a32cfecc366c7eb 0x851967f661b363f5 0xff76cffccbe3c7ff 0xffbb67fe65f1e3ff

def z408 : W := mkw 0x31fffffbffdfbc37 0x18fffffdffefde1b 0xfffffffffffffc7f 0xfffffffffffffe3f

def z409 : W := mkw 0x1237f58cc36bf58b 0x891bfac661b5fac5 0xff77fd9ccbe3ff8f 0xffbbfece65f1ffc7

def z410 : W := mkw 0x0000008041000403 0x0000004020800201 0x24000180c000040e 0x120000c060000207

def z411 : W := mkw 0x085855e053be1523 0x042c2af029df0a91 0x1278f1e0f3fc0000 0x893c78f079fe0000

def z412 : W := mkw 0x018500010c012814 0x00c280008600940a 0xe58702030c03fc7f 0x72c381018601fe3f

def z413 : W := mkw 0x07950f9fcd216fdf 0x83ca87cfe690b7ef 0xed870f9fcc03ffff 0x76c387cfe601ffff

def z414 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x2c06cd9cc003c78f 0x160366ce6001e3c7

def z415 : W := mkw 0x080000a001240760 0x04000050009203b0 0x00000000000007f0 0x00000000000003f8

def z416 : W := mkw 0x001005a001240520 0x000802d000920290 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z417 : W := mkw 0x13eff0844ffbf58b 0x89f7f84227fdfac5 0xd3fff0000fffff8f 0xe9fff80007ffffc7

def z418 : W := mkw 0x25cd2a572c016adc 0x12e6952b9600b56e 0xed8f3e7f3c03ffff 0x76c79f3f9e01ffff

def z419 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x09870e1f0c01fbf0 0x04c3870f8600fdf8

def z420 : W := mkw 0x0bfa8fec8df4c7e8 0x85fd47f646fa63f4 0xfbfe0ffc0ffdc7f0 0xfdff07fe07fee3f8

def z421 : W := mkw 0x11eff0a05fdfb423 0x08f7f8502fefda11 0xd3fff1e0fffff801 0xe9fff8f07ffffc00

def z422 : W := mkw 0x120050844ffbf58b 0x8900284227fdfac5 0x420000000fffff8e 0x2100000007ffffc7

def z423 : W := mkw 0x0210058cc120458b 0x810802c6609022c5 0xed060d9cc803c78f 0x768306ce6401e3c7

def z424 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x2401f3e3f0023c7f 0x1200f9f1f8011e3f

def z425 : W := mkw 0x01850a120c000240 0x00c2850906000120 0xed870e1f0c0007f1 0x76c3870f860003f8

def z426 : W := mkw 0x020050a5536eddbf 0x81002852a9b76edf 0x420000000ffffffe 0x2100000007ffffff

def z427 : W := mkw 0x0232d5a9d36e9d37 0x81196ad4e9b74e9b 0xf6f9f3e3f7fe3c7f 0xfb7cf9f1fbff1e3f

def z428 : W := mkw 0x0200000cc000408b 0x8100000660002045 0x0400001cc000000e 0x0200000e60000007

def z429 : W := mkw 0x21cd2a5220000000 0x10e6952910000000 0x0000000000000000 0x0000000000000000

def z430 : W := mkw 0x21ffa548a0000000 0x10ffd2a450000000 0x91fff1e0f0000001 0xc8fff8f078000000

def z431 : W := mkw 0x0000000000000000 0x0000000000000000 0xc2880000071c0000 0xe1440000038e0000

def z432 : W := mkw 0x01850a1300000814 0x00c285098000040a 0xed870e1f04023c7f 0x76c3870f82011e3f

def z433 : W := mkw 0x07b78f1f8c61ebdc 0x83dbc78fc630f5ee 0xfdf70e1f0ce3ffff 0x7efb870f8671ffff

def z434 : W := mkw 0x09d80fe40db447e8 0x04ec07f206da23f4 0xfffe0ffc0fffc7ff 0xffff07fe07ffe3ff

def z435 : W := mkw 0x0000002000040020 0x0000001000020010 0x00880260041c0070 0x00440130020e0038

def z436 : W := mkw 0x106af00002da9000 0x08357800016d4800 0xd2f9f00007fe3801 0xe97cf80003ff1c00

def z437 : W := mkw 0x0232858cc160c58b 0x811942c660b062c5 0x3d760d9cc8e1c78e 0x1ebb06ce6470e3c7

def z438 : W := mkw 0x00005021120e1834 0x0000281089070c1a 0xc289f263371e3871 0xe144f9319b8f1c38

def z439 : W := mkw 0x080000000cb00340 0x04000000065801a0 0x0000000008e00380 0x00000000047001c0

def z440 : W := mkw 0x0032c588c3020403 0x001962c461810201 0xff76cd9cc302040f 0xffbb66ce61810207

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0xc10600000803c001 0x608300000401e000

def z442 : W := mkw 0x09c80ae00db40760 0x04e4057006da03b0 0x428802600ffc07f0 0x2144013007fe03f8

def z443 : W := mkw 0x01d80fe001040420 0x00ec07f000820210 0xfbf80fe0071c0470 0xfdfc07f0038e0238

def z444 : W := mkw 0x03fac58ccff2c58b 0x81fd62c667f962c5 0xfffecd9ccfffc78f 0xffff66ce67ffe3c7

def z445 : W := mkw 0x09c80a600c940260 0x04e40530064a0130 0xd3f802600ffc0070 0xe9fc013007fe0038

def z446 : W := mkw 0x01850a120c012000 0x00c2850906009000 0xed870e1f0c03f801 0x76c3870f8601fc00

def z447 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xb9fe0ffc00000000 0xdcff07fe00000000

def z448 : W := mkw 0x0ddd0ff30db52f74 0x06ee87f986da97ba 0xfbf90fe30ffc3ff0 0xfdfc87f187fe1ff8

def z449 : W := mkw 0x23ffaf5ea060c188 0x91ffd7af503060c4 0x19760c1c08e1c380 0x0cbb060e0470e1c0

def z450 : W := mkw 0x080050a15fbe1f77 0x04002850afdf0fbb 0xe689f3e3fffe3fff 0xf344f9f1ffff1fff

def z451 : W := mkw 0x0ddd0f560cb163c8 0x06ee87ab0658b1e4 0x19760c1c08e1c380 0x0cbb060e0470e1c0

def z452 : W := mkw 0x0010458043220503 0x000822c021910281 0xff70cd80cbe2078f 0xffb866c065f103c7

def z453 : W := mkw 0x01efaa1200000000 0x00f7d50900000000 0xbdfffe1f00000001 0xdeffff0f80000000

def z454 : W := mkw 0x040050a55f0f7eff 0x02002852af87bf7f 0xe689f3e3ff1fffff 0xf344f9f1ff8fffff

def z455 : W := mkw 0x1022f000024a9000 0x0811780001254800 0x0000f00000000000 0x0000780000000000

def z456 : W := mkw 0x21faaf48a0000000 0x10fd57a450000000 0xb9f8ffe0f0000000 0xdcfc7ff078000000

def z457 : W := mkw 0x0000408043020403 0x0000204021810201 0x420000000302040e 0x2100000001810207

def z458 : W := mkw 0x1005300000093000 0x0802980000049800 0x0001300000003800 0x0000980000001c00

def z459 : W := mkw 0x21950f5aa0000000 0x10ca87ad50000000 0xad870ffff0000001 0x56c387fff8000000

def z460 : W := mkw 0x21ffaf5aac900000 0x10ffd7ad56480000 0xfffffffffffc0001 0xfffffffffffe0000

def z461 : W := mkw 0x2000001aa0000000 0x1000000d50000000 0x0400001ff0000000 0x0200000ff8000000

def z462 : W := mkw 0x31cd3a522c993000 0x18e69d29164c9800 0x00893263341c3800 0x004499319a0e1c00

def z463 : W := mkw 0x00005000020a1000 0x0000280001050800 0x42000000071e3800 0x21000000038f1c00

def z464 : W := mkw 0x0010058001200500 0x000802c000900280 0x28000d8000000780 0x140006c0000003c0

def z465 : W := mkw 0x33ffffdeeffbf58b 0x99ffffef77fdfac5 0xffffffffffffff8f 0xffffffffffffffc7

def z466 : W := mkw 0x085805e001b40520 0x042c02f000da0290 0xf2f803e007fc0470 0xf97c01f003fe0238

def z467 : W := mkw 0x05850a170001689c 0x02c2850b8000b44e 0xad870e1f0003f80f 0x56c3870f8001fc07

def z468 : W := mkw 0x09fa8fe88db40760 0x04fd47f446da03b0 0xfffecffccffc07f1 0xffff67fe67fe03f8

def z469 : W := mkw 0x0048000000900000 0x0024000000480000 0x1278000003fc0000 0x893c000001fe0000

def z470 : W := mkw 0x0032d5a9d30e1c37 0x00196ad4e9870e1b 0xfffffffff71e3c7f 0xfffffffffb8f1e3f

def z471 : W := mkw 0x07b7dfbfdf6fffff 0x83dbefdfefb7ffff 0xffffffffffffffff 0xffffffffffffffff

def z472 : W := mkw 0x0000000000000000 0x0000000000000000 0x8089f00000000001 0xc044f80000000000

def z473 : W := mkw 0x0232850c8060c188 0x81194286403060c4 0xbd76cd9cc8e1c381 0xdebb66ce6470e1c0

def z474 : W := mkw 0x13fff588cffbb503 0x89fffac467fdda81 0xd3fff180cffff801 0xe9fff8c067fffc00

def z475 : W := mkw 0x08100fe001240760 0x040807f0009203b0 0xea880fe0071c07f0 0xf54407f0038e03f8

def z476 : W := mkw 0x0dd80fe50db56ffc 0x06ec07f286dab7fe 0xfbf80fe00ffffffe 0xfdfc07f007ffffff

def z477 : W := mkw 0x0a100fecc12447eb 0x850807f6609223f5 0x2c000ffcc00007fe 0x160007fe600003ff

def z478 : W := mkw 0x01850a1600004088 0x00c2850b00002044 0xed870e1f0803c78f 0x76c3870f8401e3c7

def z479 : W := mkw 0x0185000000000000 0x00c2800000000000 0x8187000000000001 0x40c3800000000000

def z480 : W := mkw 0x0027a00000000000 0x0013d00000000000 0x0007f00000000001 0x0003f80000000000

def z481 : W := mkw 0x09d84fe04fb60763 0x04ec27f027db03b1 0xfff8cfe0cffe07ff 0xfffc67f067ff03ff

def z482 : W := mkw 0x05950f970d216fdc 0x02ca87cb8690b7ee 0xfff70f9f0fe3ffff 0xfffb87cf87f1ffff

def z483 : W := mkw 0x21ffef5aa2428000 0x10fff7ad51214000 0xfffffffffbe3c001 0xfffffffffdf1e000

def z484 : W := mkw 0x00100f4000000000 0x000807a000000000 0x28000fe000000000 0x140007f000000000

def z485 : W := mkw 0x0000002110040834 0x000000108802041a 0x0000026330000070 0x0000013198000038

def z486 : W := mkw 0x001055a1532e1d37 0x00082ad0a9970e9b 0xfff9ffe3fffe3fff 0xfffcfff1ffff1fff

def z487 : W := mkw 0x0bfacfcccff2c7cb 0x85fd67e667f963e5 0xff76cd9ccbe3c78f 0xffbb66ce65f1e3c7

def z488 : W := mkw 0x0fffcfffcff7efff 0x87ffe7ffe7fbf7ff 0xffffcfffcfffffff 0xffffe7ffe7ffffff

def z489 : W := mkw 0x03b7cf9ec362c58b 0x81dbe7cf61b162c5 0xfff7cf9fcbe3c78f 0xfffbe7cfe5f1e3c7

def z490 : W := mkw 0x00005001520a1817 0x00002800a9050c0b 0xc689f003f71e380f 0xe344f801fb8f1c07

def z491 : W := mkw 0x100050a15fdfbc37 0x08002850afefde1b 0x420000000ffffc7e 0x2100000007fffe3f

def z492 : W := mkw 0x207fa55aa0000000 0x103fd2ad50000000 0x147ff1fff0000001 0x8a3ff8fff8000000

def z493 : W := mkw 0x01efa0000c900000 0x00f7d00006480000 0xd3fff0000ffc0001 0xe9fff80007fe0000

def z494 : W := mkw 0x25950f5fac016adc 0x12ca87afd600b56e 0xed870ffffc03ffff 0x76c387fffe01ffff

def z495 : W := mkw 0x01800aa00d040660 0x00c0055006820330 0xeb880fe00f1c07f0 0xf5c407f0078e03f8

def z496 : W := mkw 0x11eaf0000eda9000 0x08f57800076d4800 0xd3f8f0000ffc0000 0xe9fc780007fe0000

def z497 : W := mkw 0x21fffffaf30e1423 0x10fffffd79870a11 0xbffffffff31c0001 0xdffffffff98e0000

def z498 : W := mkw 0x0222d0add34edcbf 0x81116856e9a76e5f 0xe68ff3fff71ffc7f 0xf347f9fffb8ffe3f

def z499 : W := mkw 0x11cd30000c993000 0x08e69800064c9800 0xd3f930000ffc3800 0xe9fc980007fe1c00

def z500 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x1b780de00bfc0380 0x8dbc06f005fe01c0

def z501 : W := mkw 0x0ddd5ff75fbf7fff 0x06eeaffbafdfbfff 0xffffffffffffffff 0xffffffffffffffff

def z502 : W := mkw 0x0005000000012000 0x0002800000009000 0x000700000003f801 0x000380000001fc00

def z503 : W := mkw 0x058500050c016adc 0x02c280028600b56e 0xc18700000c03ffff 0x60c380000601ffff

def z504 : W := mkw 0x0000408043020403 0x0000204021810201 0x0200c180c3000000 0x810060c061800000

def z505 : W := mkw 0x05851a331c0d3a74 0x02c28d198e069d3a 0x00893263341c3870 0x004499319a0e1c38

def z506 : W := mkw 0x1027f000024bb000 0x0813f8000125d800 0xc28ff000071ff801 0xe147f800038ffc00

def z507 : W := mkw 0x01800a0000000000 0x00c0050000000000 0xa9800e0000000000 0x54c0070000000000

def z508 : W := mkw 0x01c850a15f9e1c37 0x00e42850afcf0e1b 0xf7f9f3e3fffe3c7f 0xfbfcf9f1ffff1e3f

def z509 : W := mkw 0x018500000c012000 0x00c2800006009000 0x010600000801c000 0x008300000400e000

def z510 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x1177f00008e3f801 0x08bbf8000471fc00

def z511 : W := mkw 0x29ffaf5aacb00340 0x14ffd7ad565801a0 0x19760c1c08e00380 0x0cbb060e047001c0

def z512 : W := mkw 0x0a32c5accff6c7eb 0x851962d667fb63f5 0xff76cd9ccfffc7ff 0xffbb66ce67ffe3ff

def z513 : W := mkw 0x09d80fe001b40520 0x04ec07f000da0290 0xbbf80fe003fc0000 0xddfc07f001fe0000

def z514 : W := mkw 0x08100fe00db40760 0x040807f006da03b0 0x6a000fe00ffc07f0 0x350007f007fe03f8

def z515 : W := mkw 0x018500000c012000 0x00c2800006009000 0x0081000004003800 0x0040800002001c00

def z516 : W := mkw 0x15efaa160cd1e2c8 0x0af7d50b0668f164 0x19760c1c08e1c380 0x0cbb060e0470e1c0

def z517 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0xc289f000071e3c7f 0xe144f800038f1e3f

def z518 : W := mkw 0x020050a5536eddbf 0x81002852a9b76edf 0xe689f3e3ffffffff 0xf344f9f1ffffffff

def z519 : W := mkw 0x21ffaf5ba0000814 0x10ffd7add000040a 0xfdfffffff4023c7f 0xfefffffffa011e3f

def z520 : W := mkw 0x01c80a4000000000 0x00e4052000000000 0x0088026000000000 0x0044013000000000

def z521 : W := mkw 0x25ffaf5fa0004adc 0x12ffd7afd000256e 0xbdfffffff00007ff 0xdefffffff80003ff

def z522 : W := mkw 0x31fff548aedbb000 0x18fffaa4576dd800 0xd3fff1e0fffff801 0xe9fff8f07ffffc00

def z523 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xbdf70e1f00000001 0x5efb870f80000000

def z524 : W := mkw 0x0000400042020003 0x0000200021010001 0x0400c000c002000f 0x0200600060010007

def z525 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008f1e0f0000000 0x800478f078000000

def z526 : W := mkw 0x0022800880000000 0x0011400440000000 0x0406c01cc0000001 0x0203600e60000000

def z527 : W := mkw 0x0bd80feccdb447eb 0x85ec07f666da23f5 0xfff80ffccffc07fe 0xfffc07fe67fe03ff

def z528 : W := mkw 0x1000500002da9000 0x08002800016d4800 0x0200000003fc0000 0x0100000001fe0000

def z529 : W := mkw 0x000000a001040420 0x0000005000820210 0x020801e0031c0000 0x810400f0018e0000

def z530 : W := mkw 0x08100f4000200340 0x040807a0001001a0 0x08000c0000000380 0x04000600000001c0

def z531 : W := mkw 0x11eff0040edbf088 0x08f7f802076df844 0xfffffc1c0fffff8f 0xfffffe0e07ffffc7

def z532 : W := mkw 0x085855e153be1d37 0x042c2af0a9df0e9b 0xf6f9f3e3f7fe3c7f 0xfb7cf9f1fbff1e3f

def z533 : W := mkw 0x23fffffff36eddbf 0x91fffffff9b76edf 0xffffffffffffffff 0xffffffffffffffff

def z534 : W := mkw 0x09dd0fe00db52760 0x04ee87f006da93b0 0xfbff0fe00ffffff1 0xfdff87f007fffff8

def z535 : W := mkw 0x04000a16000042c8 0x0200050b00002164 0x08000c1c00000380 0x0400060e000001c0

def z536 : W := mkw 0x01850a1200000000 0x00c2850900000000 0x09060c1c00000000 0x0483060e00000000

def z537 : W := mkw 0x25ffaf5fa001689c 0x12ffd7afd000b44e 0xbdfffffff003f80f 0xdefffffff801fc07

def z538 : W := mkw 0x1048300000981000 0x08241800004c0800 0x00083000001c0000 0x00041800000e0000

def z539 : W := mkw 0x09facfe00ff68760 0x04fd67f007fb43b0 0xfbfecfe00fffc7f1 0xfdff67f007ffe3f8

def z540 : W := mkw 0x0010050880000000 0x0008028440000000 0x2c000d9cc0000000 0x160006ce60000000

def z541 : W := mkw 0x05800a170c004adc 0x02c0050b8600256e 0xed800e1f0c0007fe 0x76c0070f860003ff

def z542 : W := mkw 0x0222d00dd24ad89f 0x81116806e9256c4f 0x0407f01ff003f80f 0x0203f80ff801fc07

def z543 : W := mkw 0x000010a1510c1c37 0x00000850a8860e1b 0x248933e3f41c3c7e 0x124499f1fa0e1e3f

def z544 : W := mkw 0x01850a000c012240 0x00c2850006009120 0xe9870e000c03fff1 0x74c387000601fff8

def z545 : W := mkw 0x08105fe1532e1f77 0x04082ff0a9970fbb 0xee89ffe3f71e3fff 0xf744fff1fb8f1fff

def z546 : W := mkw 0x11cd30211c9d3834 0x08e698108e4e9c1a 0x00893263341c3870 0x004499319a0e1c38

def z547 : W := mkw 0x0000000400004088 0x0000000200002044 0x0406001c0003c00f 0x0203000e0001e007

def z548 : W := mkw 0x01d80f4000000000 0x00ec07a000000000 0x19700c0000000000 0x0cb8060000000000

def z549 : W := mkw 0x0232c588c3628503 0x811962c461b14281 0xd376c180cbe3c001 0xe9bb60c065f1e000

def z550 : W := mkw 0x0232c50cc242c08b 0x8119628661216045 0xbd76cd9cc003c00f 0xdebb66ce6001e007

def z551 : W := mkw 0x11efe0000ed3a000 0x08f7f0000769d000 0xd376c0000be3c001 0xe9bb600005f1e000

def z552 : W := mkw 0x15cd3a170c997adc 0x0ae69d0b864cbd6e 0xed8f3e1f0c1fffff 0x76c79f0f860fffff

def z553 : W := mkw 0x040550b7530f7cbf 0x0202a85ba987be5f 0xe68ff3fff71ffc7f 0xf347f9fffb8ffe3f

def z554 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x3e70cd9cc3e0078e 0x9f3866ce61f003c7

def z555 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0xe28803e0071e3c7e 0xf14401f0038f1e3f

def z556 : W := mkw 0x04000a1700004adc 0x0200050b8000256e 0xec810e1f04023fff 0x7640870f82011fff

def z557 : W := mkw 0x05dd0f570c016adc 0x02ee87ab8600b56e 0xfdff0fff0c03ffff 0xfeff87ff8601ffff

def z558 : W := mkw 0x000000a151040c37 0x00000050a882061b 0xe48103e3f4023c7f 0x724081f1fa011e3f

def z559 : W := mkw 0x0000000000000000 0x0000000000000000 0x0089326330000000 0x0044993198000000

def z560 : W := mkw 0x25cd2a532c012a54 0x12e695299600952a 0x0089326334003870 0x004499319a001c38

def z561 : W := mkw 0x01eff0a1530e1c37 0x00f7f850a9870e1b 0xf7fff3e3f71e3c7f 0xfbfff9f1fb8f1e3f

def z562 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x4208f1e0f71e3c7e 0xa10478f07b8f1e3f

def z563 : W := mkw 0x0210058cc120458b 0x810802c6609022c5 0xff700d9ccbe0078e 0xffb806ce65f003c7

def z564 : W := mkw 0x27ffefdfef63efdf 0x93fff7eff7b1f7ef 0xffffffffffe3ffff 0xfffffffffff1ffff

def z565 : W := mkw 0x0232d58dd36add9f 0x81196ac6e9b56ecf 0xff77fd9ffbe3ff8f 0xffbbfecffdf1ffc7

def z566 : W := mkw 0x01805aa15f0e1e77 0x00c02d50af870f3b 0xef89ffe3ff1e3fff 0xf7c4fff1ff8f1fff

def z567 : W := mkw 0x11ffff400edbb000 0x08ffffa0076dd800 0xfbffffe00ffff801 0xfdfffff007fffc00

def z568 : W := mkw 0x0210458cc322458b 0x810822c6619122c5 0xee00cd9cc302078f 0xf70066ce618103c7

def z569 : W := mkw 0x01b78f1a80000000 0x00dbc78d40000000 0xbdf7cf9fc0000001 0xdefbe7cfe0000000

def z570 : W := mkw 0x00005000520a1003 0x0000280029050801 0x0000f000f0000000 0x0000780078000000

def z571 : W := mkw 0x040000010c012a54 0x020000008600952a 0x0000000004003870 0x0000000002001c38

def z572 : W := mkw 0x29dd2ff22db40760 0x14ee97f916da03b0 0xfbf93fe33ffc07f0 0xfdfc9ff19ffe03f8

def z573 : W := mkw 0x0632cf9fc362cfdf 0x831967cfe1b167ef 0xff76cf9fcbe3c7ff 0xffbb67cfe5f1e3ff

def z574 : W := mkw 0x29ffaffaa1240760 0x14ffd7fd509203b0 0xbdfffffff00007f1 0xdefffffff80003f8

def z575 : W := mkw 0x03facfccc362c58b 0x81fd67e661b162c5 0xfffecffccbe3c78f 0xffff67fe65f1e3c7

def z576 : W := mkw 0x000050a0530e1423 0x0000285029870a11 0x02000000031c0000 0x01000000018e0000

def z577 : W := mkw 0x000000000c900000 0x0000000006480000 0x420000000ffc0000 0x2100000007fe0000

def z578 : W := mkw 0x018550000e0b3000 0x00c2a80007059800 0xc38ff0000f1ff801 0xe1c7f800078ffc00

def z579 : W := mkw 0x058500170c01689c 0x02c2800b8600b44e 0xc587001f0c03f80f 0x62c3800f8601fc07

def z580 : W := mkw 0x0022800000408000 0x0011400000204000 0x1176000008e1c000 0x08bb00000470e000

def z581 : W := mkw 0x1dfffff70ffffffc 0x0efffffb87fffffe 0xffffffff0fffffff 0xffffffff87ffffff

def z582 : W := mkw 0x2037a51aa0000000 0x101bd28d50000000 0xbd77fd9ff0000001 0xdebbfecff8000000

def z583 : W := mkw 0x00005001520a1817 0x00002800a9050c0b 0xa489f3e3f002380f 0xd244f9f1f8011c07

def z584 : W := mkw 0x2dffafffadb56ffc 0x16ffd7ffd6dab7fe 0xffffffffffffffff 0xffffffffffffffff

def z585 : W := mkw 0x2022a008a0000000 0x1011500450000000 0x0000f000f0000000 0x0000780078000000

def z586 : W := mkw 0x0232d5add36eddbf 0x81196ad6e9b76edf 0xff76cd9ccfffffff 0xffbb66ce67ffffff

def z587 : W := mkw 0x20100548a0000000 0x100802a450000000 0x000001e0f0000000 0x000000f078000000

def z588 : W := mkw 0x0022c00002428000 0x0011600001214000 0x0006c0000003c001 0x000360000001e000

def z589 : W := mkw 0x01ffa50880000000 0x00ffd28440000000 0xbdfffd9cc0000001 0xdefffece60000000

def z590 : W := mkw 0x0bd84fe44ff6c7eb 0x85ec27f227fb63f5 0xfbf80fe00fffc7fe 0xfdfc07f007ffe3ff

def z591 : W := mkw 0x0c0000a50db56ffc 0x0600005286dab7fe 0x420000000ffffffe 0x2100000007ffffff

def z592 : W := mkw 0x00001020100c1020 0x0000081008060810 0x00083060301c0000 0x00041830180e0000

def z593 : W := mkw 0x29fffffbffbe1f77 0x14fffffdffdf0fbb 0xfffffffffffe3fff 0xffffffffffff1fff

def z594 : W := mkw 0x000050a0530e1423 0x0000285029870a11 0xe608f1e0f31e040f 0xf30478f0798f0207

def z595 : W := mkw 0x000040a043060423 0x0000205021830211 0xe688c3e0c71e047f 0xf34461f0638f023f

def z596 : W := mkw 0x227ae5cce362c58b 0x913d72e671b162c5 0xff7efdfcfbe3c78f 0xffbf7efe7df1e3c7

def z597 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x28880fe0041c07f0 0x144407f0020e03f8

def z598 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x42893263371e3c7e 0x214499319b8f1e3f

def z599 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x0609f1e3f31e380f 0x8304f8f1f98f1c07

def z600 : W := mkw 0x01dd0f5200000000 0x00ee87a900000000 0xbdff0fff00000001 0xdeff87ff80000000

def z601 : W := mkw 0x1027f001524bb817 0x0813f800a925dc0b 0x0407f003f003f80f 0x0203f801f801fc07

def z602 : W := mkw 0x09d80f600c940260 0x04ec07b0064a0130 0xb9f80fe0041c0070 0xdcfc07f0020e0038

def z603 : W := mkw 0x05850a160c0162c8 0x02c2850b0600b164 0xed060c1c0803c78f 0x7683060e0401e3c7

def z604 : W := mkw 0x09c80ae00d940660 0x04e4057006ca0330 0xe28803e0071c0470 0xf14401f0038e0238

def z605 : W := mkw 0x01c800a00d940420 0x00e4005006ca0210 0xf3f803e00ffc0470 0xf9fc01f007fe0238

def z606 : W := mkw 0x01eac0000ed28000 0x00f5600007694000 0xd3fec0000fffc001 0xe9ff600007ffe000

def z607 : W := mkw 0x13ffa50c8cf1e188 0x89ffd2864678f0c4 0x19760c1c08e1c380 0x0cbb060e0470e1c0

def z608 : W := mkw 0x000050a0530e1423 0x0000285029870a11 0xc289f1e0f71e3801 0xe144f8f07b8f1c00

def z609 : W := mkw 0x15effa160edbf2c8 0x0af7fd0b076df964 0xdbfffc1c0ffffb81 0xedfffe0e07fffdc0

def z610 : W := mkw 0x2005201220000000 0x1002900910000000 0x0001300330000000 0x0000980198000000

def z611 : W := mkw 0x021055add32e5dbf 0x81082ad6e9972edf 0xee89fffff71e3fff 0xf744fffffb8f1fff

def z612 : W := mkw 0x0000000400004088 0x0000000200002044 0x09060c1c0801c380 0x0483060e0400e1c0

def z613 : W := mkw 0x19effa600edfb260 0x0cf7fd30076fd930 0xd3fff2600ffff871 0xe9fff93007fffc38

def z614 : W := mkw 0x0232c50c8262c188 0x81196286413160c4 0xdb76cc1c0be3c381 0xedbb660e05f1e1c0

def z615 : W := mkw 0x127af588c3fa9503 0x893d7ac461fd4a81 0x1278f180c3fc0000 0x893c78c061fe0000

def z616 : W := mkw 0x018000000c000000 0x00c0000006000000 0xc18000000c000000 0x60c0000006000000

def z617 : W := mkw 0x05800a050c016adc 0x02c005028600b56e 0xe9800e000c03fffe 0x74c007000601ffff

def z618 : W := mkw 0x21cd3a73300c1834 0x10e69d3998060c1a 0x00893263341c3870 0x004499319a0e1c38

def z619 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x5270c180cbe3c78e 0xa93860c065f1e3c7

def z620 : W := mkw 0x10005000024bb000 0x080028000125d800 0x000000000003f800 0x000000000001fc00

def z621 : W := mkw 0x0222c0844362c58b 0x8111604221b162c5 0xd376c0000be3c78f 0xe9bb600005f1e3c7

def z622 : W := mkw 0x03b7c58ccf63e58b 0x81dbe2c667b1f2c5 0xfff7cd9ccfe3ff8f 0xfffbe6ce67f1ffc7

def z623 : W := mkw 0x09d80fe15db40f77 0x04ec07f0aeda07bb 0xfff80fe3fffc07fe 0xfffc07f1fffe03ff

def z624 : W := mkw 0x31ffbf5aac993000 0x18ffdfad564c9800 0xbdfffffff41c3801 0xdefffffffa0e1c00

def z625 : W := mkw 0x0058054000000000 0x002c02a000000000 0x107801e000000000 0x883c00f000000000

def z626 : W := mkw 0x21a7aa1aa0000000 0x10d3d50d50000000 0xad87fe1ff0000001 0x56c3ff0ff8000000

def z627 : W := mkw 0x09d80fc00db00740 0x04ec07e006d803a0 0xfb700d800be00780 0xfdb806c005f003c0

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0xad060c1c00000001 0x5683060e00000000

def z629 : W := mkw 0x11efa0000cd1a000 0x08f7d0000668d000 0xd1f700000ce3f801 0x68fb80000671fc00

def z630 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x2d060e1f0801c7fe 0x1683070f8400e3ff

def z631 : W := mkw 0x05855ab75f0f7eff 0x02c2ad5baf87bf7f 0xef870e1f0f1fffff 0x77c3870f878fffff

def z632 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x10f9f3e3f0000000 0x887cf9f1f8000000

def z633 : W := mkw 0x19faffe00ffe9760 0x0cfd7ff007ff4bb0 0xfbf8ffe00ffc07f0 0xfdfc7ff007fe03f8

def z634 : W := mkw 0x021045844362c58b 0x810822c221b162c5 0xfb700d800be3c78e 0xfdb806c005f1e3c7

def z635 : W := mkw 0x11eff0010edbb814 0x08f7f800876ddc0a 0xf7fff2030ffffc7f 0xfbfff90187fffe3f

def z636 : W := mkw 0x11cd20000c912000 0x08e6900006489000 0x0000000000000000 0x0000000000000000

def z637 : W := mkw 0x19ffaf400cf1a340 0x0cffd7a00678d1a0 0x19760c0008e1c380 0x0cbb06000470e1c0

def z638 : W := mkw 0x0bfacfe8cff68763 0x85fd67f467fb43b1 0xfbf8cfe0cffc07f0 0xfdfc67f067fe03f8

def z639 : W := mkw 0x0000008001200500 0x0000004000900280 0x420000000be00780 0x2100000005f003c0

def z640 : W := mkw 0x01efe00002428000 0x00f7f00001214000 0xd3fff0000be3c001 0xe9fff80005f1e000

def z641 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x2608f3e3f31c047e 0x930479f1f98e023f

def z642 : W := mkw 0x35ffff5faedbfadc 0x1affffafd76dfd6e 0xffffffffffffffff 0xffffffffffffffff

def z643 : W := mkw 0x060040854f63efdf 0x83002042a7b1f7ef 0x420000000fe3fffe 0x2100000007f1ffff

def z644 : W := mkw 0x05850a160c0162c8 0x02c2850b0600b164 0xad870e1f0801c381 0x56c3870f8400e1c0

def z645 : W := mkw 0x01d805800db00500 0x00ec02c006d80280 0xfbf80d800ffc0780 0xfdfc06c007fe03c0

def z646 : W := mkw 0x000050a0530e1423 0x0000285029870a11 0xe288f3e0f71c0470 0xf14479f07b8e0238

def z647 : W := mkw 0x00005001020a1814 0x0000280081050c0a 0xe689f203071e3c7f 0xf344f901838f1e3f

def z648 : W := mkw 0x006aa00000000000 0x0035500000000000 0x1078f00000000000 0x883c780000000000

def z649 : W := mkw 0x01c8000000000000 0x00e4000000000000 0x91f8000000000000 0xc8fc000000000000

def z650 : W := mkw 0x0232850880608100 0x8119428440304080 0x1070000000e00000 0x0838000000700000

def z651 : W := mkw 0x09d85fe05fbe1763 0x04ec2ff02fdf0bb1 0xfbf8ffe0fffc07f0 0xfdfc7ff07ffe03f8

def z652 : W := mkw 0x13ffe58ccff3e58b 0x89fff2c667f9f2c5 0xff76cd9ccbe3c78f 0xffbb66ce65f1e3c7

def z653 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x0289f3e3f71c3870 0x8144f9f1fb8e1c38

def z654 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x008ff000041ff801 0x0047f800020ffc00

def z655 : W := mkw 0x0232c588c3628503 0x811962c461b14281 0xbf76cd9cc3e00001 0xdfbb66ce61f00000

def z656 : W := mkw 0x11eff000024bb000 0x08f7f8000125d800 0x91fff0000003f801 0xc8fff8000001fc00

def z657 : W := mkw 0x08100fe151240f77 0x040807f0a89207bb 0x2c000fe3f00007fe 0x160007f1f80003ff

def z658 : W := mkw 0x01d80f4000000000 0x00ec07a000000000 0xbdf9ffe3f0000001 0xdefcfff1f8000000

def z659 : W := mkw 0x06100f9fc1204fdf 0x830807cfe09027ef 0x2c000f9fc00007fe 0x160007cfe00003ff

def z660 : W := mkw 0x03ffe58cc362c58b 0x81fff2c661b162c5 0xfffffd9ccbe3c78f 0xfffffece65f1e3c7

def z661 : W := mkw 0x09c80a400c900240 0x04e4052006480120 0x0000000000000000 0x0000000000000000

def z662 : W := mkw 0x0400000500004adc 0x020000028000256e 0x00000000000007fe 0x00000000000003ff

def z663 : W := mkw 0x207aa548a0000000 0x103d52a450000000 0x1070000000000000 0x0838000000000000

def z664 : W := mkw 0x21ffafdaa1200500 0x10ffd7ed50900280 0xfffffffffbe00781 0xfffffffffdf003c0

def z665 : W := mkw 0x018500040c016088 0x00c280020600b044 0xed870c1c0c03ff8f 0x76c3860e0601ffc7

def z666 : W := mkw 0x000040a153060c37 0x00002050a983061b 0xe600c3e3f302047f 0xf30061f1f981023f

def z667 : W := mkw 0x21cd2a5220000000 0x10e6952910000000 0xa489f3e3f0000001 0xd244f9f1f8000000

def z668 : W := mkw 0x0232c5add366cdbf 0x811962d6e9b366df 0xff76cffffbe3c7ff 0xffbb67fffdf1e3ff

def z669 : W := mkw 0x05efaa170c016adc 0x02f7d50b8600b56e 0xfdfffe1f0c03ffff 0xfeffff0f8601ffff

def z670 : W := mkw 0x0000000100000814 0x000000008000040a 0x040100030002380f 0x0200800180011c07

def z671 : W := mkw 0x000000a051040423 0x0000005028820211 0x000001e0f0000000 0x000000f078000000

def z672 : W := mkw 0x01800a010c000a54 0x00c005008600052a 0xed810e030c023fff 0x76c0870186011fff

def z673 : W := mkw 0x15efaa170cd1eadc 0x0af7d50b8668f56e 0xfdf70e1f0ce3ffff 0x7efb870f8671ffff

def z674 : W := mkw 0x1227f00cc24bf08b 0x8913f8066125f845 0x0407f01cc003f80f 0x0203f80e6001fc07

def z675 : W := mkw 0x21cd7af3730e1c37 0x10e6bd79b9870e1b 0xe689f3e3f71e3c7f 0xf344f9f1fb8f1e3f

def z676 : W := mkw 0x08000a6000040260 0x0400053000020130 0x0000026000000070 0x0000013000000038

def z677 : W := mkw 0x2027f01bf20a1817 0x1013f80df9050c0b 0x0407f01ff002380f 0x0203f80ff8011c07

def z678 : W := mkw 0x00005021520e1837 0x00002810a9070c1b 0x0489f263f41e387f 0x0244f931fa0f1c3f

def z679 : W := mkw 0x09c85ae15f9e1e77 0x04e42d70afcf0f3b 0xe689f3e3f71e3c7f 0xf344f9f1fb8f1e3f

def z680 : W := mkw 0x01d80f400c900000 0x00ec07a006480000 0xfbf80fe00ffc0000 0xfdfc07f007fe0000

def z681 : W := mkw 0x23ffaf5ea060c188 0x91ffd7af503060c4 0xbdfffffff8e1c381 0xdefffffffc70e1c0

def z682 : W := mkw 0x0000000000000000 0x0000000000000000 0xc081000004023801 0x6040800002011c00

def z683 : W := mkw 0x0627c01fc243e89f 0x8313e00fe121f44f 0x0407c01fc003f80f 0x0203e00fe001fc07

def z684 : W := mkw 0x040500170001689c 0x0202800b8000b44e 0xed070c1f0803ff8f 0x7683860f8401ffc7

def z685 : W := mkw 0x081005e001240520 0x040802f000920290 0x000001e000000000 0x000000f000000000

def z686 : W := mkw 0x00000a1200000000 0x0000050900000000 0x2c000e1f00000000 0x1600070f80000000

def z687 : W := mkw 0x0ddd0ff60db567e8 0x06ee87fb06dab3f4 0xfbfe0ffc0ffdc7f0 0xfdff07fe07fee3f8

def z688 : W := mkw 0x000050a0530e1423 0x0000285029870a11 0xa689f3e3f31c0001 0xd344f9f1f98e0000

def z689 : W := mkw 0x15eff0170edbf89c 0x0af7f80b876dfc4e 0xd7fff01f0ffff80f 0xebfff80f87fffc07

def z690 : W := mkw 0x05850a120c012240 0x02c2850906009120 0x0000000000000000 0x0000000000000000

def z691 : W := mkw 0x21ffbf7bb00c1834 0x10ffdfbdd8060c1a 0xbdfffffff41c3871 0xdefffffffa0e1c38

def z692 : W := mkw 0x00005000020a1000 0x0000280001050800 0x0001f00000023801 0x0000f80000011c00

def z693 : W := mkw 0x11cd70a15f9f3c37 0x08e6b850afcf9e1b 0xe689f3e3f71e3c7f 0xf344f9f1fb8f1e3f

def z694 : W := mkw 0x05850ab75d056eff 0x02c2855bae82b77f 0xed870ffffc03ffff 0x76c387fffe01ffff

def z695 : W := mkw 0x01efa0000c012000 0x00f7d00006009000 0xd1fff0000c03f801 0xe8fff8000601fc00

def z696 : W := mkw 0x0222c00cc242c08b 0x8111600661216045 0xd776c01ccbe3c00f 0xebbb600e65f1e007

def z697 : W := mkw 0x05855a175e0b7adf 0x02c2ad0baf05bd6f 0xed87fe1ffc03ffff 0x76c3ff0ffe01ffff

def z698 : W := mkw 0x11efa0000cd1a000 0x08f7d0000668d000 0x91fff00008e1c001 0xc8fff8000470e000

def z699 : W := mkw 0x39fffffaafffb760 0x1cfffffd57ffdbb0 0xfffffffffffffff1 0xfffffffffffffff8

def z700 : W := mkw 0x2427a01fa001689c 0x1213d00fd000b44e 0x0407f01ff003f80f 0x0203f80ff801fc07

def z701 : W := mkw 0x29cd2a722c940260 0x14e69539164a0130 0x00893263341c0070 0x004499319a0e0038

def z702 : W := mkw 0x0222c008c2428003 0x8111600461214001 0x0000c000c0000000 0x0000600060000000

def z703 : W := mkw 0x0000400002428000 0x0000200001214000 0x420000000be3c000 0x2100000005f1e000

def z704 : W := mkw 0x0222800c8040c088 0x8111400640206044 0x0006001c0001c000 0x0003000e0000e000

def z705 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x137ef0000bfdc000 0x89bf780005fee000

def z706 : W := mkw 0x11eff0a00fdfb420 0x08f7f85007efda10 0xf3fff3e00ffffc71 0xf9fff9f007fffe38

def z707 : W := mkw 0x0c100ff751244fff 0x060807fba89227ff 0x2c000ffff00007fe 0x160007fff80003ff

def z708 : W := mkw 0x29d82fe02db40760 0x14ec17f016da03b0 0xfbf83fe03ffc07f0 0xfdfc1ff01ffe03f8

def z709 : W := mkw 0x247aa54dac016adc 0x123d52a6d600b56e 0x5078f1e0fc03fffe 0xa83c78f07e01ffff

def z710 : W := mkw 0x0232850c8060c188 0x81194286403060c4 0xfd76cd9cc8e3c78f 0xfebb66ce6471e3c7

def z711 : W := mkw 0x0beaca6cced6c2eb 0x85f56536676b6175 0x048ec27cc41fc07f 0x0247613e620fe03f

def z712 : W := mkw 0x29ffaf5aa0b00100 0x14ffd7ad50580080 0xbdfffffff0e00001 0xdefffffff8700000

def z713 : W := mkw 0x0232d58cd36ad58b 0x81196ac669b56ac5 0xff76fd9cfbe3c78f 0xffbb7ece7df1e3c7

def z714 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xe9860e1c0c03fffe 0x74c3070e0601ffff

def z715 : W := mkw 0x21fffffbf30e1c37 0x10fffffdf9870e1b 0x5b760c1c071e3c7e 0x2dbb060e038f1e3f

def z716 : W := mkw 0x0232850c8060c188 0x81194286403060c4 0x3d760c1c08e1c78e 0x1ebb060e0470e3c7

def z717 : W := mkw 0x106af00002da9000 0x08357800016d4800 0xd3fff0000ffff801 0xe9fff80007fffc00

def z718 : W := mkw 0x21ffaf5aac000240 0x10ffd7ad56000120 0xbdfffffff4000071 0xdefffffffa000038

def z719 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x4d070c1f0c03ffff 0x2683860f8601ffff

def z720 : W := mkw 0x09d85f415eba1b57 0x04ec2fa0af5d0dab 0x1d71fc03f8e23b8f 0x0eb8fe01fc711dc7

def z721 : W := mkw 0x23cd6ad66362c58b 0x91e6b56b31b162c5 0x428932633be3c78e 0x214499319df1e3c7

def z722 : W := mkw 0x085805e001b40520 0x042c02f000da0290 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z723 : W := mkw 0x11efa0a15dd5ac37 0x08f7d050aeead61b 0x357603e3f8e1c47e 0x1abb01f1fc70e23f

def z724 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xf7fff180cffff801 0xfbfff8c067fffc00

def z725 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x0689f3e3f71e387f 0x8344f9f1fb8f1c3f

def z726 : W := mkw 0x1a7af5e8c3fe9523 0x8d3d7af461ff4a91 0x1278f1e0c3fc0000 0x893c78f061fe0000

def z727 : W := mkw 0x21ffaf5aa0000240 0x10ffd7ad50000120 0xbdfffffff00007f1 0xdefffffff80003f8

def z728 : W := mkw 0x09d80ff20db40760 0x04ec07f906da03b0 0xfff80fff0ffc07f0 0xfffc07ff87fe03f8

def z729 : W := mkw 0x0a100fedd1244fff 0x850807f6e89227ff 0x2c000ffff00007fe 0x160007fff80003ff

def z730 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xd376c0000ffff801 0xe9bb600007fffc00

def z731 : W := mkw 0x0222d00dd24ad89f 0x81116806e9256c4f 0x0406c01cc003f80f 0x0203600e6001fc07

def z732 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xfffffffffbe00001 0xfffffffffdf00000

def z733 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x5b76cd9ccbe3c78e 0xadbb66ce65f1e3c7

def z734 : W := mkw 0x04050a1700016adc 0x0202850b8000b56e 0xed070e1f0803ffff 0x7683870f8401ffff

def z735 : W := mkw 0x05cd0a570c016adc 0x02e6852b8600b56e 0xed8f0e7f0c03ffff 0x76c7873f8601ffff

def z736 : W := mkw 0x01cd50000e9b3000 0x00e6a800074d9800 0xd3fff0000ffff801 0xe9fff80007fffc00

def z737 : W := mkw 0x01efc0000ed3a000 0x00f7e0000769d000 0xd3ffc0000ffff801 0xe9ffe00007fffc00

def z738 : W := mkw 0x04050a1700016adc 0x0202850b8000b56e 0xec870e1f0403ffff 0x7643870f8201ffff

def z739 : W := mkw 0x081005a00db40760 0x040802d006da03b0 0x527001800ffc07f0 0xa93800c007fe03f8

def z740 : W := mkw 0x13dd358ccdb9758b 0x89ee9ac666dcbac5 0x2c893d9cc41c3f8e 0x16449ece620e1fc7

def z741 : W := mkw 0x29d80ff22db40760 0x14ec07f916da03b0 0xfbf80fe33ffc07f0 0xfdfc07f19ffe03f8

def z742 : W := mkw 0x19dd2fe00db52760 0x0cee97f006da93b0 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z743 : W := mkw 0x05c80a170c904adc 0x02e4050b8648256e 0xfff80e1f0ffc07fe 0xfffc070f87fe03ff

def z744 : W := mkw 0x15cd2a170c916adc 0x0ae6950b8648b56e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z745 : W := mkw 0x0c5d05f701b56dbc 0x062e82fb80dab6de 0x167f01ff03fff80f 0x8b3f80ff81fffc07

def z746 : W := mkw 0x3427f01fa24bf89c 0x1a13f80fd125fc4e 0x0407f01ff003f80f 0x0203f80ff801fc07

def z747 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x537ef0000ffff800 0xa9bf780007fffc00

def z748 : W := mkw 0x2037af5aa0000000 0x101bd7ad50000000 0xac8ffffff0000001 0xd647fffff8000000

def z749 : W := mkw 0x05cd0a170c916adc 0x02e6850b8648b56e 0xed8f0e1f0c1fffff 0x76c7870f860fffff

def z750 : W := mkw 0x0232d58cc36ad58b 0x81196ac661b56ac5 0xff76cd9ccfffff8f 0xffbb66ce67ffffc7

def z751 : W := mkw 0x29ffaf5aacb00340 0x14ffd7ad565801a0 0xfffffffffffc0381 0xfffffffffffe01c0

def z752 : W := mkw 0x09c80a600c940260 0x04e40530064a0130 0xfbf80e600ffc07f0 0xfdfc073007fe03f8

def z753 : W := mkw 0x31effa522edbb000 0x18f7fd29176dd800 0xfffffe7f3ffff801 0xffffff3f9ffffc00

def z754 : W := mkw 0x21ffaf5aac900240 0x10ffd7ad56480120 0xfffffffffffc07f1 0xfffffffffffe03f8

def z755 : W := mkw 0x020050a1536e9d37 0x81002850a9b74e9b 0xe689f3e3f7fe3c7f 0xf344f9f1fbff1e3f

def z756 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xf7fff0000ffffc0f 0xfbfff80007fffe07

def z757 : W := mkw 0x06100fbfd1244fff 0x830807dfe89227ff 0x2c000ffff00007fe 0x160007fff80003ff

def z758 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xfdfffffff4023801 0xfefffffffa011c00

def z759 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xff760c1c0be3c78f 0x7fbb060e05f1e3c7

def z760 : W := mkw 0x106af0000edbb000 0x08357800076dd800 0xd2f9f0000ffff801 0xe97cf80007fffc00

def z761 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xed8f0fff0c03ffff 0xf6c787ff8601ffff

def z762 : W := mkw 0x0010050400204188 0x00080282001020c4 0xfd760c1c08e3c78f 0x7ebb060e0471e3c7

def z763 : W := mkw 0x29d80fe8adb40760 0x14ec07f456da03b0 0xfbf80fe0fffc07f0 0xfdfc07f07ffe03f8

def z764 : W := mkw 0x106af0000edbb000 0x08357800076dd800 0x527000000ffff800 0x2938000007fffc00

def z765 : W := mkw 0x0005001200000000 0x0002800900000000 0xa48ff3fff0000001 0xd247f9fff8000000

def z766 : W := mkw 0x2037a55aa0000000 0x101bd2ad50000000 0x0407f1fff0000001 0x0203f8fff8000000

def z767 : W := mkw 0x30105f5aaedbb000 0x18082fad576dd800 0x6e000ffffffff800 0x370007fffffffc00

def z768 : W := mkw 0x01dd0f5200000000 0x00ee87a900000000 0xbdfffffff0000001 0xdefffffff8000000

def z769 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfff8cfe0cffc07f1 0xfffc67f067fe03f8

def z770 : W := mkw 0x1dcd3a730c9d3a74 0x0ee69d39864e9d3a 0x00893263041c3870 0x00449931820e1c38

def z771 : W := mkw 0x0dcd0a570c916adc 0x06e6852b8648b56e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z772 : W := mkw 0x21faaf5aa0000000 0x10fd57ad50000000 0xbdf8fffff0000000 0xdefc7ffff8000000

def z773 : W := mkw 0x09d80fe04db40763 0x04ec07f026da03b1 0xfff80fe0cffc07fe 0xfffc07f067fe03ff

def z774 : W := mkw 0x21efa01aa0000000 0x10f7d00d50000000 0xb5fff3fff0000001 0xdafff9fff8000000

def z775 : W := mkw 0x11cd70000edbb000 0x08e6b800076dd800 0xd3f930000ffff800 0xe9fc980007fffc00

def z776 : W := mkw 0x11eff00002dbb000 0x08f7f800016dd800 0x93fff00003fff801 0xc9fff80001fffc00

def z777 : W := mkw 0x2232e58ce362c58b 0x911972c671b162c5 0xff76fd9cfbe3c78f 0xffbb7ece7df1e3c7

def z778 : W := mkw 0x120050a55ffffdbf 0x89002852affffedf 0x420000000ffffffe 0x2100000007ffffff

def z779 : W := mkw 0x01eff000024a9000 0x00f7f80001254800 0xd3fff0000ffff801 0xe9fff80007fffc00

def z780 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xff77fd9ffbe3c78f 0xffbbfecffdf1e3c7

def z781 : W := mkw 0x29ffaf5aacb00340 0x14ffd7ad565801a0 0xfdfffffffce007f1 0xfefffffffe7003f8

def z782 : W := mkw 0x0c100fe501244ffc 0x060807f2809227fe 0x28000fe0000007fe 0x140007f0000003ff

def z783 : W := mkw 0x07b7cf9bcf63af57 0x83dbe7cde7b1d7ab 0x12f1c383c7e03870 0x8978e1c1e3f01c38

def z784 : W := mkw 0x207aaf5aa0000000 0x103d57ad50000000 0xbd7efffff0000001 0xdebf7ffff8000000

def z785 : W := mkw 0x040500170c016adc 0x0202800b8600b56e 0xed070c1f0c03ffff 0x7683860f8601ffff

def z786 : W := mkw 0x11c850000edbb000 0x08e42800076dd800 0xd3f9f0000ffff801 0xe9fcf80007fffc00

def z787 : W := mkw 0x01900fa00d240760 0x00c807d0069203b0 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z788 : W := mkw 0x11efa0000cd1a000 0x08f7d0000668d000 0xd3ff00000ffff801 0xe9ff800007fffc00

def z789 : W := mkw 0x11c850000edbb000 0x08e42800076dd800 0x537000000ffff800 0x29b8000007fffc00

def z790 : W := mkw 0x2232c5cce362c58b 0x911962e671b162c5 0xff76cdfcfbe3c78f 0xffbb66fe7df1e3c7

def z791 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x19fffffff0000000 0x8cfffffff8000000

def z792 : W := mkw 0x040000050c016adc 0x020000028600b56e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z793 : W := mkw 0x0232c5acc366c5ab 0x811962d661b362d5 0xff76cd9ccfffc7ff 0xffbb66ce67ffe3ff

def z794 : W := mkw 0x207aaf5aa0000000 0x103d57ad50000000 0xbcf9fffff0000001 0xde7cfffff8000000

def z795 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xef8f0e1f0f1fffff 0xf7c7870f878fffff

def z796 : W := mkw 0x11eff0004edbb003 0x08f7f800276dd801 0xd7fff000cffff80f 0xebfff80067fffc07

def z797 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x1d7ffdfff0000001 0x8ebffefff8000000

def z798 : W := mkw 0x29d80ffaadb40760 0x14ec07fd56da03b0 0xfff9fffffffc07f1 0xfffcfffffffe03f8

def z799 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x5bf80e600ffc07f0 0x2dfc073007fe03f8

def z800 : W := mkw 0x0dcd1a731c9d3a74 0x06e68d398e4e9d3a 0x00893263341c3870 0x004499319a0e1c38

def z801 : W := mkw 0x20100f5aa0000000 0x100807ad50000000 0x2c08fffff0000000 0x96047ffff8000000

def z802 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xfffecd9ccfffc78f 0xffff66ce67ffe3c7

def z803 : W := mkw 0x146afa1702dadadc 0x0a357d0b816d6d6e 0x3e78fe1f03fc07fe 0x9f3c7f0f81fe03ff

def z804 : W := mkw 0x11effa120edbb240 0x08f7fd09076dd920 0xfffffe1f0ffffff1 0xffffff0f87fffff8

def z805 : W := mkw 0x23ffaf5aa0608100 0x91ffd7ad50304080 0xbdfffffff0e00001 0xdefffffff8700000

def z806 : W := mkw 0x05855ab65f0f76eb 0x02c2ad5b2f87bb75 0x0b0efdfcfb1dc380 0x85877efe7d8ee1c0

def z807 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x5377f0000ffff801 0x29bbf80007fffc00

def z808 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xfbfffc000fffff81 0xfdfffe0007ffffc0

def z809 : W := mkw 0x09dd0ff20db40760 0x04ee87f906da03b0 0xfffffffffffc07f1 0xfffffffffffe03f8

def z810 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xff76cffffbe3c78f 0xffbb67fffdf1e3c7

def z811 : W := mkw 0x09c800a00db40760 0x04e4005006da03b0 0x537000000ffc07f0 0x29b8000007fe03f8

def z812 : W := mkw 0x39ffaf5aacf1a340 0x1cffd7ad5678d1a0 0xbdfffffff8e1c381 0xdefffffffc70e1c0

def z813 : W := mkw 0x11ead0000edbb000 0x08f56800076dd800 0xd3fec0000ffff801 0xe9ff600007fffc00

def z814 : W := mkw 0x21ffaf5aac012240 0x10ffd7ad56009120 0xfdfffffffc03fff1 0xfefffffffe01fff8

def z815 : W := mkw 0x060050a55f6fffff 0x83002852afb7ffff 0x420000000ffffffe 0x2100000007ffffff

def z816 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x52f9f0000ffff800 0xa97cf80007fffc00

def z817 : W := mkw 0x2dcd2a732c952a74 0x16e69539964a953a 0x00893263341c3870 0x004499319a0e1c38

def z818 : W := mkw 0x2037a51aa0000000 0x101bd28d50000000 0xbdfffffff0000001 0xdefffffff8000000

def z819 : W := mkw 0x106ff00002dbb000 0x0837f800016dd800 0xd2fff00007fff801 0xe97ff80003fffc00

def z820 : W := mkw 0x21ffaf5aac000240 0x10ffd7ad56000120 0xbdfffffff8000381 0xdefffffffc0001c0

def z821 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xfffffffff71c0001 0xfffffffffb8e0000

def z822 : W := mkw 0x001005a001240520 0x000802d000920290 0xfb700d800ffc07f0 0xfdb806c007fe03f8

def z823 : W := mkw 0x04000a170c016adc 0x0200050b8600b56e 0xed060e1f0c03ffff 0x7683070f8601ffff

def z824 : W := mkw 0x15effa120edbb240 0x0af7fd09076dd920 0xd3fff0000ffff801 0xe9fff80007fffc00

def z825 : W := mkw 0x0032c5840362c588 0x001962c201b162c4 0xff76cd9c0be3c78f 0xffbb66ce05f1e3c7

def z826 : W := mkw 0x081005a00db40760 0x040802d006da03b0 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z827 : W := mkw 0x11effa000edbb240 0x08f7fd00076dd920 0xd3fff2000ffff871 0xe9fff90007fffc38

def z828 : W := mkw 0x11effa120edbb000 0x08f7fd09076dd800 0xdbfffc1c0ffff801 0xedfffe0e07fffc00

def z829 : W := mkw 0x2027a01aa0000000 0x1013d00d50000000 0x2407f3fff0000001 0x1203f9fff8000000

def z830 : W := mkw 0x100050000edbb000 0x08002800076dd800 0xd37000000ffff800 0xe9b8000007fffc00

def z831 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfbf93fe33ffc07f0 0xfdfc9ff19ffe03f8

def z832 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfffe0ffc0ffc07f1 0xffff07fe07fe03f8

def z833 : W := mkw 0x11cd30000c993000 0x08e69800064c9800 0xd3ff30000ffff801 0xe9ff980007fffc00

def z834 : W := mkw 0x29dd2ff22db40760 0x14ee97f916da03b0 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z835 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0xef89ffe3ff1e3fff 0xf7c4fff1ff8f1fff

def z836 : W := mkw 0x0232952d906cd9bc 0x81194a96c8366cde 0x19ff3e7f3cfdfbf0 0x0cff9f3f9e7efdf8

def z837 : W := mkw 0x31effa522edbb000 0x18f7fd29176dd800 0xd3fff0000ffff801 0xe9fff80007fffc00

def z838 : W := mkw 0x31eff01aaedbb000 0x18f7f80d576dd800 0xf7fff3fffffff801 0xfbfff9fffffffc00

def z839 : W := mkw 0x15cd2a130c912a54 0x0ae695098648952a 0x0081020304003870 0x0040810182001c38

def z840 : W := mkw 0x09dd0fe00db52760 0x04ee87f006da93b0 0xfbf90fe00ffc3ff0 0xfdfc87f007fe1ff8

def z841 : W := mkw 0x1027f0000edbb000 0x0813f800076dd800 0xd377f0000ffff801 0xe9bbf80007fffc00

def z842 : W := mkw 0x2827a0baadb40760 0x1413d05d56da03b0 0x4607f01ffffc07f1 0x2303f80ffffe03f8

def z843 : W := mkw 0x21a7aa1aa0000000 0x10d3d50d50000000 0xad8ffffff0000001 0xd6c7fffff8000000

def z844 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xfdfffffff002040f 0xfefffffff8010207

def z845 : W := mkw 0x09d80fe00db52760 0x04ec07f006da93b0 0xfbf80fe00ffffff0 0xfdfc07f007fffff8

def z846 : W := mkw 0x127af5a8d3fe9523 0x893d7ad469ff4a91 0x1278f1e0f3fc0000 0x893c78f079fe0000

def z847 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xfdfffffff4000471 0xfefffffffa000238

def z848 : W := mkw 0x021045844362c58b 0x810822c221b162c5 0xff760d9c0be3c78f 0xffbb06ce05f1e3c7

def z849 : W := mkw 0x227af5e8f36e9523 0x913d7af479b74a91 0x1278f1e0f3fc0000 0x893c78f079fe0000

def z850 : W := mkw 0x21950f5aa0000000 0x10ca87ad50000000 0xad8ffffff0000001 0xd6c7fffff8000000

def z851 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xed87fe1ffc03ffff 0x76c3ff0ffe01ffff

def z852 : W := mkw 0x0232d5acd36ed5ab 0x81196ad669b76ad5 0xfffffffffbffc78f 0xfffffffffdffe3c7

def z853 : W := mkw 0x05cd00170c91689c 0x02e6800b8648b44e 0xd7ff001f0ffff80f 0xebff800f87fffc07

def z854 : W := mkw 0x01c800000c912000 0x00e4000006489000 0xd3f800000ffff800 0xe9fc000007fffc00

def z855 : W := mkw 0x05850a170c916adc 0x02c2850b8648b56e 0xef870e1f0fffffff 0x77c3870f87ffffff

def z856 : W := mkw 0x1022d0000edbb000 0x08116800076dd800 0x5270c0000ffff800 0xa938600007fffc00

def z857 : W := mkw 0x0022c0844342c48b 0x0011604221a16245 0xff76cd9ccbe3c78f 0xffbb66ce65f1e3c7

def z858 : W := mkw 0x085805e00db40760 0x042c02f006da03b0 0x527000000ffc07f0 0x2938000007fe03f8

def z859 : W := mkw 0x31ffaf5aa041a000 0x18ffd7ad5020d000 0xbdfffffff001c001 0xdefffffff800e000

def z860 : W := mkw 0x020050a5532e5dbf 0x81002852a9972edf 0x42000000071e3ffe 0x21000000038f1fff

def z861 : W := mkw 0x21ffaf5aa0012000 0x10ffd7ad50009000 0xbdfffffff003f801 0xdefffffff801fc00

def z862 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x1bf80fe00ffc03f0 0x8dfc07f007fe01f8

def z863 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x2d070e1f0803ffff 0x1683870f8401ffff

def z864 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x3d7efffff0000000 0x9ebf7ffff8000000

def z865 : W := mkw 0x1427f017524bf89f 0x0a13f80ba925fc4f 0x0407f01ff003f80f 0x0203f80ff801fc07

def z866 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xdbf80c000ffc07f0 0xedfc060007fe03f8

def z867 : W := mkw 0x05cd2a170c016adc 0x02e6950b8600b56e 0xed8f3e1f0c03ffff 0x76c79f0f8601ffff

def z868 : W := mkw 0x104850000edbb000 0x08242800076dd800 0x527800000ffff800 0xa93c000007fffc00

def z869 : W := mkw 0x31eff01aaedbb000 0x18f7f80d576dd800 0xd3fff01c0ffff801 0xe9fff80e07fffc00

def z870 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0xf7f9f3e3fffe3c7f 0xfbfcf9f1ffff1e3f

def z871 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x2c870e1f0403ffff 0x1643870f8201ffff

def z872 : W := mkw 0x09d805a00db40760 0x04ec02d006da03b0 0xfbf80d800ffc07f0 0xfdfc06c007fe03f8

def z873 : W := mkw 0x0232d5acd36ed5ab 0x81196ad669b76ad5 0xfffefffcffffc7ff 0xffff7ffe7fffe3ff

def z874 : W := mkw 0x01ead0000eda9000 0x00f56800076d4800 0xd3fff0000ffff801 0xe9fff80007fffc00

def z875 : W := mkw 0x09dd2fe00db40760 0x04ee97f006da03b0 0xfbf93fe00ffc07f0 0xfdfc9ff007fe03f8

def z876 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x13fff0000ffdf800 0x89fff80007fefc00

def z877 : W := mkw 0x15cd3a331c9d3a74 0x0ae69d198e4e9d3a 0x00893263341c3870 0x004499319a0e1c38

def z878 : W := mkw 0x058500050c016adc 0x02c280028600b56e 0xed870c1c0c03ffff 0x76c3860e0601ffff

def z879 : W := mkw 0x11effa120edbb000 0x08f7fd09076dd800 0xfffffffffffff801 0xfffffffffffffc00

def z880 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x3cf9fffff0000000 0x9e7cfffff8000000

def z881 : W := mkw 0x106ff0000edbb000 0x0837f800076dd800 0x527ff0000ffff801 0xa93ff80007fffc00

def z882 : W := mkw 0x21ffaf5aa0900000 0x10ffd7ad50480000 0xbffffffff3fc0001 0xdffffffff9fe0000

def z883 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x2489f3e3f41e3c7f 0x1244f9f1fa0f1e3f

def z884 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x2c8ffffff0000001 0x1647fffff8000000

def z885 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x49870e1f0c03fffe 0x24c3870f8601ffff

def z886 : W := mkw 0x0627d01fd24bf89f 0x8313e80fe925fc4f 0x0407f01ff003f80f 0x0203f80ff801fc07

def z887 : W := mkw 0x0232858cc160c58b 0x811942c660b062c5 0xff760d9ccbe1c78e 0xffbb06ce65f0e3c7

def z888 : W := mkw 0x01c800000c900240 0x00e4000006480120 0xd3f800000ffc07f0 0xe9fc000007fe03f8

def z889 : W := mkw 0x080000a00db40760 0x0400005006da03b0 0xd37000000ffc07f0 0xe9b8000007fe03f8

def z890 : W := mkw 0x0232d5acd36ed5ab 0x81196ad669b76ad5 0xfffffdfcffffff8f 0xfffffefe7fffffc7

def z891 : W := mkw 0x1227f00dd24bf89f 0x8913f806e925fc4f 0x0407f01ff003f80f 0x0203f80ff801fc07

def z892 : W := mkw 0x0222c0844362c58b 0x8111604221b162c5 0xff76cc1c0be3c78f 0xffbb660e05f1e3c7

def z893 : W := mkw 0x2c100fffa1244ffc 0x160807ffd09227fe 0x2c000ffff00007fe 0x160007fff80003ff

def z894 : W := mkw 0x21ffaf5aac012000 0x10ffd7ad56009000 0xbdfffffff4003801 0xdefffffffa001c00

def z895 : W := mkw 0x21d80f5aa0000000 0x10ec07ad50000000 0xbdf9fffff0000001 0xdefcfffff8000000

def z896 : W := mkw 0x11eff0120edbb000 0x08f7f809076dd800 0xd7fff01f0ffff801 0xebfff80f87fffc00

def z897 : W := mkw 0x0232d58cc36ad58b 0x81196ac661b56ac5 0xffffffffffffff8f 0xffffffffffffffc7

def z898 : W := mkw 0x01850a170000489c 0x00c2850b8000244e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z899 : W := mkw 0x21cd2a5220000000 0x10e6952910000000 0xad8ffffff0000001 0xd6c7fffff8000000

def z900 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0xe78ff3e3ff1ffc7f 0xf3c7f9f1ff8ffe3f

def z901 : W := mkw 0x207faf5aa0000000 0x103fd7ad50000000 0x3c7ffffff0000001 0x9e3ffffff8000000

def z902 : W := mkw 0x0232c50c8262c188 0x81196286413160c4 0xff76cc1c0be3c78f 0xffbb660e05f1e3c7

def z903 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xfdfffffff803c001 0xfefffffffc01e000

def z904 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0xef8ffffff71e3c7f 0xf7c7fffffb8f1e3f

def z905 : W := mkw 0x13eff008cedbb003 0x89f7f804676dd801 0xd3fff000cffff801 0xe9fff80067fffc00

def z906 : W := mkw 0x084800a00db40760 0x0424005006da03b0 0x527800000ffc07f0 0xa93c000007fe03f8

def z907 : W := mkw 0x0232d5a8d36e9523 0x81196ad469b74a91 0x1270c180c3fc0000 0x893860c061fe0000

def z908 : W := mkw 0x05850a1700016adc 0x02c2850b8000b56e 0xad870e1f0003ffff 0x56c3870f8001ffff

def z909 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xfff7cf9fcbe3c78f 0xfffbe7cfe5f1e3c7

def z910 : W := mkw 0x0232c50cc262c18b 0x81196286613160c5 0x19760c1c08e3c38e 0x0cbb060e0471e1c7

def z911 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x7b700fe00ffc07f0 0x3db807f007fe03f8

def z912 : W := mkw 0x05800a050c016adc 0x02c005028600b56e 0xed860e1c0c03ffff 0x76c3070e0601ffff

def z913 : W := mkw 0x1022d0000edbb000 0x08116800076dd800 0x537600000ffff800 0x29bb000007fffc00

def z914 : W := mkw 0x00005021520e1837 0x00002810a9070c1b 0xa489f3e3f41e387f 0xd244f9f1fa0f1c3f

def z915 : W := mkw 0x31ffaf5aac912000 0x18ffd7ad56489000 0xbdfffffff0000001 0xdefffffff8000000

def z916 : W := mkw 0x0010050880000000 0x0008028440000000 0xac89fffff0000001 0xd644fffff8000000

def z917 : W := mkw 0x31effa522edbb000 0x18f7fd29176dd800 0xf7fff3e3fffff801 0xfbfff9f1fffffc00

def z918 : W := mkw 0x22100ffff1244dbf 0x910807fff89226df 0x2c000ffff00007fe 0x160007fff80003ff

def z919 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xd3fe00000ffff800 0xe9ff000007fffc00

def z920 : W := mkw 0x19effa400edbb240 0x0cf7fd20076dd920 0xd3fff0000ffff801 0xe9fff80007fffc00

def z921 : W := mkw 0x29d80ffaadb40760 0x14ec07fd56da03b0 0xfbf80ffc0ffc07f0 0xfdfc07fe07fe03f8

def z922 : W := mkw 0x08100fe00db40760 0x040807f006da03b0 0xfb700fe00ffc07f0 0xfdb807f007fe03f8

def z923 : W := mkw 0x040050a5530f7cbf 0x02002852a987be5f 0x42000000071ffc7e 0x21000000038ffe3f

def z924 : W := mkw 0x1837ffe0036fb760 0x0c1bfff001b7dbb0 0x2807ffe00003fff1 0x1403fff00001fff8

def z925 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0x6d060e1f0c03fffe 0x3683070f8601ffff

def z926 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xfff6cf9ccfe3c7ff 0xfffb67ce67f1e3ff

def z927 : W := mkw 0x01d80f800db00740 0x00ec07c006d803a0 0xfbf80f800ffc07f0 0xfdfc07c007fe03f8

def z928 : W := mkw 0x21ffaf5aac000000 0x10ffd7ad56000000 0xfdfffffffc000001 0xfefffffffe000000

def z929 : W := mkw 0x09dd0ff20db40760 0x04ee87f906da03b0 0xfbfe0ffc0ffc07f0 0xfdff07fe07fe03f8

def z930 : W := mkw 0x000000050000489c 0x000000028000244e 0xed060c1c0c03ffff 0x7683060e0601ffff

def z931 : W := mkw 0x2dffaf5eacb163c8 0x16ffd7af5658b1e4 0x19760c1c08e1c380 0x0cbb060e0470e1c0

def z932 : W := mkw 0x0000000400004088 0x0000000200002044 0xff760c1c0be3c78f 0xffbb060e05f1e3c7

def z933 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfff90fe30ffc07f1 0xfffc87f187fe03f8

def z934 : W := mkw 0x11effa120edbb000 0x08f7fd09076dd800 0xd3fff2030ffff801 0xe9fff90187fffc00

def z935 : W := mkw 0x35cd3a532c993a54 0x1ae69d29964c9d2a 0x00893263341c3870 0x004499319a0e1c38

def z936 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfff80fe00ffe07ff 0xfffc07f007ff03ff

def z937 : W := mkw 0x05cd0a170c016adc 0x02e6850b8600b56e 0xfdff0e1f0c03ffff 0xfeff870f8601ffff

def z938 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0xfdfffffff8000781 0xfefffffffc0003c0

def z939 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xfff7cd9ccfe3ff8f 0xfffbe6ce67f1ffc7

def z940 : W := mkw 0x2032af5aa0000000 0x101957ad50000000 0x2c00fffff0000000 0x16007ffff8000000

def z941 : W := mkw 0x1427f005024bf89c 0x0a13f8028125fc4e 0x0007f0000003f80f 0x0003f8000001fc07

def z942 : W := mkw 0x01ffa50880000000 0x00ffd28440000000 0xbdfffffff0000001 0xdefffffff8000000

def z943 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xfb760d9c0be3c78e 0xfdbb06ce05f1e3c7

def z944 : W := mkw 0x09d80fe88db40760 0x04ec07f446da03b0 0xfff80ffccffc07f0 0xfffc07fe67fe03f8

def z945 : W := mkw 0x21ffaf5aa0408000 0x10ffd7ad50204000 0xbdfffffff8e1c001 0xdefffffffc70e000

def z946 : W := mkw 0x20100f5aa0000000 0x100807ad50000000 0x2c01fffff0000001 0x1600fffff8000000

def z947 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xed8f3e7f3c03ffff 0x76c79f3f9e01ffff

def z948 : W := mkw 0x31ffaf5aa0d08000 0x18ffd7ad50684000 0xbdfffffff0e00001 0xdefffffff8700000

def z949 : W := mkw 0x0232c5acc366c5ab 0x811962d661b362d5 0xff7ecdfccbffc78f 0xffbf66fe65ffe3c7

def z950 : W := mkw 0x09c80aa00db40760 0x04e4055006da03b0 0xfbf80e000ffc07f0 0xfdfc070007fe03f8

def z951 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xfffffc1c0ffff801 0xfffffe0e07fffc00

def z952 : W := mkw 0x31effa5aaedbb000 0x18f7fd2d576dd800 0xd7fff27ffffff801 0xebfff93ffffffc00

def z953 : W := mkw 0x25852a172c016adc 0x12c2950b9600b56e 0xed873e1f3c03ffff 0x76c39f0f9e01ffff

def z954 : W := mkw 0x0232858cc160c58b 0x811942c660b062c5 0x19760c1c08e1c78e 0x0cbb060e0470e3c7

def z955 : W := mkw 0x0a0050a55ffedfff 0x85002852afff6fff 0x420000000ffffffe 0x2100000007ffffff

def z956 : W := mkw 0x018500050c01689c 0x00c280028600b44e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z957 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x7f760d9ccbe3c78e 0x3fbb06ce65f1e3c7

def z958 : W := mkw 0x01d80fe001240520 0x00ec07f000920290 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z959 : W := mkw 0x000010a1510c1c37 0x00000850a8860e1b 0xa489f3e3f41c3c7f 0xd244f9f1fa0e1e3f

def z960 : W := mkw 0x21ffaf5aac912000 0x10ffd7ad56489000 0xfffffffffffff801 0xfffffffffffffc00

def z961 : W := mkw 0x08580fe001b40760 0x042c07f000da03b0 0xfaf80fe007fc07f0 0xfd7c07f003fe03f8

def z962 : W := mkw 0x00000a1200000000 0x0000050900000000 0xac89fffff0000001 0xd644fffff8000000

def z963 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x3f76cd9ccbe1c78e 0x9fbb66ce65f0e3c7

def z964 : W := mkw 0x29dd2ff22db40760 0x14ee97f916da03b0 0xffff3fff3ffc07f1 0xffff9fff9ffe03f8

def z965 : W := mkw 0x25850a572c016adc 0x12c2852b9600b56e 0xed870e7f3c03ffff 0x76c3873f9e01ffff

def z966 : W := mkw 0x01efa0000c912000 0x00f7d00006489000 0xd3fff0000ffff801 0xe9fff80007fffc00

def z967 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xf3fff2000ffffc71 0xf9fff90007fffe38

def z968 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x137ff0000bfff801 0x89bff80005fffc00

def z969 : W := mkw 0x0232858c8160c588 0x811942c640b062c4 0xff760d9c0be3c78f 0xffbb06ce05f1e3c7

def z970 : W := mkw 0x01800a050c004adc 0x00c005028600256e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z971 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xd3f700000ffff801 0x69fb800007fffc00

def z972 : W := mkw 0x01b78f1a80000000 0x00dbc78d40000000 0xbdfffffff0000001 0xdefffffff8000000

def z973 : W := mkw 0x0232850cc060c18b 0x81194286603060c5 0x1d760c1cc8e1c38e 0x0ebb060e6470e1c7

def z974 : W := mkw 0x21ffaf5aa0200100 0x10ffd7ad50100080 0xbdfffffff8e00381 0xdefffffffc7001c0

def z975 : W := mkw 0x000000a101040c34 0x000000508082061a 0xe689f3e3f71e3c7f 0xf344f9f1fb8f1e3f

def z976 : W := mkw 0x0232c50cc262c18b 0x81196286613160c5 0xfd76cc1cc8e3c78f 0x7ebb660e6471e3c7

def z977 : W := mkw 0x09950fe00d252760 0x04ca87f0069293b0 0xe9870fe00c03fff1 0x74c387f00601fff8

def z978 : W := mkw 0x11eff0000edbb240 0x08f7f800076dd920 0xd3fff0000ffffff1 0xe9fff80007fffff8

def z979 : W := mkw 0x0022800880000000 0x0011400440000000 0xa48ff3fff0000001 0xd247f9fff8000000

def z980 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x53ff30000ffff800 0x29ff980007fffc00

def z981 : W := mkw 0x01fa8f4880000000 0x00fd47a440000000 0xbdfffffff0000001 0xdefffffff8000000

def z982 : W := mkw 0x04000a1700004adc 0x0200050b8000256e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z983 : W := mkw 0x085805e00db40760 0x042c02f006da03b0 0xf2f803e00ffc07f0 0xf97c01f007fe03f8

def z984 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xc9870c1c0c03ffff 0x64c3860e0601ffff

def z985 : W := mkw 0x040000050c016adc 0x020000028600b56e 0x49060c1c0c03fffe 0x2483060e0601ffff

def z986 : W := mkw 0x0e100fffc1244fff 0x870807ffe09227ff 0x2c000fffc00007fe 0x160007ffe00003ff

def z987 : W := mkw 0x0232d58cc36ad58b 0x81196ac661b56ac5 0xff7efd9ccbffc78f 0xffbf7ece65ffe3c7

def z988 : W := mkw 0x11effa000edbb000 0x08f7fd00076dd800 0xfbfffe000ffff801 0xfdffff0007fffc00

def z989 : W := mkw 0x01a7d0000e4bb000 0x00d3e8000725d800 0xd3fff0000ffff801 0xe9fff80007fffc00

def z990 : W := mkw 0x20328f5aa0000000 0x101947ad50000000 0xbdfffffff0000001 0xdefffffff8000000

def z991 : W := mkw 0x0dcd0a530c912a54 0x06e685298648952a 0x0081020304003870 0x0040810182001c38

def z992 : W := mkw 0x21b7af5aa0000000 0x10dbd7ad50000000 0xad87fffff0000001 0x56c3fffff8000000

def z993 : W := mkw 0x09dd0ff20db52760 0x04ee87f906da93b0 0xffff0fff0ffffff1 0xffff87ff87fffff8

def z994 : W := mkw 0x01c80aa00d940660 0x00e4055006ca0330 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z995 : W := mkw 0x21ffaf5aac900000 0x10ffd7ad56480000 0xbdfffffff8e00001 0xdefffffffc700000

def z996 : W := mkw 0x207aa548a0000000 0x103d52a450000000 0xbdfffffff0000001 0xdefffffff8000000

def z997 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x3d76cd9cc8e3c78f 0x1ebb66ce6471e3c7

def z998 : W := mkw 0x0032c50c8242c088 0x0019628641216044 0xff76cd9ccbe3c78f 0xffbb66ce65f1e3c7

def z999 : W := mkw 0x140050a55fdffeff 0x0a002852afefff7f 0x420000000ffffffe 0x2100000007ffffff

def z1000 : W := mkw 0x05cd0a170c916adc 0x02e6850b8648b56e 0xfdf70e1f0ce3ffff 0x7efb870f8671ffff

def z1001 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfff80fe3fffc07f0 0xfffc07f1fffe03f8

def z1002 : W := mkw 0x0032858c81204588 0x001942c6409022c4 0xff76cd9ccbe3c78f 0xffbb66ce65f1e3c7

def z1003 : W := mkw 0x0ddd0ff20db52760 0x06ee87f906da93b0 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z1004 : W := mkw 0x001045844322458b 0x000822c2219122c5 0xff76cd9ccbe3c78f 0xffbb66ce65f1e3c7

def z1005 : W := mkw 0x081005a00db40760 0x040802d006da03b0 0x5b700c000ffc07f0 0x2db8060007fe03f8

def z1006 : W := mkw 0x11effa400edbb000 0x08f7fd20076dd800 0xd3fff2600ffff801 0xe9fff93007fffc00

def z1007 : W := mkw 0x0232d58cc36ad58b 0x81196ac661b56ac5 0xff77fd9ccbe3ff8f 0xffbbfece65f1ffc7

def z1008 : W := mkw 0x2037af5aa0000000 0x101bd7ad50000000 0xbd77fffff0000001 0xdebbfffff8000000

def z1009 : W := mkw 0x29dd0ffaadb40760 0x14ee87fd56da03b0 0xffff0ffffffc07f1 0xffff87fffffe03f8

def z1010 : W := mkw 0x01d805a00db40520 0x00ec02d006da0290 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z1011 : W := mkw 0x29ffaf5aa0200340 0x14ffd7ad501001a0 0xbdfffffff0000381 0xdefffffff80001c0

def z1012 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x52f803e00ffc07f0 0xa97c01f007fe03f8

def z1013 : W := mkw 0x08580fe001b40760 0x042c07f000da03b0 0xfb780fe00bfc07f0 0xfdbc07f005fe03f8

def z1014 : W := mkw 0x29dd2ffaadb40760 0x14ee97fd56da03b0 0xfff93ffffffc07f0 0xfffc9ffffffe03f8

def z1015 : W := mkw 0x09dd0fe00db40760 0x04ee87f006da03b0 0xfbff0fe00ffc07f1 0xfdff87f007fe03f8

def z1016 : W := mkw 0x207aa55aa0000000 0x103d52ad50000000 0x1478f1fff0000000 0x8a3c78fff8000000

def z1017 : W := mkw 0x08100fe001240760 0x040807f0009203b0 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z1018 : W := mkw 0x01efaa1200000000 0x00f7d50900000000 0xbdfffffff0000001 0xdefffffff8000000

def z1019 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x3d77fffff0000001 0x1ebbfffff8000000

def z1020 : W := mkw 0x2227f01ff24ad89f 0x9113f80ff9256c4f 0x0407f01ff003f80f 0x0203f80ff801fc07

def z1021 : W := mkw 0x1232f58cc36ad58b 0x89197ac661b56ac5 0xff76fd9ccbe3c78f 0xffbb7ece65f1e3c7

def z1022 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xed870ffffc03ffff 0x76c387fffe01ffff

def z1023 : W := mkw 0x00005001020a1814 0x0000280081050c0a 0xe689f3e3f71e3c7f 0xf344f9f1fb8f1e3f

def z1024 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xed060c1c0c03ffff 0x7683060e0601ffff

def z1025 : W := mkw 0x31ffaf5aacd1a000 0x18ffd7ad5668d000 0xfdfffffffce3f801 0xfefffffffe71fc00

def z1026 : W := mkw 0x09d80fe05db40763 0x04ec07f02eda03b1 0xfbf80fe0fffc07f0 0xfdfc07f07ffe03f8

def z1027 : W := mkw 0x29ffaf5aac900240 0x14ffd7ad56480120 0xbdfffffff0000001 0xdefffffff8000000

def z1028 : W := mkw 0x1022d0000edbb000 0x08116800076dd800 0xd3fff0000ffff801 0xe9fff80007fffc00

def z1029 : W := mkw 0x21ffaf5aac012000 0x10ffd7ad56009000 0xbdfffffff801c001 0xdefffffffc00e000

def z1030 : W := mkw 0x25cd2a572c016adc 0x12e6952b9600b56e 0xed8ffffffc03ffff 0xf6c7fffffe01ffff

def z1031 : W := mkw 0x0000000000000000 0x0000000000000000 0xad8ffffff0000001 0xd6c7fffff8000000

def z1032 : W := mkw 0x31eff0122edbb000 0x18f7f809176dd800 0xd3fff0033ffff801 0xe9fff8019ffffc00

def z1033 : W := mkw 0x05cd0a130c912a54 0x02e685098648952a 0x00890203041c3870 0x00448101820e1c38

def z1034 : W := mkw 0x09dd0ff20db40760 0x04ee87f906da03b0 0xfbf90fe30ffc07f0 0xfdfc87f187fe03f8

def z1035 : W := mkw 0x106af00002dbb000 0x08357800016dd800 0x1278f00003fff800 0x893c780001fffc00

def z1036 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xd3fff2633ffff801 0xe9fff9319ffffc00

def z1037 : W := mkw 0x0c0050a55fbf7fff 0x06002852afdfbfff 0x420000000ffffffe 0x2100000007ffffff

def z1038 : W := mkw 0x0232858cc160c58b 0x811942c660b062c5 0xfd760d9cc8e3c78f 0x7ebb06ce6471e3c7

def z1039 : W := mkw 0x11efb0000cd9b000 0x08f7d800066cd800 0xd3ff30000ffdf800 0xe9ff980007fefc00

def z1040 : W := mkw 0x0232858cc160c58b 0x811942c660b062c5 0xbd76cd9cc8e1c78f 0xdebb66ce6470e3c7

def z1041 : W := mkw 0x085805e001b40760 0x042c02f000da03b0 0x127801e003fc07f0 0x893c00f001fe03f8

def z1042 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xfffffd9ccbe3c78f 0xfffffece65f1e3c7

def z1043 : W := mkw 0x0232850c8060c188 0x81194286403060c4 0x1d760c1c08e3c38f 0x0ebb060e0471e1c7

def z1044 : W := mkw 0x0022d000024a9000 0x0011680001254800 0xd376c0000ffff801 0xe9bb600007fffc00

def z1045 : W := mkw 0x08580fe00db40760 0x042c07f006da03b0 0x7a780fe00ffc07f0 0xbd3c07f007fe03f8

def z1046 : W := mkw 0x0232c5acc366c5ab 0x811962d661b362d5 0xffffffffffffc7ff 0xffffffffffffe3ff

def z1047 : W := mkw 0x09d80f600cb40360 0x04ec07b0065a01b0 0xdbf80e600ffc03f0 0xedfc073007fe01f8

def z1048 : W := mkw 0x21efaa5aa0000000 0x10f7d52d50000000 0xa48ff3fff0000001 0xd247f9fff8000000

def z1049 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xf7fff2030ffff801 0xfbfff90187fffc00

def z1050 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xd3fff1e0fffff801 0xe9fff8f07ffffc00

def z1051 : W := mkw 0x0232d5acd36ed5ab 0x81196ad669b76ad5 0xff76cd9ccbffc78f 0xffbb66ce65ffe3c7

def z1052 : W := mkw 0x21ffa55aa0000000 0x10ffd2ad50000000 0x95fff1fff0000001 0xcafff8fff8000000

def z1053 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xed8ffe1f0c03ffff 0xf6c7ff0f8601ffff

def z1054 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfbf9ffe00ffc07f1 0xfdfcfff007fe03f8

def z1055 : W := mkw 0x040050a5530e5eff 0x02002852a9872f7f 0x42000000071e3ffe 0x21000000038f1fff

def z1056 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xd7fff003fffff801 0xebfff801fffffc00

def z1057 : W := mkw 0x11a7d0000edbb000 0x08d3e800076dd800 0xd3f7c0000ffff801 0xe9fbe00007fffc00

def z1058 : W := mkw 0x020050a5534edcbf 0x81002852a9a76e5f 0x42000000071ffc7e 0x21000000038ffe3f

def z1059 : W := mkw 0x0222c00cc242c08b 0x8111600661216045 0xff76cc1ccbe3c78f 0xffbb660e65f1e3c7

def z1060 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x3b780fe00bfc07f0 0x9dbc07f005fe03f8

def z1061 : W := mkw 0x0232c5acc366c5ab 0x811962d661b362d5 0xff76cffccbe3c7ff 0xffbb67fe65f1e3ff

def z1062 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xff7efdfcfbe3c78f 0xffbf7efe7df1e3c7

def z1063 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x4289f3e3f71e3c7e 0xa144f9f1fb8f1e3f

def z1064 : W := mkw 0x21ffaf5aac900000 0x10ffd7ad56480000 0xbdfffffff41c0001 0xdefffffffa0e0000

def z1065 : W := mkw 0x11cd50000edbb000 0x08e6a800076dd800 0xd3ff00000ffff801 0xe9ff800007fffc00

def z1066 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xfffecffccbe3c78f 0xffff67fe65f1e3c7

def z1067 : W := mkw 0x2027a01aa0000000 0x1013d00d50000000 0x040ff1fff0000001 0x8207f8fff8000000

def z1068 : W := mkw 0x31ffaf5aacd1a000 0x18ffd7ad5668d000 0xfffffffffffdc001 0xfffffffffffee000

def z1069 : W := mkw 0x09d805e00db40760 0x04ec02f006da03b0 0xd3f801e00ffc07f0 0xe9fc00f007fe03f8

def z1070 : W := mkw 0x0232850c8060c188 0x81194286403060c4 0x59760c1c08e3c78e 0x2cbb060e0471e3c7

def z1071 : W := mkw 0x002280040040c088 0x0011400200206044 0xfd760c1c08e3c78f 0x7ebb060e0471e3c7

def z1072 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfbf00e000ffc07f0 0x7df8070007fe03f8

def z1073 : W := mkw 0x0bd80fe8cdb40763 0x85ec07f466da03b1 0xfbf80fe0cffc07f0 0xfdfc07f067fe03f8

def z1074 : W := mkw 0x09d80f400cb00340 0x04ec07a0065801a0 0xfbf80e000ffc07f0 0xfdfc070007fe03f8

def z1075 : W := mkw 0x09d80fe001b40760 0x04ec07f000da03b0 0xbbf80fe003fc07f0 0xddfc07f001fe03f8

def z1076 : W := mkw 0x11eff0005edbb003 0x08f7f8002f6dd801 0xd3fff000fffff801 0xe9fff8007ffffc00

def z1077 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfb700d800ffc07f0 0xfdb806c007fe03f8

def z1078 : W := mkw 0x11eaf0000edbb000 0x08f57800076dd800 0xd3f8f0000ffff800 0xe9fc780007fffc00

def z1079 : W := mkw 0x0a32c5ecc366c5ab 0x851962f661b362d5 0xff76cdfccbe3c78f 0xffbb66fe65f1e3c7

def z1080 : W := mkw 0x0a7ad5e8d3fe9523 0x853d6af469ff4a91 0x1278f1e0f3fc0000 0x893c78f079fe0000

def z1081 : W := mkw 0x25ffaf5aac012240 0x12ffd7ad56009120 0xbdfffffff0000001 0xdefffffff8000000

def z1082 : W := mkw 0x1027f000024bb000 0x0813f8000125d800 0xd3fff0000ffff801 0xe9fff80007fffc00

def z1083 : W := mkw 0x25cd2a572c016adc 0x12e6952b9600b56e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z1084 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0x12fff00007fff801 0x897ff80003fffc00

def z1085 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfbf8ffe0fffc07f0 0xfdfc7ff07ffe03f8

def z1086 : W := mkw 0x0232c50cc262c18b 0x81196286613160c5 0xbd76cd9cc8e3c38f 0xdebb66ce6471e1c7

def z1087 : W := mkw 0x106ff00002dbb000 0x0837f800016dd800 0xd37ff0000bfff801 0xe9bff80005fffc00

def z1088 : W := mkw 0x21dd2f5aa0000000 0x10ee97ad50000000 0xac89fffff0000001 0xd644fffff8000000

def z1089 : W := mkw 0x11effa000edbb240 0x08f7fd00076dd920 0xdbfffc000ffffb81 0xedfffe0007fffdc0

def z1090 : W := mkw 0x000050a5530e5cbf 0x00002852a9872e5f 0x420000000f1ffffe 0x21000000078fffff

def z1091 : W := mkw 0x085805e00db40760 0x042c02f006da03b0 0xfb780de00ffc07f0 0xfdbc06f007fe03f8

def z1092 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0xdb76cc1c0be3c78f 0xedbb660e05f1e3c7

def z1093 : W := mkw 0x31effa1aaedbb000 0x18f7fd0d576dd800 0xfffffe1ffffff801 0xffffff0ffffffc00

def z1094 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xed87cf9fcc03ffff 0xf6c3e7cfe601ffff

def z1095 : W := mkw 0x040500170001689c 0x0202800b8000b44e 0xed870e1f0c03ffff 0x76c3870f8601ffff

def z1096 : W := mkw 0x09900fa00db40760 0x04c807d006da03b0 0xfbf00f800ffc07f0 0xfdf807c007fe03f8

def z1097 : W := mkw 0x000050a1532e1d37 0x00002850a9970e9b 0xe689f3e3fffe3fff 0xf344f9f1ffff1fff

def z1098 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfbfe0fe00fffc7f1 0xfdff07f007ffe3f8

def z1099 : W := mkw 0x00001021100c1834 0x0000081088060c1a 0xe489f3e3f41e3c7f 0xf244f9f1fa0f1e3f

def z1100 : W := mkw 0x09dd0fe00db52760 0x04ee87f006da93b0 0xfbfe0fe00ffdc7f0 0xfdff07f007fee3f8

def z1101 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x3af80fe007fc07f0 0x9d7c07f003fe03f8

def z1102 : W := mkw 0x1627f01fc24bf89f 0x8b13f80fe125fc4f 0x0407f01fc003f80f 0x0203f80fe001fc07

def z1103 : W := mkw 0x0232c5acd366c5ab 0x811962d669b362d5 0xff76cdfcfbe3c78f 0xffbb66fe7df1e3c7

def z1104 : W := mkw 0x01d80f400c900240 0x00ec07a006480120 0xfbf80fe00ffc07f0 0xfdfc07f007fe03f8

def z1105 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x5f76cc1ccbe3c78f 0x2fbb660e65f1e3c7

def z1106 : W := mkw 0x21ffaf5aa0000000 0x10ffd7ad50000000 0x14fff3fff0000001 0x8a7ff9fff8000000

def z1107 : W := mkw 0x000050a1530e1c37 0x00002850a9870e1b 0x2689f3e3f71c3c7e 0x9344f9f1fb8e1e3f

def z1108 : W := mkw 0x31eff0402edbb000 0x18f7f820176dd800 0xd3fff0603ffff801 0xe9fff8301ffffc00

def z1109 : W := mkw 0x11eff0088edbb000 0x08f7f804476dd800 0xd7fff01ccffff801 0xebfff80e67fffc00

def z1110 : W := mkw 0x0210058cc120458b 0x810802c6609022c5 0xff760d9ccbe3c78f 0xffbb06ce65f1e3c7

def z1111 : W := mkw 0x0232c50cc262c18b 0x81196286613160c5 0xdf76cc1ccbe3c38f 0xefbb660e65f1e1c7

def z1112 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0x5b780de00ffc07f0 0xadbc06f007fe03f8

def z1113 : W := mkw 0x09c80ae00db40760 0x04e4057006da03b0 0xd3f802600ffc07f0 0xe9fc013007fe03f8

def z1114 : W := mkw 0x207fa55aa0000000 0x103fd2ad50000000 0xb4fff3fff0000001 0xda7ff9fff8000000

def z1115 : W := mkw 0x09c800a00db40760 0x04e4005006da03b0 0xf3f803e00ffc07f0 0xf9fc01f007fe03f8

def z1116 : W := mkw 0x021005add1244dbf 0x810802d6e89226df 0x2c000d9cc00007fe 0x160006ce600003ff

def z1117 : W := mkw 0x207fa55aa0000000 0x103fd2ad50000000 0xbd7ffdfff0000001 0xdebffefff8000000

def z1118 : W := mkw 0x0232d5acc36ed5ab 0x81196ad661b76ad5 0xfffffffccfffffff 0xfffffffe67ffffff

def z1119 : W := mkw 0x11a7fa000e4bb240 0x08d3fd000725d920 0xe987fe000c03fff1 0x74c3ff000601fff8

def z1120 : W := mkw 0x35ffaf5eacd1e2c8 0x1affd7af5668f164 0x19760c1c08e1c380 0x0cbb060e0470e1c0

def z1121 : W := mkw 0x05850a170c016adc 0x02c2850b8600b56e 0xfff70e1f0fe3ffff 0xfffb870f87f1ffff

def z1122 : W := mkw 0x000050a1534e9c37 0x00002850a9a74e1b 0xe689f3e3fffffc7f 0xf344f9f1fffffe3f

def z1123 : W := mkw 0x106af0000edbb000 0x08357800076dd800 0xd37ef0000ffff801 0xe9bf780007fffc00

def z1124 : W := mkw 0x0232c58cc362c58b 0x811962c661b162c5 0x1f76cd9ccbe3c38f 0x8fbb66ce65f1e1c7

def z1125 : W := mkw 0x01850a040c0162c8 0x00c285020600b164 0xed870e1c0c03ffff 0x76c3870e0601ffff

def z1126 : W := mkw 0x29dd2ff22db40760 0x14ee97f916da03b0 0xfff9ffe3fffc07f1 0xfffcfff1fffe03f8

def z1127 : W := mkw 0x04050a170c016adc 0x0202850b8600b56e 0x6c070e1f0c03ffff 0x3603870f8601ffff

def z1128 : W := mkw 0x2000001aa0000000 0x1000000d50000000 0xa489f3fff0000001 0xd244f9fff8000000

def z1129 : W := mkw 0x11eff0000edbb000 0x08f7f800076dd800 0xf3fff3e00ffff801 0xf9fff9f007fffc00

def z1130 : W := mkw 0x31eff008aedbb000 0x18f7f804576dd800 0xd3fff000fffff801 0xe9fff8007ffffc00

def z1131 : W := mkw 0x09d80fe00db40760 0x04ec07f006da03b0 0xfbf90fe00ffe3ff1 0xfdfc87f007ff1ff8

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z5,z8,z6]),(0,[z7,z1,z2,z3,z9,z5,z6])],[(0,[z10,z7,z1,z2,z3,z5,z6]),(0,[z11,z7,z1,z2,z3,z5,z6]),(0,[z12,z13,z7,z1,z3,z5,z6]),(0,[z7,z14,z1,z2,z3,z5,z6]),(0,[z7,z15,z1,z2,z3,z5,z6])],[(0,[z16,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z17,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z18,z6]),(0,[z7,z1,z2,z3,z5,z6,z19]),(0,[z7,z20,z21,z2,z3,z5,z6]),(0,[z7,z1,z2,z22,z3,z5,z6])],[(0,[z23,z7,z1,z24,z3,z5,z6]),(0,[z25,z7,z26,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z5,z27]),(0,[z7,z28,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z29,z6]),(0,[z30,z7,z1,z2,z3,z5,z6]),(1,[z7,z31,z1,z2,z5,z6])],[(0,[z32,z7,z33,z2,z3,z5,z6]),(0,[z34,z7,z1,z2,z3,z5,z6]),(1,[z7,z14,z2,z35,z5,z6])],[(0,[z7,z1,z2,z3,z5,z6,z36])],[(0,[z7,z37,z1,z2,z3,z5,z6]),(0,[z7,z1,z38,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z39,z6]),(0,[z7,z1,z2,z40,z3,z5,z6]),(0,[z7,z1,z41,z2,z3,z42,z6]),(0,[z7,z1,z2,z3,z5,z43,z6]),(0,[z7,z1,z2,z44,z3,z5,z6])],[(0,[z7,z45,z21,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z5,z46]),(0,[z47,z7,z48,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z49,z6]),(0,[z7,z1,z2,z3,z5,z6,z50]),(0,[z7,z51,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z52,z6])]],
   [[(0,[z23,z7,z1,z53,z3,z5,z6]),(1,[z25,z1,z2,z54,z5,z6]),(0,[z7,z1,z2,z3,z5,z55,z6])],[(0,[z7,z1,z2,z3,z5,z56,z6]),(0,[z7,z1,z2,z3,z5,z57,z6]),(0,[z7,z1,z2,z3,z58,z4,z6]),(0,[z59,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z60,z3,z5,z61,z6]),(0,[z7,z1,z62,z2,z3,z5,z6])],[(0,[z7,z33,z2,z3,z5,z63,z6]),(0,[z7,z1,z2,z5,z64,z6,z65])],[(1,[z7,z66,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z46]),(0,[z7,z1,z2,z3,z4,z6,z67]),(0,[z7,z1,z2,z68,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z69,z6])],[(0,[z7,z1,z2,z3,z5,z70,z6]),(0,[z7,z1,z2,z71,z3,z5,z6]),(0,[z7,z1,z72,z2,z3,z5,z6]),(0,[z73,z7,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z74,z3,z5,z6]),(0,[z75,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z76,z6]),(0,[z1,z2,z3,z5,z77,z6,z78]),(0,[z7,z1,z2,z3,z5,z6,z79])],[(0,[z7,z1,z2,z3,z5,z6,z80]),(0,[z7,z1,z2,z3,z5,z81,z6]),(0,[z7,z82,z1,z2,z3,z5,z83]),(0,[z7,z84,z1,z2,z3,z5,z6]),(0,[z7,z85,z1,z2,z3,z5,z6])],[(0,[z12,z23,z1,z2,z3,z5,z6]),(0,[z86,z7,z1,z2,z3,z5,z6]),(0,[z25,z7,z1,z2,z87,z5,z6]),(0,[z88,z7,z1,z2,z87,z5,z6]),(0,[z89,z7,z90,z1,z2,z3,z6]),(0,[z7,z1,z2,z3,z5,z77,z6]),(0,[z91,z7,z1,z2,z3,z5,z92])]],
   [[(0,[z93,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z94,z6]),(0,[z7,z95,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z96])],[(0,[z7,z1,z2,z87,z5,z6,z65]),(0,[z7,z1,z2,z97,z87,z5,z6]),(0,[z7,z90,z1,z2,z3,z5,z6]),(0,[z7,z1,z98,z3,z5,z99,z6]),(0,[z7,z82,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z100,z5,z6]),(0,[z7,z1,z2,z3,z5,z101,z6])],[(0,[z7,z102,z21,z2,z3,z5,z6]),(0,[z7,z103,z1,z2,z3,z5,z6]),(0,[z7,z90,z1,z2,z3,z58,z6]),(0,[z7,z104,z1,z2,z3,z105,z6]),(0,[z7,z1,z41,z2,z3,z5,z6]),(0,[z7,z106,z1,z2,z3,z5,z107])],[(0,[z7,z1,z2,z3,z5,z6,z108]),(0,[z7,z1,z2,z3,z5,z109,z6]),(0,[z7,z1,z2,z110,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z111,z6])],[(0,[z7,z1,z2,z3,z5,z112,z6]),(0,[z7,z1,z2,z3,z5,z6,z113]),(0,[z7,z14,z1,z2,z114,z5,z6]),(0,[z7,z1,z2,z3,z115,z5,z6]),(0,[z7,z116,z2,z3,z105,z5,z6])],[(0,[z7,z117,z1,z45,z2,z3,z6]),(0,[z7,z1,z2,z3,z5,z118,z6]),(0,[z7,z1,z2,z119,z3,z5,z6]),(0,[z120,z7,z1,z2,z3,z5,z6]),(1,[z7,z1,z2,z121,z5,z6])],[(0,[z7,z1,z2,z54,z5,z6,z65]),(0,[z7,z1,z2,z3,z122,z5,z6]),(0,[z7,z1,z2,z3,z123,z5,z6]),(1,[z7,z1,z2,z124,z5,z6]),(0,[z7,z1,z125,z2,z3,z5,z6])],[(0,[z7,z126,z1,z2,z3,z5,z6]),(1,[z7,z1,z2,z127,z128,z6])]],
   [[(0,[z129,z7,z1,z2,z3,z5,z6]),(0,[z7,z130,z1,z2,z3,z5,z6]),(0,[z7,z131,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z132,z6]),(0,[z7,z133,z1,z41,z2,z3,z6]),(0,[z7,z1,z134,z2,z3,z5,z83])],[(0,[z23,z7,z66,z2,z3,z5,z6])],[(0,[z7,z135,z1,z2,z3,z5,z6]),(0,[z7,z82,z1,z3,z5,z6,z136]),(0,[z7,z1,z2,z3,z5,z6,z137])],[(1,[z138,z7,z1,z3,z5,z6]),(0,[z7,z1,z139,z2,z3,z5,z6]),(0,[z7,z1,z98,z2,z128,z5,z6]),(0,[z7,z106,z1,z2,z124,z5,z6]),(0,[z7,z1,z134,z2,z3,z5,z6])],[(0,[z0,z7,z1,z2,z3,z140,z6])],[(0,[z7,z1,z2,z141,z3,z5,z6]),(0,[z7,z1,z2,z142,z3,z5,z6]),(1,[z7,z143,z21,z3,z5,z6]),(0,[z7,z144,z1,z2,z3,z5,z6]),(0,[z7,z20,z1,z2,z3,z145,z6]),(0,[z7,z1,z2,z3,z5,z6,z146]),(0,[z7,z1,z2,z3,z128,z42,z6]),(1,[z7,z147,z1,z2,z5,z65]),(1,[z7,z1,z2,z3,z58,z92])],[(0,[z7,z148,z1,z2,z3,z5,z6]),(0,[z149,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z150,z3,z5,z6]),(0,[z7,z1,z2,z151,z3,z5,z6]),(0,[z7,z1,z2,z127,z152,z5,z6])],[(0,[z7,z1,z153,z2,z3,z5,z6]),(0,[z7,z1,z2,z152,z3,z5,z6])]],
   [[(0,[z7,z1,z2,z3,z154,z5,z6]),(0,[z7,z1,z2,z155,z3,z5,z6]),(0,[z7,z1,z2,z3,z140,z6,z67]),(0,[z7,z133,z1,z2,z3,z128,z6]),(0,[z156,z7,z1,z2,z3,z5,z6])],[(0,[z7,z157,z1,z2,z3,z5,z6]),(0,[z7,z106,z1,z2,z3,z42,z6])],[(0,[z7,z33,z1,z2,z3,z5,z6]),(0,[z158,z7,z1,z2,z3,z5,z6]),(0,[z7,z159,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z160]),(1,[z7,z1,z2,z3,z161,z6]),(0,[z7,z1,z2,z3,z58,z5,z92])],[(0,[z162,z7,z1,z2,z3,z5,z6]),(1,[z7,z2,z3,z163,z5,z6])],[(0,[z25,z7,z1,z2,z54,z5,z6]),(0,[z88,z7,z1,z2,z54,z5,z6]),(0,[z47,z7,z1,z164,z3,z5,z6])],[(0,[z7,z1,z2,z128,z5,z101,z6]),(0,[z7,z165,z1,z2,z3,z5,z92])],[(0,[z7,z1,z2,z97,z54,z5,z6]),(0,[z7,z1,z2,z3,z5,z166,z6])],[(0,[z7,z143,z1,z134,z3,z5,z6]),(0,[z167,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z136,z67]),(0,[z7,z1,z2,z3,z5,z168,z6]),(0,[z7,z1,z2,z3,z5,z6,z169])]],
   [[(1,[z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z170]),(0,[z7,z1,z2,z171,z3,z5,z6]),(0,[z7,z172,z2,z3,z5,z6,z173]),(0,[z7,z1,z2,z3,z174,z5,z6]),(0,[z7,z1,z175,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z176,z6])],[(0,[z177,z7,z1,z2,z3,z5,z6]),(0,[z7,z133,z1,z178,z3,z5,z6]),(0,[z7,z1,z2,z3,z128,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z179])],[(1,[z7,z1,z2,z3,z180,z6]),(0,[z181,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z92,z83]),(0,[z7,z1,z2,z121,z5,z92,z6])],[(0,[z7,z1,z182,z2,z3,z5,z6]),(0,[z7,z1,z134,z24,z3,z5,z6]),(0,[z183,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z184,z6]),(0,[z7,z1,z2,z3,z5,z27,z6]),(0,[z7,z1,z185,z2,z3,z5,z6]),(0,[z7,z186,z1,z2,z3,z5,z6])],[(0,[z7,z187,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z6]),(0,[z7,z1,z2,z188,z3,z5,z6])],[(0,[z189,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z190,z6]),(0,[z7,z191,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z192]),(0,[z193,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z194,z3,z5,z6]),(0,[z7,z106,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z92,z6])],[(0,[z13,z7,z33,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z195,z6]),(0,[z7,z1,z2,z3,z196,z5,z6]),(0,[z7,z1,z2,z3,z197,z5,z6]),(0,[z7,z14,z1,z2,z97,z5,z6]),(0,[z7,z1,z2,z3,z58,z5,z6]),(0,[z7,z1,z2,z121,z3,z5,z6])],[(0,[z7,z1,z2,z3,z198,z5,z6]),(0,[z7,z1,z2,z3,z42,z101,z6])]],
   [[(0,[z199,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z134,z53,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z200,z6]),(0,[z7,z1,z2,z3,z99,z6,z67]),(0,[z7,z133,z1,z2,z5,z6,z65]),(0,[z7,z1,z2,z127,z3,z6,z67])],[(0,[z32,z7,z45,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z201,z6]),(0,[z7,z133,z1,z98,z2,z5,z6]),(0,[z7,z202,z1,z2,z3,z5,z6]),(1,[z7,z1,z178,z3,z5,z6])],[(0,[z7,z1,z2,z3,z203,z5,z6]),(0,[z89,z7,z1,z2,z3,z140,z6]),(0,[z7,z1,z2,z3,z204,z5,z6]),(1,[z7,z1,z205,z3,z5,z6]),(0,[z7,z90,z1,z2,z3,z6,z67]),(0,[z7,z1,z41,z3,z105,z5,z6]),(0,[z7,z1,z98,z2,z152,z5,z6]),(0,[z7,z1,z2,z206,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z140,z6]),(0,[z7,z207,z1,z2,z3,z5,z6]),(0,[z7,z2,z35,z3,z114,z5,z6]),(0,[z7,z208,z1,z2,z105,z5,z6]),(0,[z7,z1,z2,z97,z105,z5,z6]),(0,[z7,z1,z2,z3,z5,z83,z65]),(0,[z7,z1,z2,z3,z5,z209,z6]),(0,[z7,z1,z2,z3,z210,z5,z6])],[(0,[z47,z7,z1,z2,z211,z5,z6]),(0,[z7,z1,z212,z2,z3,z5,z6]),(0,[z7,z213,z1,z2,z3,z5,z6])],[(0,[z7,z1,z214,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z61,z6])],[(0,[z23,z7,z1,z2,z3,z5,z6]),(0,[z7,z215,z1,z2,z3,z5,z6]),(0,[z7,z216,z1,z2,z3,z5,z6]),(0,[z217,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z218,z6])],[(0,[z7,z219,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z220]),(0,[z7,z1,z2,z3,z221,z5,z6]),(0,[z7,z1,z2,z3,z163,z5,z6])]],
   [[(0,[z7,z222,z1,z2,z3,z5,z6]),(0,[z7,z102,z1,z2,z35,z5,z6]),(1,[z7,z20,z2,z3,z63,z6]),(0,[z7,z1,z2,z3,z5,z223,z6])],[(0,[z7,z1,z2,z3,z5,z224,z6]),(1,[z88,z1,z2,z87,z5,z6]),(0,[z225,z7,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z5,z6]),(0,[z7,z172,z226,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z61,z6,z227]),(0,[z7,z208,z1,z2,z3,z52,z6]),(0,[z7,z133,z1,z2,z3,z101,z6])],[(0,[z7,z1,z2,z228,z3,z5,z6]),(0,[z7,z1,z2,z3,z229,z5,z6]),(0,[z7,z1,z2,z3,z230,z5,z6]),(0,[z7,z1,z2,z3,z231,z5,z6])],[(0,[z7,z1,z2,z3,z232,z5,z6])],[(0,[z7,z1,z2,z3,z233,z5,z6])],[(1,[z7,z234,z1,z2,z3,z6]),(0,[z7,z235,z1,z2,z3,z5,z6]),(0,[z91,z7,z172,z1,z2,z3,z5]),(0,[z7,z90,z1,z2,z3,z63,z6]),(0,[z7,z1,z2,z3,z5,z6,z236])],[(0,[z7,z1,z2,z3,z5,z237,z6])]],
   [[(0,[z7,z1,z2,z3,z5,z238,z6]),(0,[z7,z1,z2,z3,z5,z6,z239]),(0,[z7,z1,z2,z3,z240,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z241]),(0,[z7,z1,z2,z3,z5,z242,z6])],[(0,[z243,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z244,z6]),(0,[z7,z245,z1,z2,z3,z5,z6]),(0,[z13,z7,z1,z246,z3,z5,z6])],[(0,[z7,z1,z2,z247,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z248]),(1,[z7,z1,z2,z3,z249,z6]),(0,[z7,z1,z2,z3,z5,z92,z65]),(0,[z7,z1,z250,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z251,z5,z6]),(0,[z7,z1,z2,z3,z252,z5,z6]),(0,[z7,z1,z2,z253,z3,z5,z6]),(0,[z47,z7,z254,z2,z3,z5,z6]),(0,[z7,z133,z1,z2,z5,z101,z6])],[(0,[z7,z1,z2,z87,z3,z5,z6]),(0,[z7,z1,z2,z255,z3,z5,z6]),(0,[z7,z1,z2,z3,z114,z5,z6]),(0,[z7,z1,z2,z3,z5,z256,z6]),(0,[z7,z1,z2,z257,z3,z5,z6])],[(0,[z258,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z259,z2,z53,z3,z5]),(0,[z7,z260,z1,z2,z3,z5,z6]),(0,[z261,z7,z1,z2,z3,z5,z6]),(0,[z262,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z263,z2,z3,z5,z6]),(0,[z7,z31,z1,z2,z5,z99,z6])],[(0,[z7,z1,z264,z45,z3,z5,z6]),(0,[z7,z265,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z266,z6])],[(0,[z7,z1,z53,z3,z5,z6,z136]),(1,[z7,z1,z2,z3,z267,z6]),(0,[z7,z143,z1,z2,z3,z5,z6]),(0,[z7,z1,z268,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z269,z5,z6])]],
   [[(0,[z91,z7,z1,z2,z3,z5,z77]),(0,[z7,z1,z2,z270,z3,z5,z6]),(0,[z7,z271,z1,z2,z3,z5,z6]),(1,[z7,z1,z134,z3,z5,z83])],[(0,[z272,z7,z1,z2,z3,z5,z6])],[(0,[z7,z273,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z274,z3,z5,z6])],[(1,[z7,z1,z2,z3,z174,z6]),(0,[z7,z2,z3,z5,z275,z99,z6])],[(0,[z276,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z277,z3,z5,z6]),(0,[z278,z7,z1,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z5,z279]),(0,[z280,z7,z1,z2,z3,z5,z6])],[(0,[z13,z7,z1,z21,z3,z5,z6]),(0,[z281,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z282,z6]),(0,[z7,z1,z2,z3,z5,z6,z283])],[(0,[z7,z1,z2,z3,z5,z284,z6]),(0,[z7,z208,z1,z2,z3,z5,z279])],[(0,[z32,z7,z1,z2,z3,z5,z6]),(0,[z285,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z286,z6]),(0,[z7,z1,z2,z3,z249,z61,z6])]],
   [[(0,[z7,z143,z1,z3,z5,z6,z136]),(0,[z7,z1,z2,z277,z5,z61,z6]),(0,[z7,z1,z2,z3,z5,z6,z279]),(1,[z7,z1,z2,z3,z5,z107]),(0,[z7,z287,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z288,z3,z5,z6])],[(0,[z7,z1,z2,z289,z3,z5,z6])],[(0,[z7,z226,z33,z2,z3,z5,z6]),(0,[z7,z1,z290,z2,z3,z5,z6]),(0,[z7,z291,z1,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z5,z292]),(1,[z7,z1,z2,z293,z5,z6]),(0,[z7,z133,z1,z2,z127,z5,z6])],[(0,[z7,z45,z2,z3,z114,z5,z6]),(0,[z7,z294,z1,z2,z53,z3,z5]),(0,[z295,z7,z1,z2,z3,z5,z6])],[(0,[z7,z1,z296,z2,z3,z5,z6]),(0,[z297,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z298]),(0,[z7,z1,z2,z3,z249,z5,z6])],[(0,[z1,z2,z87,z3,z54,z5,z6]),(0,[z7,z1,z2,z128,z5,z6,z65])],[(0,[z7,z1,z2,z3,z5,z6,z299]),(0,[z300,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z301,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z292])],[(1,[z7,z302,z2,z3,z5,z6]),(0,[z7,z1,z2,z303,z3,z5,z6]),(0,[z7,z1,z2,z3,z304,z5,z6]),(1,[z7,z1,z2,z3,z305,z6]),(0,[z7,z106,z1,z2,z3,z5,z292]),(0,[z7,z1,z2,z3,z306,z5,z6])]],
   [[(0,[z47,z7,z172,z1,z2,z3,z5]),(0,[z7,z1,z307,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z42,z5,z6]),(0,[z7,z1,z2,z3,z308,z5,z6]),(0,[z7,z1,z2,z3,z5,z64,z136]),(0,[z7,z1,z2,z3,z161,z64,z6])],[(0,[z7,z1,z309,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z267,z6]),(0,[z7,z1,z2,z3,z305,z5,z6]),(0,[z7,z1,z2,z310,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z311,z6]),(0,[z7,z1,z2,z3,z5,z6,z312])],[(0,[z7,z1,z313,z2,z3,z5,z6]),(0,[z7,z208,z1,z98,z3,z5,z6]),(0,[z7,z1,z3,z105,z5,z99,z6])],[(0,[z7,z1,z314,z2,z3,z5,z6]),(0,[z7,z315,z1,z2,z3,z5,z6]),(0,[z13,z7,z20,z2,z3,z5,z6]),(0,[z7,z1,z2,z246,z3,z5,z6]),(0,[z7,z1,z2,z3,z316,z5,z6])],[(0,[z7,z1,z2,z317,z3,z5,z6]),(0,[z7,z1,z2,z3,z145,z5,z6])],[(0,[z91,z7,z1,z2,z3,z5,z6]),(0,[z7,z102,z2,z3,z114,z5,z6]),(0,[z7,z106,z1,z3,z5,z99,z6])],[(0,[z7,z148,z1,z45,z2,z3,z5]),(1,[z7,z1,z60,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z318,z6])]],
   [[(0,[z7,z1,z2,z319,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z320,z6]),(0,[z321,z7,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z322,z6]),(0,[z7,z1,z45,z2,z3,z5,z6]),(0,[z7,z323,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z324,z5,z6]),(0,[z325,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z326,z6]),(0,[z7,z327,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z83,z6]),(0,[z328,z7,z1,z2,z3,z5,z6])],[(1,[z12,z1,z53,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z329]),(0,[z7,z1,z66,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z330]),(0,[z47,z7,z1,z2,z3,z5,z77]),(0,[z7,z82,z1,z2,z331,z5,z6])],[(0,[z7,z332,z1,z2,z3,z5,z6]),(1,[z7,z172,z2,z3,z5,z173]),(0,[z7,z133,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z333])],[(1,[z23,z1,z24,z3,z5,z6]),(0,[z334,z7,z1,z2,z3,z5,z6]),(0,[z7,z335,z1,z2,z3,z5,z6]),(0,[z7,z336,z1,z2,z3,z5,z6]),(0,[z7,z133,z1,z2,z3,z58,z6]),(0,[z7,z1,z337,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z58,z92,z6])],[(0,[z7,z1,z2,z3,z5,z338,z6]),(0,[z7,z208,z1,z2,z128,z5,z6]),(0,[z7,z1,z152,z3,z105,z5,z6]),(0,[z7,z1,z2,z3,z58,z42,z6]),(0,[z339,z7,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z6,z340]),(0,[z7,z102,z1,z2,z5,z6,z65]),(0,[z7,z1,z2,z5,z341,z99,z6])],[(0,[z7,z1,z2,z3,z5,z63,z6]),(1,[z7,z226,z2,z3,z5,z61]),(0,[z7,z1,z2,z3,z5,z6,z342]),(0,[z7,z1,z2,z5,z92,z6,z343])]],
   [[(0,[z344,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z345,z6]),(0,[z7,z1,z60,z2,z3,z5,z6]),(1,[z7,z1,z98,z152,z5,z6])],[(0,[z346,z7,z45,z2,z3,z5,z6]),(0,[z347,z7,z1,z2,z3,z5,z6])],[(0,[z89,z7,z348,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z58,z140,z6]),(0,[z91,z7,z1,z2,z3,z5,z78]),(0,[z7,z349,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z350,z3,z5,z6]),(0,[z7,z1,z2,z3,z351,z5,z6]),(0,[z7,z352,z1,z2,z3,z5,z6])],[(0,[z25,z7,z1,z2,z3,z5,z6]),(0,[z88,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z98,z152,z3,z5,z6])],[(0,[z47,z7,z1,z2,z3,z5,z92]),(0,[z7,z82,z1,z2,z3,z353,z6])],[(0,[z7,z208,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z97,z3,z5,z6])],[(0,[z7,z354,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z355]),(0,[z7,z1,z2,z3,z5,z92,z64])],[(0,[z138,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z356]),(0,[z7,z357,z1,z2,z3,z5,z6]),(0,[z7,z358,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z359,z6]),(0,[z7,z360,z1,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z6,z236]),(0,[z7,z1,z2,z3,z5,z361,z6])]],
   [[(1,[z7,z1,z264,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z362,z6]),(0,[z7,z106,z133,z1,z2,z3,z6])],[(0,[z7,z1,z2,z363,z3,z5,z6]),(0,[z364,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z365,z6]),(0,[z7,z1,z366,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z367]),(0,[z7,z1,z2,z3,z5,z368,z6]),(0,[z7,z1,z2,z3,z5,z6,z369])],[(0,[z12,z7,z143,z1,z3,z5,z6]),(0,[z370,z7,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z371,z5,z6]),(0,[z7,z14,z33,z2,z3,z5,z6]),(0,[z91,z7,z1,z2,z3,z5,z65]),(0,[z7,z372,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z373,z6]),(0,[z7,z1,z2,z3,z5,z6,z374]),(0,[z375,z7,z1,z2,z3,z5,z6]),(0,[z7,z165,z1,z2,z3,z5,z6])],[(0,[z138,z7,z1,z45,z3,z5,z6]),(0,[z7,z147,z1,z2,z3,z5,z6]),(0,[z7,z165,z1,z2,z3,z58,z6])],[(0,[z25,z7,z102,z1,z2,z5,z6]),(0,[z88,z7,z102,z1,z2,z5,z6]),(0,[z7,z1,z2,z3,z376,z5,z6])],[(0,[z7,z1,z2,z3,z377,z5,z6]),(0,[z378,z7,z1,z2,z3,z5,z6]),(0,[z7,z379,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z380,z5,z6]),(0,[z7,z1,z3,z5,z83,z6,z136]),(0,[z7,z1,z2,z3,z5,z6,z381])]],
   [[(0,[z346,z32,z1,z2,z3,z5,z6]),(0,[z47,z7,z1,z2,z3,z5,z6]),(0,[z13,z7,z2,z35,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z6,z220]),(0,[z13,z7,z102,z2,z3,z5,z6]),(0,[z7,z172,z1,z2,z3,z5,z61]),(1,[z7,z1,z2,z331,z5,z6])],[(0,[z47,z7,z1,z2,z3,z180,z6]),(0,[z91,z7,z82,z1,z2,z3,z5]),(0,[z7,z1,z2,z3,z382,z5,z6]),(0,[z7,z1,z2,z3,z383,z5,z6])],[(0,[z7,z1,z164,z2,z3,z5,z6]),(0,[z7,z172,z1,z2,z3,z5,z173]),(0,[z7,z384,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z385,z5,z6]),(0,[z7,z386,z1,z2,z3,z5,z6])],[(0,[z13,z23,z7,z1,z3,z5,z6]),(0,[z7,z387,z1,z2,z3,z5,z6]),(0,[z7,z388,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z389]),(0,[z7,z1,z2,z3,z390,z5,z6])],[(0,[z7,z1,z391,z2,z3,z5,z6]),(0,[z7,z392,z1,z2,z3,z5,z6])],[(0,[z7,z1,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z393,z6])]],
   [[(1,[z346,z33,z2,z3,z5,z6]),(0,[z7,z394,z1,z2,z3,z5,z6]),(0,[z7,z1,z395,z2,z3,z5,z6]),(0,[z7,z1,z396,z2,z3,z5,z6]),(1,[z7,z1,z41,z3,z42,z6])],[(0,[z7,z1,z2,z397,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z398]),(0,[z7,z1,z2,z3,z399,z5,z6]),(0,[z7,z1,z2,z3,z5,z400,z6])],[(0,[z23,z7,z143,z1,z3,z5,z6]),(0,[z0,z7,z20,z1,z2,z3,z6]),(0,[z7,z1,z2,z3,z4,z5,z27]),(0,[z47,z7,z1,z205,z3,z5,z6]),(0,[z7,z1,z2,z3,z401,z5,z6]),(0,[z7,z1,z2,z3,z331,z5,z6]),(0,[z7,z402,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z97,z3,z5,z65]),(0,[z7,z403,z1,z2,z3,z5,z6])],[(0,[z7,z1,z264,z2,z3,z5,z6]),(0,[z7,z90,z33,z2,z3,z5,z6]),(0,[z7,z1,z2,z404,z3,z5,z6]),(0,[z7,z1,z2,z405,z3,z5,z6]),(1,[z7,z2,z3,z5,z275,z6])],[(0,[z7,z1,z2,z3,z5,z406,z6]),(0,[z47,z7,z1,z2,z3,z5,z78]),(1,[z7,z271,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z407,z5,z6])],[(0,[z7,z234,z1,z45,z2,z3,z6]),(0,[z7,z1,z2,z3,z5,z6,z408]),(0,[z7,z1,z2,z105,z5,z101,z6]),(1,[z7,z104,z1,z2,z3,z6]),(0,[z7,z1,z2,z3,z5,z409,z6]),(0,[z7,z147,z1,z2,z5,z6,z65])],[(0,[z410,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z411,z3,z5,z6]),(0,[z7,z412,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z413,z3,z5,z6]),(0,[z7,z414,z1,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z5,z209]),(0,[z7,z1,z2,z415,z3,z5,z6])],[(0,[z346,z7,z1,z2,z3,z5,z6]),(0,[z1,z24,z2,z53,z3,z5,z6]),(0,[z91,z7,z226,z1,z2,z3,z5])]],
   [[(1,[z7,z416,z1,z2,z5,z6])],[(0,[z7,z20,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z417,z6]),(0,[z7,z1,z2,z3,z5,z6,z418]),(0,[z7,z1,z2,z127,z3,z128,z6])],[(0,[z7,z1,z419,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z420,z5,z6]),(0,[z7,z1,z2,z3,z5,z421,z6]),(0,[z7,z1,z2,z3,z5,z422,z6]),(0,[z7,z423,z1,z2,z3,z5,z6]),(0,[z424,z7,z1,z2,z3,z5,z6]),(0,[z7,z147,z1,z2,z3,z5,z65]),(0,[z7,z425,z1,z2,z3,z5,z6])],[(0,[z7,z426,z1,z2,z3,z5,z6]),(0,[z7,z1,z24,z2,z3,z5,z6]),(0,[z25,z1,z2,z3,z54,z5,z6]),(1,[z7,z1,z2,z5,z6,z343])],[(1,[z7,z1,z2,z141,z5,z6]),(0,[z7,z1,z427,z2,z3,z5,z6]),(0,[z7,z428,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z429,z6]),(0,[z47,z7,z1,z2,z3,z5,z65]),(0,[z7,z208,z1,z3,z105,z5,z6])],[(0,[z7,z271,z2,z3,z5,z99,z6]),(0,[z7,z1,z2,z3,z5,z430,z6]),(0,[z7,z133,z1,z22,z3,z5,z6]),(0,[z7,z1,z2,z3,z64,z6,z236])],[(0,[z431,z7,z1,z2,z3,z5,z6]),(0,[z7,z432,z1,z2,z3,z5,z6])]],
   [[(0,[z7,z1,z2,z433,z3,z5,z6]),(0,[z7,z33,z2,z3,z5,z6,z173]),(0,[z0,z89,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z434,z5,z6]),(0,[z7,z208,z1,z2,z3,z174,z6]),(0,[z7,z1,z2,z3,z5,z83,z67]),(0,[z7,z133,z1,z2,z97,z5,z6])],[(0,[z435,z7,z1,z2,z3,z5,z6]),(1,[z7,z1,z259,z2,z3,z5]),(0,[z47,z91,z1,z2,z3,z5,z6]),(0,[z7,z106,z1,z41,z3,z5,z6])],[(0,[z7,z1,z2,z127,z105,z5,z6])],[(0,[z7,z1,z2,z3,z436,z5,z6]),(0,[z89,z7,z437,z2,z3,z5,z6]),(0,[z7,z21,z2,z35,z3,z5,z6]),(0,[z438,z7,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z2,z3,z5,z6]),(0,[z7,z1,z2,z439,z3,z5,z6]),(0,[z47,z7,z82,z1,z2,z3,z5]),(0,[z7,z440,z1,z2,z3,z5,z6]),(0,[z441,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z343])],[(0,[z7,z1,z2,z442,z3,z5,z6]),(0,[z7,z1,z3,z5,z61,z6,z418]),(0,[z7,z1,z2,z3,z5,z353,z6]),(0,[z7,z165,z1,z2,z3,z6,z67])],[(0,[z7,z443,z1,z2,z3,z5,z6]),(0,[z7,z226,z2,z3,z5,z61,z6]),(1,[z7,z1,z2,z277,z5,z6]),(0,[z7,z1,z444,z2,z3,z5,z6]),(1,[z7,z1,z22,z3,z5,z6]),(1,[z7,z1,z2,z97,z5,z64])],[(1,[z7,z148,z1,z2,z3,z5]),(0,[z47,z7,z1,z2,z3,z267,z6]),(0,[z7,z1,z2,z445,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z275,z6]),(0,[z7,z446,z1,z2,z3,z5,z6])]],
   [[(0,[z7,z1,z2,z3,z5,z447,z6]),(0,[z89,z7,z20,z1,z2,z3,z6]),(0,[z7,z1,z2,z3,z448,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z449])],[(0,[z13,z7,z2,z246,z3,z5,z6]),(0,[z7,z102,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z450,z3,z5,z6])],[(0,[z25,z7,z302,z2,z3,z5,z6]),(0,[z7,z1,z2,z87,z3,z5,z190]),(0,[z13,z7,z2,z3,z145,z5,z6]),(0,[z7,z1,z2,z3,z451,z5,z6])],[(0,[z7,z33,z21,z2,z3,z5,z6]),(0,[z7,z452,z1,z2,z3,z5,z6]),(0,[z7,z453,z1,z2,z3,z5,z6]),(0,[z7,z1,z454,z2,z3,z5,z6])],[(1,[z7,z348,z2,z3,z5,z6]),(0,[z13,z7,z1,z134,z3,z5,z6]),(0,[z7,z116,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z455,z5,z6]),(0,[z7,z1,z2,z3,z5,z456,z6])],[(0,[z457,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z458,z5,z6]),(1,[z7,z106,z1,z3,z99,z6]),(0,[z7,z1,z41,z2,z3,z99,z6]),(0,[z7,z1,z2,z3,z5,z459,z6]),(0,[z7,z1,z2,z293,z3,z5,z6]),(1,[z7,z1,z2,z3,z5,z460])],[(0,[z13,z7,z45,z2,z3,z5,z6]),(0,[z7,z1,z2,z205,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z461,z6]),(0,[z7,z1,z2,z3,z5,z6,z462]),(0,[z7,z1,z2,z3,z5,z6,z67])],[(0,[z91,z7,z1,z2,z3,z5,z64]),(0,[z7,z226,z1,z2,z3,z5,z61])]],
   [[(0,[z463,z7,z1,z2,z3,z5,z6]),(1,[z13,z7,z246,z3,z5,z6]),(0,[z7,z464,z1,z2,z3,z5,z6]),(0,[z7,z14,z1,z2,z35,z5,z6]),(0,[z7,z20,z90,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z465]),(0,[z7,z1,z2,z3,z58,z5,z67])],[(0,[z7,z1,z2,z466,z3,z5,z6]),(0,[z47,z7,z226,z1,z2,z3,z5]),(0,[z7,z226,z1,z2,z3,z5,z173]),(0,[z7,z82,z1,z2,z3,z100,z6]),(0,[z7,z1,z2,z3,z5,z64,z83]),(0,[z7,z1,z2,z3,z5,z6,z460]),(0,[z7,z1,z467,z2,z3,z5,z6])],[(0,[z89,z1,z2,z3,z5,z140,z6]),(0,[z7,z1,z2,z3,z468,z5,z6]),(0,[z7,z469,z1,z2,z3,z5,z6]),(0,[z7,z147,z1,z2,z97,z5,z6])],[(0,[z91,z1,z2,z3,z5,z77,z6]),(0,[z7,z470,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z99,z101,z6]),(0,[z7,z1,z2,z127,z3,z101,z6]),(0,[z7,z165,z1,z2,z3,z5,z67])],[(0,[z7,z1,z2,z3,z5,z64,z6])],[(0,[z7,z1,z2,z471,z3,z5,z6]),(0,[z472,z7,z1,z2,z3,z5,z6]),(0,[z7,z473,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z474,z6]),(0,[z7,z90,z1,z2,z3,z145,z6])],[(0,[z7,z1,z2,z475,z3,z5,z6]),(0,[z7,z1,z98,z2,z105,z5,z6]),(0,[z7,z1,z2,z3,z476,z5,z6])],[(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z477,z5,z6]),(0,[z7,z478,z1,z2,z3,z5,z6]),(0,[z7,z479,z1,z2,z3,z5,z6]),(0,[z7,z480,z1,z2,z3,z5,z6])]],
   [[(0,[z7,z1,z2,z3,z481,z5,z6]),(0,[z7,z1,z2,z482,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z483]),(0,[z7,z484,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z97,z128,z5,z6])],[(0,[z485,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z53,z3,z5,z6])],[(0,[z7,z486,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z487,z5,z6]),(0,[z7,z1,z2,z3,z488,z5,z6]),(0,[z7,z1,z489,z2,z3,z5,z6]),(0,[z490,z7,z1,z2,z3,z5,z6])],[(1,[z7,z294,z1,z2,z3,z5]),(0,[z7,z1,z2,z3,z491,z5,z6]),(0,[z7,z102,z1,z2,z114,z5,z6]),(1,[z7,z1,z2,z3,z5,z492]),(1,[z7,z1,z2,z5,z341,z6]),(0,[z7,z493,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z494])],[(0,[z7,z495,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z496,z5,z6])],[(0,[z7,z1,z2,z3,z5,z6,z497]),(0,[z7,z498,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z499,z5,z6]),(0,[z7,z1,z2,z97,z3,z5,z64])],[(1,[z7,z117,z1,z2,z3,z6]),(0,[z7,z1,z2,z500,z3,z5,z6]),(0,[z7,z1,z2,z3,z501,z5,z6]),(1,[z47,z1,z2,z3,z5,z78]),(0,[z7,z502,z1,z2,z3,z5,z6])]],
   [[(0,[z7,z90,z45,z2,z3,z5,z6]),(0,[z12,z7,z1,z24,z3,z5,z6]),(0,[z7,z1,z348,z2,z3,z5,z6]),(0,[z7,z2,z3,z145,z5,z63,z6]),(1,[z7,z116,z2,z3,z5,z6]),(0,[z7,z1,z503,z2,z3,z5,z6])],[(0,[z504,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z505,z3,z5,z6]),(0,[z7,z1,z2,z3,z506,z5,z6]),(0,[z7,z507,z1,z2,z3,z5,z6]),(0,[z7,z508,z1,z2,z3,z5,z6])],[(0,[z23,z7,z157,z2,z3,z5,z6]),(0,[z7,z509,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z510,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z511]),(0,[z7,z1,z2,z3,z512,z5,z6])],[(0,[z25,z7,z14,z1,z2,z5,z6]),(0,[z7,z1,z2,z513,z3,z5,z6]),(0,[z7,z1,z2,z514,z3,z5,z6])],[(0,[z7,z515,z1,z2,z3,z5,z6]),(0,[z7,z20,z2,z3,z5,z63,z6]),(0,[z7,z104,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z516,z6]),(0,[z7,z1,z2,z3,z128,z99,z6]),(0,[z517,z7,z1,z2,z3,z5,z6])],[(0,[z7,z518,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z105,z5,z6,z65]),(0,[z7,z1,z2,z3,z5,z341,z6]),(0,[z7,z1,z41,z2,z127,z3,z6]),(0,[z7,z1,z2,z3,z92,z6,z67])],[(0,[z7,z1,z2,z3,z5,z6,z519]),(0,[z7,z520,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z521]),(0,[z7,z1,z2,z3,z5,z6,z522]),(0,[z7,z147,z1,z2,z3,z5,z64])],[(0,[z7,z416,z1,z45,z2,z5,z6]),(0,[z7,z1,z2,z3,z5,z523,z6]),(1,[z7,z48,z2,z3,z5,z6])]],
   [[(0,[z524,z7,z1,z2,z3,z5,z6]),(0,[z525,z7,z1,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z5,z220]),(0,[z7,z526,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z527,z5,z6]),(0,[z7,z106,z1,z2,z3,z99,z6]),(0,[z7,z1,z2,z3,z528,z5,z6])],[(0,[z7,z45,z2,z3,z5,z63,z6]),(0,[z529,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z530,z3,z5,z6]),(0,[z7,z254,z1,z2,z3,z5,z6]),(0,[z47,z7,z1,z2,z3,z5,z64]),(0,[z7,z1,z2,z3,z5,z531,z6]),(0,[z7,z1,z2,z532,z3,z5,z6]),(0,[z7,z1,z2,z3,z58,z99,z6])],[(0,[z7,z1,z2,z3,z5,z6,z533]),(0,[z7,z172,z1,z2,z3,z5,z6]),(0,[z7,z106,z1,z2,z534,z5,z6])],[(0,[z7,z1,z535,z2,z3,z5,z6]),(0,[z7,z536,z1,z2,z3,z5,z6]),(0,[z0,z7,z1,z2,z3,z4,z6])],[(0,[z91,z7,z1,z134,z2,z3,z5]),(0,[z13,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z537]),(0,[z7,z1,z2,z3,z5,z107,z6]),(0,[z7,z1,z2,z3,z42,z6,z67])],[(0,[z7,z1,z2,z3,z538,z5,z6]),(0,[z7,z14,z2,z35,z3,z5,z6]),(0,[z7,z1,z2,z3,z539,z5,z6]),(0,[z7,z540,z1,z2,z3,z5,z6]),(0,[z7,z1,z41,z98,z3,z5,z6]),(1,[z7,z82,z1,z3,z5,z136]),(0,[z7,z1,z541,z2,z3,z5,z6])],[(0,[z7,z542,z1,z45,z2,z5,z6]),(0,[z7,z117,z1,z2,z3,z5,z6]),(0,[z543,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z534,z5,z6]),(0,[z7,z544,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z545,z3,z5,z6])],[(0,[z7,z1,z2,z3,z546,z5,z6]),(0,[z547,z7,z1,z2,z3,z5,z6]),(0,[z7,z208,z1,z2,z152,z5,z6]),(0,[z7,z1,z2,z97,z152,z5,z6])]],
   [[(1,[z7,z26,z2,z3,z5,z6]),(0,[z7,z548,z1,z2,z3,z5,z6]),(0,[z7,z143,z21,z2,z3,z5,z6]),(0,[z7,z549,z1,z2,z3,z5,z6]),(0,[z7,z550,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z551,z5,z6]),(1,[z7,z1,z2,z3,z5,z190]),(0,[z7,z1,z2,z3,z5,z552,z6]),(0,[z7,z133,z1,z2,z3,z5,z209])],[(0,[z7,z226,z45,z2,z3,z5,z6]),(0,[z12,z1,z2,z53,z3,z5,z6]),(0,[z7,z1,z553,z2,z3,z5,z6])],[(0,[z7,z554,z1,z2,z3,z5,z6]),(0,[z555,z7,z1,z2,z3,z5,z6])],[(0,[z7,z1,z556,z2,z3,z5,z6]),(0,[z7,z1,z3,z42,z5,z99,z6]),(0,[z7,z1,z2,z127,z128,z5,z6]),(0,[z7,z1,z2,z557,z3,z5,z6])],[(1,[z7,z437,z2,z3,z5,z6]),(0,[z7,z437,z1,z2,z3,z5,z6]),(0,[z13,z7,z1,z3,z5,z6,z136]),(0,[z7,z1,z2,z3,z5,z99,z6]),(0,[z558,z7,z1,z2,z3,z5,z6]),(0,[z7,z82,z1,z2,z3,z5,z136])],[(0,[z559,z7,z1,z2,z3,z5,z6]),(0,[z7,z102,z1,z2,z97,z5,z6]),(1,[z7,z1,z2,z3,z353,z6]),(0,[z7,z1,z2,z3,z5,z6,z560]),(0,[z7,z561,z1,z2,z3,z5,z6])],[(1,[z7,z208,z1,z105,z5,z6]),(0,[z562,z7,z1,z2,z3,z5,z6]),(0,[z7,z133,z1,z2,z3,z6,z67]),(0,[z7,z563,z1,z2,z3,z5,z6])]],
   [[(0,[z7,z1,z2,z3,z5,z6,z564])],[(0,[z7,z1,z565,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z227]),(0,[z7,z566,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z567,z6])],[(0,[z7,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z136,z65])],[(0,[z7,z568,z1,z2,z3,z5,z6]),(0,[z7,z1,z48,z2,z3,z5,z6]),(0,[z7,z569,z1,z2,z3,z5,z6])],[(0,[z7,z426,z1,z45,z2,z3,z5]),(0,[z570,z7,z1,z2,z3,z5,z6]),(0,[z7,z143,z1,z246,z3,z5,z6]),(0,[z7,z1,z571,z2,z3,z5,z6]),(0,[z7,z2,z3,z5,z61,z6,z173]),(0,[z7,z1,z2,z5,z61,z6,z572]),(0,[z7,z1,z2,z573,z3,z5,z6]),(0,[z7,z1,z2,z127,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z574]),(0,[z7,z1,z575,z2,z3,z5,z6])],[(0,[z576,z7,z1,z2,z3,z5,z6]),(0,[z7,z20,z1,z2,z3,z58,z6]),(0,[z577,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z127,z3,z58,z6])],[(0,[z7,z578,z1,z2,z3,z5,z6]),(0,[z7,z14,z1,z2,z5,z6,z65]),(0,[z7,z1,z579,z2,z3,z5,z6])],[(0,[z7,z580,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z581,z6]),(0,[z7,z1,z134,z2,z3,z5,z136])]],
   [[(0,[z91,z7,z1,z2,z3,z5,z67]),(0,[z7,z1,z2,z3,z5,z582,z6]),(0,[z7,z106,z1,z2,z127,z3,z6]),(0,[z583,z7,z1,z2,z3,z5,z6])],[(0,[z7,z416,z1,z2,z3,z5,z6]),(0,[z89,z7,z1,z2,z3,z4,z6]),(1,[z89,z1,z2,z3,z140,z6]),(0,[z7,z1,z2,z3,z5,z6,z584]),(0,[z7,z1,z2,z3,z5,z585,z6]),(1,[z7,z133,z1,z2,z101,z6])],[(0,[z7,z1,z586,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z587,z6])],[(0,[z7,z588,z1,z2,z3,z5,z6]),(0,[z7,z589,z1,z2,z3,z5,z6]),(1,[z7,z90,z2,z3,z145,z6]),(0,[z7,z1,z2,z3,z590,z5,z6]),(0,[z7,z1,z2,z3,z591,z5,z6]),(0,[z7,z1,z2,z3,z5,z64,z67])],[(0,[z592,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z26,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z593]),(1,[z7,z1,z164,z3,z5,z6]),(0,[z594,z7,z1,z2,z3,z5,z6]),(0,[z595,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z596])],[(0,[z7,z1,z2,z597,z3,z5,z6]),(0,[z598,z7,z1,z2,z3,z5,z6]),(0,[z599,z7,z1,z2,z3,z5,z6]),(0,[z7,z600,z1,z2,z3,z5,z6])],[(0,[z47,z7,z1,z134,z2,z3,z5]),(0,[z7,z102,z14,z2,z3,z5,z6]),(0,[z7,z1,z41,z3,z42,z5,z6])],[(0,[z7,z1,z259,z2,z3,z5,z6]),(0,[z7,z1,z24,z3,z5,z6,z136]),(0,[z7,z1,z2,z3,z601,z5,z6]),(0,[z7,z1,z2,z602,z3,z5,z6])]],
   [[(0,[z7,z542,z1,z2,z3,z5,z6]),(0,[z7,z1,z603,z2,z3,z5,z6]),(0,[z7,z1,z2,z604,z3,z5,z6]),(0,[z25,z88,z1,z2,z3,z5,z6]),(0,[z7,z605,z1,z2,z3,z5,z6]),(0,[z7,z143,z1,z21,z3,z5,z6]),(0,[z7,z606,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z607,z6]),(0,[z608,z7,z1,z2,z3,z5,z6]),(0,[z7,z133,z1,z2,z3,z5,z460])],[(0,[z7,z1,z2,z3,z5,z609,z6]),(0,[z7,z1,z2,z3,z5,z610,z6]),(1,[z7,z1,z2,z5,z6,z572])],[(0,[z7,z611,z1,z2,z3,z5,z6]),(1,[z7,z1,z3,z5,z6,z418]),(1,[z7,z165,z1,z2,z3,z67])],[(0,[z612,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z613,z6])],[(0,[z7,z614,z1,z2,z3,z5,z6]),(0,[z47,z7,z1,z2,z141,z5,z6]),(0,[z7,z1,z2,z3,z5,z615,z6]),(0,[z7,z616,z1,z2,z3,z5,z6]),(0,[z7,z1,z617,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z618,z6]),(0,[z13,z7,z143,z2,z3,z5,z6]),(0,[z7,z2,z3,z163,z105,z5,z6]),(0,[z7,z619,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z620,z5,z6]),(0,[z7,z621,z1,z2,z3,z5,z6])],[(0,[z7,z1,z622,z2,z3,z5,z6])],[(0,[z346,z33,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z623,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z624]),(0,[z7,z625,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z626,z6])]],
   [[(0,[z7,z1,z2,z87,z3,z5,z46]),(0,[z0,z7,z1,z2,z3,z5,z6]),(0,[z7,z226,z1,z2,z3,z5,z6]),(0,[z7,z1,z98,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z136]),(0,[z7,z1,z2,z97,z5,z64,z6])],[(0,[z7,z1,z2,z627,z3,z5,z6]),(0,[z7,z302,z1,z2,z3,z5,z6]),(0,[z628,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z92,z136])],[(0,[z7,z1,z2,z3,z629,z5,z6]),(0,[z7,z1,z630,z2,z3,z5,z6]),(0,[z7,z1,z2,z631,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z632,z6]),(0,[z7,z1,z2,z3,z5,z6,z572]),(0,[z7,z1,z2,z3,z5,z633,z6]),(0,[z7,z634,z1,z2,z3,z5,z6])],[(0,[z7,z14,z45,z2,z3,z5,z6]),(0,[z12,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z635,z6])],[(0,[z7,z1,z2,z3,z636,z5,z6]),(1,[z7,z1,z2,z211,z5,z6]),(0,[z7,z1,z2,z3,z5,z637,z6])],[(0,[z7,z294,z1,z2,z3,z5,z6]),(0,[z88,z1,z2,z87,z3,z5,z6]),(0,[z7,z1,z2,z3,z638,z5,z6]),(0,[z639,z7,z1,z2,z3,z5,z6]),(0,[z7,z640,z1,z2,z3,z5,z6]),(0,[z641,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z642])],[(0,[z32,z1,z45,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z180,z5,z6]),(0,[z47,z1,z2,z3,z5,z6,z78]),(0,[z7,z1,z2,z643,z3,z5,z6])],[(1,[z7,z426,z1,z2,z3,z5]),(0,[z7,z33,z2,z3,z114,z5,z6]),(1,[z7,z157,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z4,z6]),(0,[z7,z1,z644,z2,z3,z5,z6])]],
   [[(1,[z91,z1,z2,z3,z5,z77]),(0,[z7,z645,z1,z2,z3,z5,z6]),(0,[z646,z7,z1,z2,z3,z5,z6]),(0,[z647,z7,z1,z2,z3,z5,z6]),(0,[z7,z648,z1,z2,z3,z5,z6]),(0,[z7,z1,z134,z3,z5,z83,z6]),(0,[z7,z649,z1,z2,z3,z5,z6])],[(0,[z7,z650,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z651,z5,z6]),(0,[z7,z1,z2,z3,z5,z652,z6]),(0,[z653,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z654,z5,z6]),(0,[z7,z655,z1,z2,z3,z5,z6]),(0,[z7,z1,z178,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z656,z5,z6])],[(0,[z7,z1,z2,z3,z54,z5,z6]),(0,[z7,z1,z2,z657,z3,z5,z6]),(0,[z7,z658,z1,z2,z3,z5,z6]),(0,[z47,z7,z1,z2,z3,z5,z67]),(0,[z7,z1,z2,z659,z3,z5,z6]),(0,[z7,z1,z660,z2,z3,z5,z6])],[(0,[z7,z1,z2,z661,z3,z5,z6]),(0,[z7,z234,z1,z2,z3,z5,z6]),(0,[z7,z1,z662,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z663,z6]),(0,[z7,z1,z2,z3,z5,z6,z664]),(0,[z7,z665,z1,z2,z3,z5,z6]),(0,[z666,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z152,z5,z6,z65])],[(0,[z7,z1,z2,z3,z5,z667,z6]),(0,[z7,z1,z668,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z211,z5,z6]),(0,[z7,z20,z1,z2,z3,z6,z67]),(0,[z7,z1,z2,z3,z5,z6,z173]),(0,[z7,z1,z2,z3,z5,z65,z67]),(0,[z7,z1,z2,z669,z3,z5,z6])],[(0,[z670,z7,z1,z2,z3,z5,z6]),(0,[z671,z7,z1,z2,z3,z5,z6]),(0,[z7,z672,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z673,z6]),(0,[z7,z1,z2,z3,z5,z674,z6]),(0,[z7,z1,z2,z3,z5,z675,z6]),(0,[z7,z1,z2,z3,z161,z5,z6])],[(0,[z1,z2,z3,z4,z5,z140,z6]),(0,[z7,z1,z2,z676,z3,z5,z6]),(0,[z7,z90,z2,z3,z145,z5,z6])]],
   [[(0,[z7,z1,z2,z3,z5,z677,z6]),(0,[z678,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z679,z3,z5,z6]),(0,[z7,z680,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z6,z681]),(0,[z682,z7,z1,z2,z3,z5,z6]),(0,[z7,z208,z1,z2,z3,z5,z492]),(0,[z7,z1,z2,z3,z5,z492,z6]),(0,[z7,z82,z1,z134,z3,z5,z6])],[],[(1,[z7,z254,z2,z3,z5,z6]),(0,[z7,z1,z2,z683,z3,z5,z6])],[(0,[z7,z1,z684,z2,z3,z5,z6]),(0,[z7,z1,z2,z685,z3,z5,z6]),(0,[z7,z31,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z6,z78]),(1,[z7,z1,z2,z3,z52,z6]),(0,[z686,z7,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z687,z5,z6]),(0,[z88,z7,z14,z1,z2,z5,z6]),(0,[z89,z7,z1,z2,z3,z5,z6]),(0,[z688,z7,z1,z2,z3,z5,z6])],[(0,[z23,z1,z24,z2,z3,z5,z6]),(0,[z7,z21,z2,z246,z3,z5,z6]),(0,[z7,z1,z2,z3,z105,z5,z6]),(0,[z7,z1,z2,z124,z3,z5,z6])]],
   [[(0,[z12,z7,z1,z53,z3,z5,z6]),(0,[z7,z1,z21,z2,z3,z5,z6]),(0,[z7,z21,z2,z3,z145,z5,z6]),(0,[z7,z1,z2,z35,z3,z5,z6]),(1,[z7,z102,z2,z114,z5,z6]),(0,[z7,z1,z2,z3,z5,z689,z6]),(1,[z7,z1,z2,z534,z5,z6]),(0,[z7,z82,z1,z2,z293,z5,z6])],[(0,[z7,z1,z690,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z691]),(0,[z346,z7,z33,z2,z3,z5,z6]),(0,[z692,z7,z1,z2,z3,z5,z6]),(0,[z0,z7,z90,z1,z2,z3,z6]),(0,[z7,z20,z1,z2,z3,z63,z6]),(0,[z7,z1,z2,z3,z693,z5,z6])],[(0,[z7,z1,z2,z694,z3,z5,z6]),(1,[z7,z1,z2,z3,z6,z227]),(0,[z7,z1,z2,z3,z305,z105,z6]),(0,[z7,z695,z1,z2,z3,z5,z6]),(0,[z7,z696,z1,z2,z3,z5,z6])],[(1,[z32,z45,z2,z3,z5,z6]),(0,[z7,z1,z2,z697,z3,z5,z6]),(0,[z7,z1,z2,z3,z698,z5,z6]),(1,[z7,z1,z2,z3,z100,z6]),(0,[z7,z1,z2,z3,z5,z6,z699])],[(0,[z7,z45,z2,z3,z5,z6,z173]),(0,[z7,z208,z133,z1,z2,z5,z6])],[(0,[z33,z1,z45,z2,z3,z5,z6]),(1,[z7,z542,z1,z2,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z700]),(0,[z7,z1,z2,z3,z5,z6,z701])],[(0,[z7,z702,z1,z2,z3,z5,z6]),(0,[z703,z7,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z65])],[(0,[z7,z704,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z705,z5,z6]),(0,[z7,z1,z2,z3,z5,z706,z6]),(0,[z7,z1,z2,z152,z5,z101,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z234,z348,z2,z3,z6]),(0,[z7,z1,z2,z3,z707,z6]),(0,[z7,z1,z2,z5,z6,z708]),(0,[z7,z1,z2,z5,z6,z572]),(0,[z7,z1,z41,z127,z105,z6]),(0,[z7,z1,z2,z3,z5,z709])],[(0,[z7,z710,z2,z3,z5,z6]),(0,[z7,z143,z21,z3,z5,z6]),(0,[z7,z1,z3,z5,z6,z418]),(0,[z7,z1,z2,z711,z5,z6]),(0,[z7,z1,z2,z3,z58,z92])],[(0,[z7,z1,z2,z3,z5,z712]),(0,[z7,z713,z2,z3,z5,z6]),(0,[z7,z1,z714,z3,z5,z6]),(0,[z7,z1,z2,z3,z180,z92]),(0,[z7,z1,z2,z3,z5,z715]),(0,[z91,z7,z1,z2,z5,z343]),(0,[z7,z133,z1,z2,z5,z279])],[(0,[z7,z90,z348,z2,z3,z6]),(0,[z7,z716,z2,z3,z5,z6]),(0,[z7,z1,z41,z22,z3,z6]),(0,[z7,z1,z617,z3,z5,z83])],[(0,[z32,z148,z45,z2,z3,z5]),(0,[z7,z1,z2,z3,z717,z6]),(0,[z7,z1,z2,z3,z5,z718]),(0,[z7,z116,z2,z97,z5,z6]),(0,[z7,z1,z3,z534,z99,z6]),(0,[z7,z1,z2,z3,z99,z292])],[(0,[z7,z1,z719,z3,z5,z6]),(1,[z1,z2,z720,z5,z6]),(0,[z47,z7,z1,z2,z3,z236]),(0,[z7,z1,z2,z128,z689,z6])],[(0,[z7,z172,z2,z3,z5,z721]),(0,[z7,z1,z2,z534,z5,z292])],[(0,[z32,z264,z45,z3,z5,z6]),(0,[z7,z1,z2,z722,z5,z6]),(0,[z23,z157,z24,z3,z5,z6]),(0,[z0,z1,z2,z3,z723,z6]),(0,[z7,z2,z3,z163,z5,z6]),(0,[z7,z21,z3,z122,z5,z6])]],
   [[(0,[z7,z544,z1,z105,z5,z6])],[(0,[z7,z1,z2,z3,z724,z6]),(0,[z7,z1,z2,z141,z5,z190]),(0,[z725,z1,z2,z3,z5,z6]),(0,[z7,z271,z106,z3,z99,z6]),(0,[z7,z1,z2,z293,z100,z6])],[(0,[z7,z264,z66,z3,z5,z6]),(0,[z7,z1,z3,z5,z726,z6]),(0,[z7,z1,z98,z3,z52,z6]),(0,[z7,z1,z2,z3,z5,z727]),(0,[z7,z469,z1,z2,z101,z6]),(0,[z7,z1,z2,z728,z5,z6])],[(0,[z7,z1,z2,z3,z729,z6]),(0,[z7,z1,z2,z211,z5,z6]),(0,[z7,z245,z1,z2,z3,z67]),(0,[z7,z226,z48,z2,z3,z5])],[(0,[z7,z1,z2,z3,z730,z6]),(0,[z7,z731,z1,z2,z5,z6]),(0,[z7,z1,z2,z3,z5,z732]),(0,[z7,z208,z104,z1,z2,z6])],[(0,[z7,z733,z2,z3,z5,z6]),(0,[z7,z1,z2,z211,z180,z6]),(0,[z7,z1,z734,z3,z5,z6]),(0,[z7,z1,z735,z3,z5,z6])],[(0,[z7,z736,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6]),(0,[z7,z737,z1,z2,z3,z6]),(0,[z7,z1,z2,z121,z5,z65])],[(0,[z91,z1,z2,z3,z5,z77])]],
   [[(0,[z13,z7,z234,z2,z3,z6]),(0,[z12,z1,z259,z53,z3,z5]),(0,[z7,z1,z738,z3,z5,z6]),(0,[z7,z1,z2,z739,z5,z6]),(0,[z7,z1,z2,z3,z740,z6]),(0,[z7,z1,z2,z5,z6,z741])],[(0,[z7,z148,z226,z2,z3,z5]),(0,[z7,z208,z1,z105,z174,z6])],[(0,[z7,z1,z2,z5,z742,z6]),(0,[z7,z1,z2,z743,z3,z6])],[(0,[z1,z2,z3,z720,z5,z6]),(0,[z13,z7,z482,z3,z5,z6]),(1,[z7,z1,z105,z52,z6]),(0,[z7,z133,z1,z2,z101,z209])],[(0,[z7,z1,z3,z5,z744,z6]),(0,[z7,z1,z2,z128,z52,z6]),(0,[z7,z1,z745,z105,z5,z6]),(0,[z7,z106,z3,z275,z99,z6]),(0,[z7,z1,z2,z5,z6,z746]),(0,[z7,z446,z1,z3,z5,z136])],[(0,[z7,z1,z2,z3,z747,z6]),(0,[z7,z1,z2,z97,z5,z190]),(0,[z7,z1,z5,z6,z418,z572]),(0,[z7,z1,z60,z3,z6,z227]),(0,[z7,z1,z178,z3,z5,z6])],[(0,[z7,z1,z205,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z748]),(0,[z7,z1,z749,z3,z5,z6]),(0,[z7,z1,z2,z5,z166,z65])],[(0,[z595,z45,z2,z3,z5,z6]),(0,[z7,z750,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z751]),(0,[z7,z1,z2,z752,z5,z6]),(0,[z7,z1,z2,z3,z6,z753]),(0,[z7,z2,z3,z305,z163,z6]),(0,[z7,z31,z1,z2,z5,z754])]],
   [[(0,[z7,z1,z205,z3,z180,z6]),(0,[z755,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z756,z6]),(0,[z7,z1,z2,z757,z3,z6]),(0,[z7,z1,z2,z3,z5,z758]),(0,[z7,z759,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z760,z6]),(0,[z7,z1,z761,z3,z5,z6]),(0,[z7,z762,z2,z3,z5,z6]),(0,[z7,z502,z1,z3,z99,z6]),(0,[z7,z1,z2,z5,z6,z763])],[(0,[z7,z254,z2,z3,z5,z6]),(0,[z7,z1,z2,z249,z6,z572])],[(0,[z7,z1,z2,z3,z764,z6]),(0,[z25,z302,z2,z54,z5,z6]),(0,[z7,z1,z3,z249,z6,z418]),(0,[z7,z765,z1,z2,z3,z5]),(0,[z7,z1,z2,z127,z230,z6]),(0,[z7,z1,z2,z3,z5,z766]),(0,[z7,z1,z2,z3,z767,z67])],[(0,[z32,z117,z45,z2,z3,z6]),(0,[z7,z768,z1,z2,z3,z5]),(0,[z7,z1,z164,z141,z5,z6]),(0,[z7,z1,z277,z5,z6,z418]),(0,[z7,z1,z2,z3,z52,z6]),(0,[z7,z1,z2,z127,z3,z292]),(0,[z7,z1,z2,z3,z58,z459])],[(0,[z7,z1,z2,z769,z5,z6]),(0,[z7,z226,z2,z3,z5,z667]),(0,[z7,z2,z3,z5,z770,z6])],[(0,[z7,z1,z3,z771,z5,z6]),(0,[z438,z33,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z772])],[(0,[z7,z234,z1,z264,z3,z6]),(0,[z7,z102,z2,z114,z5,z6]),(0,[z7,z1,z2,z3,z136,z236])]],
   [[(0,[z7,z1,z2,z773,z5,z6])],[(0,[z7,z1,z2,z3,z5,z774]),(0,[z7,z1,z2,z127,z534,z6])],[(0,[z7,z234,z1,z2,z3,z6]),(0,[z47,z48,z2,z3,z5,z78]),(0,[z7,z1,z2,z3,z775,z6]),(0,[z7,z1,z2,z124,z5,z107])],[(0,[z7,z1,z2,z3,z723,z6]),(0,[z7,z1,z2,z3,z776,z6]),(0,[z7,z2,z3,z5,z6,z777]),(0,[z7,z1,z467,z152,z5,z6])],[(0,[z7,z1,z2,z3,z5,z778]),(0,[z7,z779,z1,z2,z3,z6]),(0,[z7,z780,z2,z3,z5,z6])],[],[(0,[z7,z1,z2,z3,z5,z781])],[(0,[z7,z143,z66,z3,z5,z6]),(0,[z7,z90,z2,z3,z740,z6]),(0,[z7,z1,z2,z3,z782,z6]),(0,[z7,z133,z1,z2,z242,z6])]],
   [[(0,[z138,z7,z117,z1,z3,z6]),(0,[z217,z1,z2,z3,z4,z6]),(1,[z7,z783,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z784]),(0,[z7,z1,z785,z3,z5,z6]),(0,[z7,z1,z2,z128,z5,z279])],[(0,[z7,z1,z2,z3,z786,z6]),(0,[z89,z348,z2,z3,z140,z6])],[(0,[z7,z787,z1,z2,z5,z6]),(0,[z7,z1,z2,z3,z5,z27]),(0,[z7,z1,z2,z211,z267,z6]),(0,[z47,z7,z1,z2,z331,z5]),(0,[z7,z133,z1,z2,z101,z460])],[(0,[z12,z294,z1,z53,z3,z5]),(0,[z23,z66,z24,z3,z5,z6]),(0,[z7,z1,z2,z3,z788,z6]),(0,[z7,z1,z2,z3,z789,z6]),(0,[z7,z1,z2,z3,z58,z27]),(0,[z7,z14,z2,z35,z5,z6]),(0,[z7,z2,z3,z5,z6,z790])],[(0,[z7,z1,z2,z3,z5,z791]),(0,[z7,z1,z792,z3,z5,z6]),(0,[z7,z1,z2,z3,z180,z27]),(0,[z47,z1,z2,z3,z5,z368]),(0,[z7,z1,z134,z3,z5,z83])],[(0,[z7,z793,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z794]),(0,[z7,z1,z795,z3,z5,z6])],[(0,[z7,z1,z2,z3,z796,z6]),(0,[z7,z1,z2,z3,z5,z797]),(0,[z7,z1,z2,z5,z27,z798]),(0,[z7,z2,z35,z448,z5,z6])]],
   [[(0,[z7,z1,z2,z799,z5,z6]),(0,[z7,z2,z3,z800,z5,z6]),(0,[z7,z1,z2,z3,z5,z801]),(0,[z7,z802,z2,z3,z5,z6]),(0,[z7,z1,z2,z5,z6,z798]),(0,[z7,z1,z2,z3,z5,z279]),(0,[z7,z1,z3,z803,z99,z6]),(0,[z7,z1,z2,z331,z100,z6]),(0,[z7,z1,z2,z3,z804,z6])],[(0,[z138,z7,z542,z1,z5,z6]),(0,[z7,z1,z2,z3,z5,z805]),(0,[z7,z1,z806,z3,z5,z6]),(0,[z7,z1,z2,z3,z807,z6]),(0,[z7,z1,z2,z3,z808,z6]),(0,[z7,z2,z3,z145,z740,z6]),(0,[z7,z1,z3,z5,z803,z6]),(1,[z7,z1,z3,z5,z709]),(0,[z7,z695,z1,z2,z3,z67])],[(0,[z7,z66,z2,z3,z5,z6]),(0,[z7,z416,z117,z1,z2,z6]),(0,[z7,z1,z2,z809,z5,z6]),(0,[z7,z810,z2,z3,z5,z6]),(0,[z7,z1,z2,z811,z5,z27]),(0,[z7,z1,z41,z3,z803,z6]),(0,[z7,z1,z2,z3,z5,z812])],[(0,[z7,z1,z2,z3,z813,z6])],[(0,[z7,z2,z3,z740,z63,z6]),(0,[z7,z1,z2,z3,z5,z107]),(0,[z7,z1,z2,z3,z5,z814])],[(0,[z7,z1,z2,z815,z3,z5]),(0,[z1,z24,z806,z3,z5,z6]),(0,[z7,z1,z205,z3,z267,z6])],[(0,[z7,z1,z2,z3,z816,z6]),(0,[z7,z1,z105,z5,z52,z6]),(0,[z7,z1,z2,z293,z5,z6]),(0,[z7,z2,z3,z5,z6,z817])],[(0,[z7,z1,z2,z3,z5,z818]),(0,[z7,z202,z1,z2,z5,z65]),(0,[z7,z1,z22,z3,z128,z6])]],
   [[(0,[z7,z1,z2,z3,z819,z6]),(0,[z7,z1,z2,z3,z5,z820]),(0,[z7,z1,z2,z3,z5,z821]),(0,[z7,z822,z1,z2,z5,z6]),(0,[z7,z1,z823,z3,z5,z6])],[(0,[z7,z1,z2,z3,z824,z6]),(0,[z7,z254,z2,z3,z267,z6]),(0,[z7,z2,z3,z145,z29,z6]),(0,[z7,z825,z2,z3,z5,z6]),(0,[z7,z31,z1,z98,z5,z6])],[(0,[z7,z1,z2,z826,z5,z6]),(0,[z7,z1,z2,z211,z5,z67]),(0,[z7,z226,z586,z2,z3,z5]),(0,[z7,z1,z2,z3,z827,z6]),(0,[z7,z1,z2,z121,z5,z64])],[(0,[z7,z254,z2,z141,z5,z6]),(0,[z7,z82,z1,z205,z3,z5]),(0,[z7,z1,z2,z5,z136,z343])],[(0,[z7,z1,z2,z3,z828,z6]),(0,[z7,z1,z2,z3,z5,z829]),(0,[z7,z1,z2,z3,z830,z6])],[(0,[z7,z1,z2,z831,z5,z6]),(0,[z7,z1,z2,z832,z5,z6]),(0,[z7,z1,z2,z3,z833,z6]),(0,[z7,z1,z2,z124,z5,z6]),(0,[z7,z680,z1,z2,z5,z65])],[(0,[z7,z1,z2,z5,z6,z834]),(0,[z835,z1,z2,z3,z5,z6])],[(1,[z836,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z6,z837]),(0,[z47,z1,z164,z3,z5,z78]),(0,[z7,z82,z1,z3,z353,z136])]],
   [[(0,[z7,z1,z2,z3,z267,z65]),(0,[z7,z1,z3,z6,z418,z227]),(0,[z7,z208,z1,z745,z5,z6]),(0,[z7,z1,z41,z534,z5,z6])],[(0,[z193,z45,z2,z3,z5,z6])],[(0,[z138,z7,z1,z3,z5,z6]),(0,[z7,z1,z2,z3,z6,z838]),(0,[z7,z2,z3,z5,z839,z6]),(0,[z7,z1,z2,z840,z5,z6]),(0,[z7,z1,z2,z3,z841,z6]),(0,[z7,z271,z31,z2,z5,z6]),(0,[z7,z147,z1,z2,z5,z842])],[(0,[z1,z2,z3,z4,z723,z6]),(0,[z7,z1,z337,z3,z42,z6])],[(0,[z7,z1,z2,z3,z5,z843]),(0,[z7,z147,z1,z2,z5,z65])],[(0,[z7,z1,z2,z3,z5,z844]),(0,[z7,z1,z134,z3,z5,z632])],[(0,[z346,z836,z2,z3,z5,z6]),(0,[z7,z1,z2,z845,z5,z6])],[(0,[z13,z7,z264,z3,z5,z6]),(0,[z7,z1,z3,z5,z846,z6]),(0,[z7,z1,z2,z3,z5,z847]),(0,[z7,z48,z164,z3,z5,z6]),(0,[z1,z2,z3,z5,z77,z715]),(0,[z7,z172,z2,z3,z5,z173]),(0,[z7,z848,z2,z3,z5,z6])]],
   [[(0,[z7,z1,z3,z5,z6,z849]),(0,[z23,z1,z24,z3,z5,z6])],[(0,[z7,z1,z2,z3,z161,z6])],[(0,[z7,z148,z542,z1,z2,z5])],[(0,[z7,z1,z2,z3,z5,z850]),(0,[z7,z2,z5,z341,z275,z6]),(0,[z7,z31,z1,z2,z6,z67])],[(0,[z7,z294,z1,z3,z5,z136]),(0,[z7,z1,z851,z3,z5,z6]),(0,[z7,z1,z2,z277,z6,z227]),(0,[z7,z852,z2,z3,z5,z6])],[],[(0,[z0,z611,z1,z2,z3,z6])],[(0,[z7,z1,z2,z3,z5,z6]),(0,[z47,z1,z2,z211,z5,z78]),(0,[z7,z226,z2,z3,z5,z721]),(0,[z7,z1,z2,z853,z5,z6]),(0,[z7,z854,z1,z2,z3,z6]),(0,[z7,z1,z855,z3,z5,z6])]],
   [[(0,[z7,z1,z2,z3,z856,z6]),(0,[z7,z1,z2,z44,z128,z6])],[(0,[z32,z836,z2,z3,z5,z6]),(0,[z7,z148,z48,z2,z3,z5]),(0,[z7,z857,z2,z3,z5,z6]),(0,[z7,z294,z1,z2,z858,z5]),(0,[z7,z1,z2,z3,z180,z6]),(0,[z7,z208,z163,z105,z5,z6]),(0,[z7,z106,z1,z534,z99,z6]),(0,[z7,z1,z22,z3,z101,z6])],[],[(0,[z7,z1,z2,z3,z5,z859]),(0,[z7,z860,z1,z2,z3,z5]),(0,[z7,z1,z2,z3,z174,z279]),(0,[z7,z1,z2,z3,z5,z861]),(0,[z7,z1,z2,z3,z6,z236])],[(0,[z7,z1,z2,z862,z5,z6]),(0,[z32,z426,z45,z2,z3,z5]),(0,[z7,z1,z863,z3,z5,z6]),(0,[z7,z1,z2,z331,z5,z136])],[(0,[z7,z1,z2,z3,z5,z864]),(0,[z7,z1,z2,z5,z865,z6]),(0,[z7,z1,z2,z866,z5,z6]),(0,[z7,z1,z867,z3,z5,z6]),(1,[z7,z1,z745,z5,z6]),(0,[z7,z1,z98,z745,z5,z6]),(0,[z7,z1,z2,z3,z868,z6])],[(0,[z12,z1,z806,z3,z5,z6]),(0,[z7,z1,z2,z3,z6,z869]),(0,[z870,z1,z2,z3,z5,z6])],[(0,[z7,z426,z542,z1,z2,z5]),(0,[z1,z2,z720,z54,z5,z6]),(0,[z7,z1,z2,z811,z5,z6]),(0,[z7,z48,z2,z211,z5,z6]),(0,[z7,z1,z205,z3,z5,z64]),(0,[z7,z1,z2,z3,z698,z67]),(0,[z7,z1,z871,z3,z5,z6]),(0,[z7,z1,z2,z97,z5,z8]),(0,[z7,z1,z2,z872,z5,z6]),(0,[z7,z873,z2,z3,z5,z6]),(0,[z7,z1,z2,z121,z5,z209])]],
   [[(0,[z7,z874,z1,z2,z3,z6]),(0,[z13,z7,z783,z3,z5,z6]),(0,[z7,z14,z2,z5,z6,z701]),(0,[z7,z1,z2,z875,z5,z6])],[(0,[z7,z1,z3,z5,z709,z136])],[(0,[z7,z1,z2,z3,z876,z6]),(0,[z7,z2,z3,z5,z877,z6]),(0,[z7,z1,z878,z3,z5,z6]),(0,[z7,z1,z22,z5,z101,z6])],[(0,[z7,z1,z2,z3,z879,z6]),(0,[z0,z1,z2,z3,z4,z220]),(0,[z7,z1,z2,z3,z5,z880]),(0,[z7,z1,z2,z3,z881,z6]),(0,[z7,z1,z2,z3,z5,z882])],[(0,[z594,z45,z2,z3,z5,z6]),(0,[z91,z1,z2,z3,z5,z333])],[(0,[z280,z1,z53,z3,z5,z6]),(0,[z23,z1,z806,z3,z5,z6]),(0,[z883,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z884]),(0,[z7,z1,z60,z3,z249,z6]),(0,[z7,z1,z2,z5,z6,z842]),(0,[z7,z1,z2,z121,z6,z67])],[(0,[z7,z1,z885,z3,z5,z6]),(0,[z7,z1,z2,z886,z5,z6]),(0,[z7,z294,z1,z2,z3,z879]),(0,[z7,z887,z2,z3,z5,z6]),(0,[z47,z254,z2,z3,z5,z78]),(0,[z7,z1,z2,z3,z353,z136]),(0,[z7,z888,z1,z2,z5,z6])],[(0,[z7,z20,z2,z3,z63,z6]),(0,[z7,z1,z2,z889,z5,z6]),(0,[z7,z890,z2,z3,z5,z6])]],
   [[(0,[z7,z1,z2,z5,z891,z6]),(0,[z88,z1,z2,z87,z5,z6]),(0,[z7,z1,z2,z5,z190,z65]),(0,[z91,z7,z1,z2,z3,z236]),(0,[z7,z892,z2,z3,z5,z6])],[(0,[z370,z1,z2,z54,z5,z6]),(0,[z7,z1,z2,z3,z6,z893])],[(0,[z7,z117,z542,z1,z2,z6]),(0,[z7,z1,z2,z3,z5,z894]),(0,[z7,z1,z2,z3,z5,z842])],[(0,[z7,z1,z2,z3,z5,z895]),(0,[z7,z1,z2,z3,z896,z6]),(0,[z7,z897,z2,z3,z5,z6])],[(0,[z346,z33,z2,z3,z5,z6]),(0,[z7,z898,z1,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z899]),(0,[z1,z2,z3,z5,z6,z715]),(0,[z7,z1,z2,z3,z161,z209]),(0,[z7,z1,z2,z3,z6,z767])],[(0,[z91,z518,z1,z2,z3,z5]),(0,[z900,z1,z2,z3,z5,z6]),(0,[z7,z1,z783,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z901]),(0,[z7,z1,z2,z3,z92,z767])],[(0,[z7,z902,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z903]),(0,[z904,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z905,z6]),(0,[z7,z1,z2,z906,z5,z6]),(0,[z7,z1,z2,z5,z209,z65])],[(0,[z7,z102,z26,z2,z5,z6]),(0,[z7,z1,z907,z3,z5,z6]),(0,[z7,z2,z3,z5,z275,z6]),(0,[z7,z226,z2,z3,z61,z227]),(0,[z7,z1,z2,z745,z5,z6]),(0,[z7,z1,z2,z534,z99,z6]),(0,[z7,z1,z2,z124,z5,z292])]],
   [[(0,[z7,z2,z3,z5,z721,z173]),(0,[z7,z104,z1,z22,z3,z6]),(0,[z7,z1,z908,z3,z5,z6])],[(0,[z7,z909,z2,z3,z5,z6]),(0,[z7,z294,z1,z134,z3,z5]),(0,[z7,z1,z2,z3,z249,z6]),(0,[z7,z104,z1,z2,z127,z6]),(0,[z7,z910,z2,z3,z5,z6])],[(0,[z32,z542,z45,z2,z5,z6]),(0,[z7,z1,z2,z911,z5,z6]),(0,[z7,z1,z912,z3,z5,z6])],[(0,[z7,z1,z2,z3,z913,z6]),(0,[z89,z392,z1,z2,z3,z6]),(0,[z7,z102,z2,z434,z5,z6]),(0,[z914,z1,z2,z3,z5,z6]),(0,[z7,z1,z98,z5,z318,z6])],[(0,[z7,z1,z2,z3,z267,z64]),(0,[z7,z648,z1,z2,z3,z67])],[(0,[z7,z1,z2,z3,z5,z915]),(0,[z7,z916,z1,z2,z3,z5]),(0,[z7,z1,z2,z3,z42,z292])],[(0,[z7,z1,z2,z3,z6,z917]),(0,[z7,z1,z2,z3,z267,z6]),(0,[z47,z1,z2,z3,z5,z361]),(0,[z7,z1,z2,z152,z52,z6]),(0,[z7,z1,z2,z127,z6,z169])],[(0,[z7,z1,z2,z3,z6,z918]),(0,[z7,z1,z2,z3,z919,z6])]],
   [[(0,[z7,z1,z2,z141,z5,z6])],[(0,[z7,z1,z2,z3,z306,z92])],[(0,[z7,z1,z2,z3,z920,z6]),(0,[z7,z1,z2,z5,z6,z921]),(0,[z7,z1,z2,z141,z180,z6]),(0,[z7,z1,z2,z922,z5,z6]),(0,[z7,z1,z2,z3,z174,z6]),(0,[z7,z208,z1,z105,z5,z492]),(0,[z7,z1,z923,z2,z3,z5]),(0,[z7,z133,z1,z2,z924,z6]),(0,[z7,z1,z2,z3,z5,z767])],[(0,[z7,z1,z925,z3,z5,z6]),(0,[z7,z1,z178,z3,z5,z209]),(1,[z7,z1,z2,z5,z842]),(0,[z7,z1,z2,z3,z58,z767])],[(0,[z7,z416,z2,z114,z5,z6]),(0,[z138,z7,z416,z1,z5,z6]),(0,[z7,z926,z2,z3,z5,z6]),(0,[z7,z1,z164,z211,z5,z6]),(0,[z7,z783,z246,z3,z5,z6]),(0,[z7,z82,z1,z3,z100,z136]),(0,[z7,z1,z2,z97,z161,z64])],[(0,[z7,z927,z1,z2,z5,z6]),(0,[z7,z1,z2,z3,z5,z928])],[(0,[z7,z416,z14,z2,z5,z6]),(0,[z7,z1,z2,z929,z5,z6]),(0,[z7,z1,z2,z97,z161,z6])],[(0,[z930,z7,z1,z3,z5,z6])]],
   [[(0,[z7,z148,z1,z264,z3,z5]),(0,[z1,z2,z3,z5,z6,z931]),(0,[z932,z7,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z161,z67])],[(0,[z7,z1,z2,z933,z5,z6]),(0,[z7,z1,z2,z3,z934,z6]),(0,[z7,z20,z2,z3,z400,z6]),(0,[z7,z1,z2,z3,z5,z292]),(0,[z7,z31,z1,z41,z2,z6]),(0,[z7,z2,z3,z5,z6,z935])],[(0,[z7,z1,z2,z936,z5,z6]),(0,[z7,z1,z205,z141,z5,z6]),(0,[z7,z1,z22,z3,z5,z6]),(0,[z7,z1,z937,z3,z5,z6])],[(0,[z7,z148,z1,z2,z3,z5]),(0,[z7,z1,z2,z3,z5,z938]),(0,[z7,z104,z1,z98,z2,z6])],[(0,[z7,z939,z2,z3,z5,z6]),(0,[z7,z2,z3,z5,z6,z721]),(0,[z7,z208,z104,z1,z105,z6]),(0,[z7,z1,z2,z3,z5,z940]),(0,[z7,z1,z2,z5,z941,z6])],[(0,[z7,z942,z1,z2,z3,z5]),(0,[z7,z943,z2,z3,z5,z6]),(0,[z7,z1,z134,z205,z3,z5]),(0,[z47,z1,z2,z3,z5,z715]),(0,[z7,z1,z2,z944,z5,z6])],[(0,[z7,z302,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z945]),(0,[z7,z1,z2,z3,z5,z946]),(0,[z7,z1,z2,z3,z305,z6])],[(0,[z7,z1,z947,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z948]),(0,[z7,z949,z2,z3,z5,z6]),(0,[z7,z1,z3,z105,z52,z6]),(0,[z7,z1,z2,z3,z5,z754]),(0,[z7,z1,z2,z950,z5,z6])]],
   [[(0,[z7,z348,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z180,z67]),(0,[z7,z1,z2,z3,z951,z6]),(0,[z7,z1,z2,z3,z6,z952]),(0,[z7,z1,z3,z5,z6,z953])],[(0,[z7,z1,z2,z3,z5,z460])],[(0,[z47,z7,z1,z2,z3,z353]),(0,[z7,z1,z2,z152,z5,z279]),(0,[z7,z954,z2,z3,z5,z6])],[(0,[z7,z254,z164,z3,z5,z6]),(0,[z7,z133,z1,z41,z98,z6]),(0,[z7,z625,z1,z2,z5,z65])],[(0,[z7,z1,z2,z3,z955,z5]),(0,[z7,z956,z1,z3,z5,z6]),(0,[z25,z26,z2,z54,z5,z6]),(0,[z7,z957,z2,z3,z5,z6]),(0,[z13,z7,z246,z3,z5,z6]),(0,[z7,z1,z41,z3,z496,z6])],[(0,[z7,z958,z1,z2,z5,z6]),(0,[z7,z1,z2,z141,z5,z65]),(0,[z91,z7,z1,z2,z331,z5]),(0,[z959,z1,z2,z3,z5,z6]),(0,[z7,z2,z3,z5,z61,z721]),(0,[z7,z1,z2,z3,z5,z960])],[(0,[z59,z45,z2,z3,z5,z6]),(0,[z7,z1,z2,z961,z5,z6]),(0,[z7,z1,z2,z3,z190,z838]),(0,[z7,z1,z60,z3,z5,z6]),(0,[z7,z143,z783,z3,z5,z6]),(0,[z7,z1,z579,z152,z5,z6]),(0,[z962,z7,z1,z2,z3,z5])],[(0,[z7,z963,z2,z3,z5,z6]),(0,[z7,z1,z2,z5,z6,z964])]],
   [[(0,[z7,z234,z21,z2,z3,z6]),(0,[z7,z294,z1,z2,z3,z764]),(0,[z7,z1,z205,z3,z5,z67]),(0,[z7,z1,z3,z5,z6,z965]),(0,[z7,z966,z1,z2,z3,z6]),(0,[z7,z1,z2,z3,z83,z236])],[(0,[z12,z1,z53,z3,z5,z6]),(0,[z7,z1,z2,z3,z967,z6]),(0,[z7,z1,z2,z3,z968,z6]),(0,[z7,z969,z2,z3,z5,z6]),(0,[z7,z226,z2,z5,z61,z572]),(0,[z7,z106,z1,z22,z3,z6])],[(0,[z7,z970,z1,z3,z5,z6]),(0,[z7,z1,z134,z631,z3,z5]),(0,[z7,z226,z3,z5,z61,z418]),(0,[z7,z1,z3,z5,z83,z709]),(0,[z7,z1,z22,z5,z6,z65]),(0,[z7,z1,z178,z3,z5,z460]),(0,[z7,z1,z2,z128,z6,z389])],[(0,[z7,z1,z2,z3,z971,z6])],[(0,[z1,z806,z53,z3,z5,z6]),(0,[z278,z7,z1,z105,z5,z6])],[(0,[z7,z972,z1,z2,z3,z5]),(0,[z7,z102,z2,z512,z5,z6]),(0,[z7,z973,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z974]),(0,[z7,z226,z2,z3,z5,z61])],[(0,[z7,z1,z2,z141,z267,z6]),(0,[z7,z1,z98,z152,z5,z6]),(0,[z975,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z97,z5,z842])]],
   [[(0,[z7,z234,z2,z3,z63,z6]),(0,[z7,z117,z1,z264,z3,z6]),(0,[z25,z1,z2,z720,z5,z6])],[(0,[z7,z294,z1,z2,z809,z5]),(0,[z7,z976,z2,z3,z5,z6]),(0,[z7,z1,z2,z977,z3,z6])],[(0,[z138,z7,z426,z1,z3,z5]),(0,[z7,z1,z2,z3,z284,z67]),(1,[z7,z2,z3,z5,z721]),(0,[z7,z1,z2,z3,z978,z6]),(0,[z7,z1,z3,z42,z803,z6]),(0,[z7,z1,z2,z5,z64,z842])],[(0,[z47,z1,z2,z3,z5,z78]),(0,[z7,z979,z1,z2,z3,z5]),(0,[z7,z106,z31,z1,z2,z6]),(0,[z7,z1,z2,z257,z5,z64])],[(0,[z7,z1,z2,z3,z980,z6]),(0,[z7,z981,z1,z2,z3,z5]),(0,[z7,z1,z982,z3,z5,z6]),(0,[z7,z1,z2,z983,z5,z6]),(0,[z7,z1,z984,z3,z5,z6]),(0,[z7,z1,z2,z5,z326,z65]),(0,[z7,z425,z1,z3,z5,z136])],[(0,[z7,z1,z985,z3,z5,z6]),(0,[z89,z437,z2,z3,z140,z6]),(0,[z47,z1,z2,z3,z180,z78]),(0,[z7,z1,z2,z3,z986,z6])],[(0,[z7,z987,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z988,z6])],[(0,[z7,z1,z264,z3,z5,z6]),(0,[z7,z989,z1,z2,z3,z6]),(0,[z7,z1,z2,z3,z5,z990]),(0,[z7,z2,z3,z991,z5,z6]),(0,[z7,z1,z2,z3,z5,z992]),(0,[z7,z1,z2,z993,z5,z6])]],
   [[(0,[z836,z45,z2,z3,z5,z6]),(0,[z7,z994,z1,z2,z5,z6]),(0,[z7,z1,z2,z3,z5,z995]),(0,[z7,z104,z2,z3,z163,z6]),(0,[z7,z104,z1,z2,z534,z6]),(1,[z7,z1,z534,z99,z6]),(0,[z7,z1,z3,z5,z6,z709])],[(0,[z7,z1,z2,z3,z5,z996])],[(0,[z7,z997,z2,z3,z5,z6]),(0,[z7,z998,z2,z3,z5,z6])],[(0,[z7,z48,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z999]),(0,[z7,z1,z1000,z3,z5,z6])],[(0,[z7,z416,z426,z1,z2,z5]),(0,[z7,z1,z2,z3,z5,z220]),(0,[z7,z1,z2,z1001,z5,z6]),(0,[z7,z1002,z2,z3,z5,z6])],[(0,[z7,z1,z2,z1003,z5,z6]),(0,[z7,z1004,z2,z3,z5,z6]),(0,[z7,z48,z2,z3,z180,z6]),(0,[z47,z1,z205,z3,z5,z78]),(0,[z7,z1,z2,z331,z5,z83])],[(0,[z7,z1,z2,z1005,z5,z6]),(0,[z688,z1,z24,z3,z5,z6]),(1,[z1,z2,z3,z5,z715]),(0,[z7,z1,z2,z3,z1006,z6]),(0,[z7,z1,z541,z3,z42,z6]),(0,[z7,z82,z1,z3,z5,z709])],[(0,[z13,z7,z416,z2,z5,z6]),(0,[z7,z1007,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z1008])]],
   [[(0,[z7,z148,z117,z1,z2,z3]),(0,[z7,z1,z2,z3,z52,z492]),(0,[z7,z1,z2,z331,z5,z6]),(0,[z7,z1,z2,z5,z6,z1009])],[(0,[z7,z90,z2,z3,z377,z6]),(0,[z1,z2,z3,z5,z715,z78]),(0,[z7,z1,z2,z3,z58,z111]),(0,[z7,z1,z98,z310,z5,z6]),(0,[z7,z82,z1,z3,z5,z136]),(0,[z7,z1,z2,z924,z101,z6])],[(0,[z138,z7,z234,z1,z3,z6]),(0,[z7,z1010,z1,z2,z5,z6]),(0,[z7,z1,z2,z3,z5,z1011]),(0,[z47,z470,z1,z2,z3,z5]),(0,[z7,z1,z2,z1012,z5,z6]),(0,[z7,z143,z3,z5,z6,z560]),(0,[z7,z1,z2,z1013,z5,z6]),(0,[z7,z1,z2,z5,z6,z1014]),(0,[z7,z1,z2,z1015,z5,z6]),(0,[z7,z1,z2,z3,z5,z1016])],[(0,[z7,z836,z2,z3,z5,z6]),(0,[z7,z1,z2,z1017,z5,z6]),(0,[z7,z1018,z1,z2,z3,z5]),(0,[z7,z1,z2,z3,z5,z1019]),(0,[z7,z104,z1,z3,z99,z6]),(0,[z7,z133,z1,z178,z101,z6])],[(0,[z7,z26,z2,z3,z5,z6]),(0,[z7,z1,z2,z5,z6,z1020]),(0,[z7,z1,z2,z119,z5,z65]),(0,[z7,z116,z2,z5,z6,z65]),(0,[z7,z31,z1,z2,z128,z6]),(0,[z7,z1,z2,z5,z83,z343])],[(0,[z7,z48,z205,z3,z5,z6]),(0,[z7,z2,z3,z5,z1021,z6])],[(0,[z0,z1,z2,z3,z4,z27]),(0,[z7,z425,z1,z105,z5,z6])],[(0,[z7,z1,z1022,z3,z5,z6]),(0,[z47,z7,z1,z2,z5,z343]),(0,[z7,z1,z41,z3,z42,z6]),(0,[z1023,z1,z2,z3,z5,z6]),(0,[z7,z1,z22,z97,z5,z6])]],
   [[(0,[z7,z226,z2,z3,z249,z61])],[(0,[z7,z1,z1024,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z1025]),(0,[z7,z106,z1,z3,z99,z107])],[(0,[z7,z1,z2,z3,z353,z6])],[(0,[z32,z234,z45,z2,z3,z6]),(0,[z7,z1,z2,z1026,z5,z6]),(0,[z91,z1,z2,z3,z5,z511]),(0,[z7,z271,z2,z3,z5,z6]),(0,[z7,z1,z3,z5,z393,z136]),(0,[z7,z133,z1,z2,z52,z6]),(0,[z7,z1,z41,z3,z231,z6])],[(0,[z7,z416,z1,z264,z5,z6]),(0,[z7,z416,z234,z1,z2,z6]),(0,[z7,z1,z2,z3,z5,z1027]),(0,[z7,z1,z2,z3,z1028,z6]),(0,[z7,z1,z2,z720,z5,z6]),(0,[z7,z116,z104,z2,z3,z6]),(0,[z7,z104,z1,z2,z3,z6]),(0,[z7,z271,z2,z3,z58,z6]),(0,[z7,z1,z22,z127,z5,z6])],[(0,[z7,z1,z2,z3,z5,z209])],[(0,[z7,z1,z2,z3,z58,z209])],[(0,[z7,z416,z1,z2,z5,z6]),(0,[z7,z1,z2,z3,z5,z1029]),(0,[z7,z1,z152,z745,z5,z6]),(0,[z7,z133,z1,z2,z69,z6])]],
   [[(0,[z7,z1,z3,z5,z6,z1030]),(0,[z7,z1,z2,z127,z351,z6])],[(0,[z7,z234,z426,z1,z2,z3]),(0,[z7,z1,z2,z141,z5,z64]),(0,[z1031,z7,z1,z2,z3,z5]),(0,[z7,z20,z2,z3,z531,z6]),(0,[z7,z1,z2,z3,z6,z1032]),(0,[z7,z1033,z22,z3,z5,z6])],[(0,[z7,z1,z134,z3,z5,z56]),(0,[z7,z1,z2,z3,z27,z67]),(0,[z47,z1,z2,z3,z267,z78]),(0,[z7,z21,z3,z5,z552,z6]),(0,[z7,z1,z2,z1034,z5,z6]),(0,[z7,z106,z1,z124,z99,z6]),(0,[z7,z1,z2,z5,z6,z343]),(0,[z7,z165,z1,z2,z3,z767])],[(0,[z7,z2,z3,z711,z5,z6]),(0,[z7,z31,z1,z2,z5,z766]),(0,[z7,z1,z2,z3,z1035,z6])],[(0,[z7,z1,z2,z3,z1036,z6]),(0,[z7,z1,z2,z3,z1037,z5]),(0,[z7,z1038,z2,z3,z5,z6]),(0,[z7,z31,z1,z2,z52,z6]),(0,[z7,z133,z1,z22,z101,z6])],[(0,[z7,z1,z2,z3,z1039,z6]),(0,[z7,z133,z1,z2,z101,z6])],[(0,[z836,z1,z2,z3,z5,z6]),(0,[z13,z7,z66,z3,z5,z6]),(0,[z88,z1,z2,z87,z5,z190])],[(0,[z88,z498,z1,z2,z5,z6]),(0,[z7,z1040,z2,z3,z5,z6]),(0,[z7,z1,z2,z1041,z5,z6])]],
   [[(0,[z7,z1,z164,z3,z5,z6]),(0,[z7,z1,z259,z2,z3,z5]),(0,[z7,z1042,z2,z3,z5,z6]),(0,[z7,z1043,z2,z3,z5,z6]),(0,[z7,z106,z1,z3,z803,z6])],[(0,[z7,z1044,z1,z2,z3,z6])],[(0,[z7,z48,z2,z3,z267,z6]),(0,[z7,z1,z164,z3,z180,z6]),(0,[z7,z1,z2,z3,z209,z67])],[(0,[z13,z7,z288,z3,z5,z6]),(0,[z7,z208,z1,z105,z52,z6])],[(0,[z13,z7,z391,z3,z5,z6]),(0,[z7,z1,z2,z211,z5,z92]),(0,[z7,z1,z2,z1045,z5,z6]),(0,[z7,z133,z1,z2,z3,z292]),(0,[z7,z1046,z2,z3,z5,z6])],[(0,[z7,z1,z2,z1047,z5,z6]),(0,[z7,z1,z2,z3,z5,z1048]),(0,[z7,z1,z2,z3,z1049,z6]),(0,[z7,z1,z2,z3,z1050,z6]),(0,[z7,z1051,z2,z3,z5,z6]),(0,[z7,z2,z783,z3,z5,z6]),(0,[z7,z1,z2,z277,z5,z6]),(0,[z7,z2,z35,z711,z5,z6]),(0,[z7,z1,z2,z3,z5,z1052]),(0,[z7,z1,z2,z97,z5,z64])],[(0,[z7,z1,z1053,z3,z5,z6]),(0,[z7,z1,z2,z1054,z5,z6]),(0,[z7,z102,z2,z711,z5,z6]),(0,[z7,z31,z1,z2,z101,z6]),(0,[z7,z1,z1055,z2,z3,z5]),(0,[z7,z1,z22,z3,z58,z6]),(0,[z7,z165,z1,z2,z3,z67])],[(0,[z325,z33,z2,z3,z5,z6]),(1,[z1,z2,z3,z723,z6])]],
   [[(0,[z7,z1,z2,z3,z1056,z6]),(0,[z7,z1,z2,z3,z1057,z6]),(0,[z7,z1,z98,z128,z99,z6])],[(0,[z7,z1058,z1,z2,z3,z5]),(0,[z7,z1,z3,z745,z5,z6]),(0,[z7,z1059,z2,z3,z5,z6]),(0,[z7,z1,z2,z534,z5,z107]),(0,[z7,z133,z1,z2,z534,z6])],[(0,[z653,z33,z2,z3,z5,z6]),(0,[z7,z172,z48,z2,z3,z5]),(0,[z7,z1,z2,z22,z101,z6])],[(0,[z7,z1,z2,z1060,z5,z6]),(0,[z7,z1061,z2,z3,z5,z6]),(0,[z7,z116,z2,z3,z305,z6])],[(0,[z7,z1062,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z789,z190]),(0,[z1063,z1,z2,z3,z5,z6]),(1,[z7,z2,z711,z5,z6]),(0,[z7,z1,z2,z3,z5,z1064]),(0,[z7,z208,z1,z22,z5,z6]),(0,[z7,z106,z1,z3,z99,z6]),(0,[z7,z544,z133,z1,z2,z6])],[(0,[z73,z1,z2,z3,z140,z6]),(0,[z7,z226,z60,z3,z5,z61]),(0,[z7,z1,z2,z3,z1065,z6])],[(0,[z7,z1066,z2,z3,z5,z6])],[(0,[z7,z1,z205,z3,z5,z92])]],
   [[(0,[z7,z426,z1,z264,z3,z5]),(0,[z7,z1,z2,z3,z5,z1067]),(0,[z7,z1,z2,z3,z5,z1068]),(0,[z7,z1,z503,z3,z5,z83])],[(0,[z138,z7,z148,z1,z3,z5]),(0,[z7,z1,z2,z1069,z5,z6])],[(0,[z7,z90,z2,z3,z6,z462]),(0,[z7,z104,z1,z41,z3,z6])],[(0,[z7,z157,z2,z3,z5,z6]),(0,[z7,z426,z1,z2,z3,z5]),(0,[z7,z2,z3,z5,z740,z6]),(0,[z7,z82,z1,z293,z5,z136])],[(0,[z7,z271,z2,z3,z6,z67]),(0,[z7,z1070,z2,z3,z5,z6])],[(1,[z1,z806,z3,z5,z6]),(0,[z7,z1071,z2,z3,z5,z6]),(0,[z7,z31,z1,z105,z5,z6]),(0,[z7,z544,z1,z3,z99,z6])],[(0,[z7,z1,z2,z1072,z5,z6]),(0,[z7,z1,z2,z1073,z5,z6]),(0,[z7,z1,z2,z3,z803,z6])],[(0,[z7,z20,z348,z2,z3,z6]),(0,[z7,z1,z2,z3,z5,z721]),(0,[z7,z208,z1,z105,z5,z279]),(0,[z7,z104,z1,z2,z101,z6])]],
   [[(0,[z7,z1,z2,z1074,z5,z6]),(0,[z7,z1,z2,z534,z42,z6]),(0,[z7,z1,z2,z1075,z5,z6]),(0,[z7,z1,z2,z161,z6,z65])],[(0,[z7,z1,z2,z3,z1076,z6]),(0,[z7,z1,z2,z6,z572,z227])],[(0,[z7,z416,z21,z2,z5,z6]),(0,[z7,z1,z2,z1077,z5,z6]),(0,[z583,z1,z2,z87,z5,z6]),(0,[z7,z1,z205,z211,z5,z6]),(0,[z7,z1,z105,z99,z101,z6]),(0,[z7,z1,z2,z127,z924,z6])],[(0,[z7,z416,z148,z1,z2,z5]),(0,[z7,z294,z1,z2,z3,z5]),(0,[z89,z1,z2,z3,z723,z6]),(1,[z7,z2,z3,z740,z6]),(0,[z7,z1,z2,z3,z5,z492]),(0,[z7,z1,z2,z5,z341,z6]),(0,[z7,z1,z2,z3,z1078,z6]),(0,[z7,z2,z3,z1079,z5,z6])],[(0,[z7,z133,z1,z62,z2,z6]),(0,[z7,z1,z2,z293,z353,z6]),(0,[z7,z133,z1,z2,z65,z67])],[(0,[z13,z7,z350,z3,z5,z6])],[(0,[z7,z117,z1,z2,z3,z6]),(0,[z7,z148,z2,z3,z5,z173]),(0,[z88,z1,z2,z720,z5,z6]),(0,[z7,z254,z2,z211,z5,z6])],[(0,[z7,z1,z164,z3,z267,z6]),(0,[z7,z116,z2,z3,z5,z6]),(0,[z7,z1,z2,z277,z249,z6])]],
   [[(0,[z7,z1,z3,z1080,z5,z6]),(0,[z91,z1,z2,z3,z5,z715]),(0,[z7,z1,z22,z3,z5,z209])],[(0,[z7,z1,z2,z3,z5,z1081]),(0,[z7,z1,z2,z3,z1082,z6]),(0,[z7,z254,z2,z3,z180,z6]),(0,[z7,z2,z711,z114,z5,z6]),(0,[z7,z104,z1,z2,z3,z940]),(0,[z7,z1,z98,z22,z5,z6])],[(0,[z7,z1,z2,z97,z5,z209])],[(0,[z7,z1,z2,z128,z924,z6])],[(0,[z7,z1,z2,z534,z5,z6])],[(0,[z7,z1,z3,z5,z6,z1083]),(0,[z25,z486,z1,z2,z5,z6]),(0,[z91,z7,z1,z2,z3,z353])],[(0,[z7,z542,z1,z264,z5,z6]),(0,[z12,z28,z1,z3,z5,z6]),(0,[z7,z21,z783,z3,z5,z6]),(0,[z7,z1,z2,z3,z6,z227]),(0,[z7,z1,z22,z3,z6,z67])],[(0,[z32,z45,z2,z3,z5,z6]),(0,[z7,z14,z565,z2,z5,z6]),(0,[z7,z90,z668,z2,z3,z6]),(0,[z7,z1,z2,z3,z100,z6])]],
   [[(0,[z7,z1,z2,z3,z1084,z6]),(0,[z7,z1,z134,z3,z5,z709])],[(0,[z7,z542,z1,z2,z5,z6]),(0,[z7,z1,z2,z1085,z5,z6]),(0,[z7,z1086,z2,z3,z5,z6]),(0,[z7,z254,z205,z3,z5,z6]),(0,[z7,z1,z2,z3,z1087,z6]),(0,[z7,z104,z1,z2,z97,z6]),(0,[z7,z1,z2,z3,z311,z67])],[(0,[z7,z1,z2,z3,z5,z1088]),(0,[z7,z1,z2,z3,z1089,z6]),(0,[z7,z1090,z1,z2,z3,z5]),(0,[z7,z1,z2,z105,z52,z6]),(0,[z7,z104,z1,z2,z3,z960]),(0,[z7,z1,z534,z5,z99,z6]),(0,[z7,z133,z1,z2,z6,z699])],[(0,[z1,z2,z87,z720,z5,z6]),(0,[z7,z1,z2,z1091,z5,z6]),(0,[z7,z1,z2,z3,z924,z6]),(0,[z7,z133,z1,z2,z237,z6]),(0,[z7,z1,z2,z5,z842,z65])],[(0,[z7,z264,z21,z3,z5,z6])],[(0,[z7,z1092,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z6,z1093]),(0,[z7,z453,z1,z2,z3,z67])],[(0,[z7,z1,z1094,z3,z5,z6]),(0,[z7,z1,z1095,z3,z5,z6]),(0,[z7,z294,z1,z205,z3,z5]),(0,[z7,z1,z2,z1096,z5,z6]),(0,[z7,z116,z208,z105,z5,z6]),(0,[z7,z31,z1,z22,z5,z6]),(0,[z932,z7,z22,z3,z5,z6])],[(0,[z225,z33,z2,z3,z5,z6]),(0,[z7,z14,z26,z2,z5,z6]),(0,[z1097,z1,z2,z3,z5,z6]),(0,[z7,z31,z1,z2,z5,z6])]],
   [[(0,[z7,z234,z148,z1,z2,z3]),(0,[z7,z1,z2,z3,z5,z190]),(0,[z7,z1,z205,z3,z5,z65]),(0,[z7,z31,z1,z2,z58,z6])],[(0,[z7,z1,z2,z1098,z5,z6]),(0,[z1099,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z1100,z5,z6]),(0,[z1,z2,z3,z723,z140,z6]),(0,[z7,z1,z2,z1101,z5,z6]),(0,[z7,z1,z2,z5,z1102,z6]),(0,[z7,z1,z2,z3,z353,z83]),(0,[z7,z1,z2,z58,z92,z343])],[(0,[z7,z1103,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z46]),(0,[z7,z658,z1,z2,z5,z65]),(0,[z7,z446,z1,z3,z99,z6]),(0,[z7,z1104,z1,z2,z5,z6])],[(0,[z7,z437,z2,z3,z5,z6]),(0,[z25,z1,z2,z54,z5,z6]),(0,[z7,z1105,z2,z3,z5,z6]),(0,[z91,z1,z454,z2,z3,z5]),(0,[z7,z1,z2,z3,z5,z1106]),(0,[z1107,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z6,z1108]),(0,[z7,z271,z2,z5,z341,z6]),(0,[z7,z1,z2,z5,z924,z6])],[(0,[z7,z1,z2,z3,z1109,z6]),(0,[z7,z1110,z2,z3,z5,z6]),(0,[z7,z106,z31,z1,z99,z6])],[(0,[z7,z14,z2,z604,z5,z6]),(0,[z7,z208,z1,z105,z5,z6]),(0,[z7,z106,z1,z3,z99,z292]),(0,[z7,z1,z2,z121,z58,z92])],[(0,[z7,z1,z22,z3,z5,z460])]],
   [[(0,[z7,z426,z117,z1,z2,z3]),(0,[z7,z1111,z2,z3,z5,z6])],[(0,[z7,z234,z542,z1,z2,z6]),(0,[z7,z1,z2,z1112,z5,z6]),(0,[z1,z2,z3,z723,z5,z6]),(0,[z7,z1,z2,z1113,z5,z6]),(0,[z7,z208,z1,z305,z105,z6])],[(0,[z7,z82,z1,z331,z5,z136])],[(0,[z7,z1,z2,z3,z5,z1114]),(0,[z7,z1,z2,z1115,z5,z6]),(0,[z7,z1116,z1,z2,z3,z6]),(0,[z7,z1,z2,z3,z5,z1117]),(0,[z7,z20,z2,z3,z740,z6]),(1,[z7,z1,z22,z101,z6])],[(0,[z7,z1,z60,z5,z6,z572]),(0,[z7,z1,z60,z277,z5,z6]),(1,[z7,z1,z2,z924,z6]),(0,[z7,z1118,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z767])],[(0,[z32,z416,z45,z2,z5,z6]),(0,[z7,z1,z2,z1119,z5,z6]),(0,[z7,z106,z1,z341,z99,z6]),(0,[z1,z2,z3,z5,z6,z1120]),(0,[z7,z1,z2,z669,z3,z67])],[(0,[z23,z1,z427,z3,z5,z6]),(0,[z7,z1,z1121,z3,z5,z6]),(0,[z1122,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z174,z492]),(0,[z7,z1,z2,z105,z5,z279]),(0,[z7,z1,z2,z97,z5,z626])],[(0,[z47,z1,z2,z141,z5,z78])]],
   [[(0,[z138,z32,z45,z3,z5,z6]),(0,[z7,z1,z2,z858,z5,z6]),(0,[z89,z1,z2,z3,z140,z6]),(0,[z7,z1,z2,z3,z1123,z6]),(0,[z7,z1,z2,z97,z64,z236])],[(0,[z7,z1124,z2,z3,z5,z6]),(0,[z7,z1125,z1,z3,z5,z6]),(0,[z7,z1,z2,z121,z5,z6])],[(0,[z47,z352,z1,z2,z3,z5]),(0,[z7,z90,z2,z3,z145,z6]),(0,[z7,z493,z1,z2,z3,z67]),(0,[z7,z1,z2,z3,z161,z92]),(0,[z7,z1,z2,z121,z58,z6])],[(0,[z33,z836,z2,z3,z5,z6]),(0,[z13,z7,z433,z3,z5,z6]),(0,[z1,z2,z806,z3,z5,z6]),(0,[z7,z14,z2,z711,z5,z6]),(0,[z7,z1,z2,z331,z353,z6]),(0,[z7,z1,z2,z127,z128,z6])],[(0,[z7,z1,z2,z5,z6,z1126]),(0,[z88,z1,z2,z87,z5,z46]),(0,[z7,z226,z2,z277,z5,z61]),(0,[z7,z600,z1,z2,z5,z65]),(0,[z7,z1,z1127,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z1128])],[(0,[z7,z234,z90,z2,z3,z6]),(0,[z7,z1,z2,z3,z1129,z6]),(0,[z7,z1,z2,z3,z52,z279]),(0,[z7,z1,z2,z3,z6,z1130])],[(0,[z7,z1,z2,z1131,z5,z6]),(0,[z7,z1,z2,z557,z5,z65])],[(0,[z7,z416,z26,z2,z5,z6]),(0,[z7,z48,z2,z141,z5,z6]),(0,[z7,z104,z1,z2,z6,z65]),(1,[z7,z1,z3,z803,z6]),(0,[z7,z31,z2,z5,z275,z6]),(0,[z7,z2,z1033,z3,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 543) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 543).take 540) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1083).take 23) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1106)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [543, 540, 23] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 131).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 131).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 248).take 8).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [131, 117, 8] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_39815

theorem PEqualNP.Outside.L_meta_39815 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4007714944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4007714944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39815.solve