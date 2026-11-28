import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39087

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
  Nat.testBit (4276813544 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0002018500812948#64 ++ 0x24000806140204a5#64 ++ 0x809e038f018fffff#64 ++ 0xfa02780e3c063fff#64 : BitVec 256),
   (0x01290c3286349491#64 ++ 0x1804a430ca18d252#64 ++ 0xa3691c738e749cf7#64 ++ 0x768da471ce39d273#64 : BitVec 256),
   (0x04516058b058c622#64 ++ 0x5011458162c16318#64 ++ 0xdc71e07cf078e72e#64 ++ 0xef71c781f3c1e39c#64 : BitVec 256),
   (0x1a81b680db80f804#64 ++ 0x606a06da036e03e0#64 ++ 0xff81ff80ff80f81d#64 ++ 0xdffe07fe03fe03e0#64 : BitVec 256),
   (0x0ffc00006d6e0007#64 ++ 0x803ff00001b5b800#64 ++ 0x9ffe0000ffff003c#64 ++ 0x3e7ff80003fffc00#64 : BitVec 256),
   (0x2ffedb6f00000038#64 ++ 0x00bffb6dbc000000#64 ++ 0xefffffff00000003#64 ++ 0xffbffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [8, 7]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000049cf4 0x0000000000001273

def z1 : W := mkw 0x0002018500812948 0x24000806140204a5 0x809e038f018fffff 0xfa02780e3c063fff

def z2 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c738e749cf7 0x768da471ce39d273

def z3 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e07cf078e72e 0xef71c781f3c1e39c

def z4 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0000ffff003c 0x3e7ff80003fffc00

def z5 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff80f81d 0xdffe07fe03fe03e0

def z6 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff00000003 0xffbffffffc000000

def z7 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3611c708e708426 0x668d8471c239c210

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0x001e0000000f0020 0x2000780000003c00

def z9 : W := mkw 0x000000006d6e0007 0x8000000001b5b800 0x909e0000ffff003c 0x3a42780003fffc00

def z10 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0x6f61fc7000000000 0x05bd87f1c0000000

def z11 : W := mkw 0x1a80b6805b807804 0x606a02da016e01e0 0x7f80ff807f807819 0x99fe03fe01fe01e0

def z12 : W := mkw 0x2bae9b2700000018 0x00aeba6c9c000000 0xa3ef1ff300000003 0x768fbc7fcc000000

def z13 : W := mkw 0x0ed56058f95ac626 0xd03b558163e56b18 0xdcf7e07cf1fbe72e 0xef73df81f3c7ef9c

def z14 : W := mkw 0x0a80000049000004 0x002a000001240000 0x9f800000ff80001c 0x1e7e000003fe0000

def z15 : W := mkw 0x1ffdb680ffeef807 0xe07ff6da03ffbbe0 0xffffff80fffff83d 0xfffffffe03ffffe0

def z16 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0x6001ffff00000003 0xc18007fffc000000

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0x8008000300049cf7 0x720020000c001273

def z18 : W := mkw 0x0002018500812948 0x24000806140204a5 0x0096038c018b6308 0x8802580e30062d8c

def z19 : W := mkw 0x0001001080108400 0x1000040042004210 0x8061007080708426 0x66018401c201c210

def z20 : W := mkw 0x01280c2206241091 0x0804a03088189042 0x23081c030e0418d1 0x108c20700c381063

def z21 : W := mkw 0x0128000004240001 0x0004a00000109000 0x0068000000740020 0x2001a0000001d000

def z22 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7c81ff807180f809 0xc9f207fe01c603e0

def z23 : W := mkw 0x2ed6d34d00000028 0x00bb5b4d34000000 0x4c96e38c00000000 0x89325b8e30000000

def z24 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xffffffffffff003f 0xfffffffffffffc00

def z25 : W := mkw 0x000000006d6e0007 0x8000000001b5b800 0x10000000ffff003c 0x0040000003fffc00

def z26 : W := mkw 0x0bac00004d260005 0x802eb00001349800 0x038e00000f870010 0x100e3800003e1c00

def z27 : W := mkw 0x2bae9b2700000018 0x00aeba6c9c000000 0x238e1f8300000001 0x108e387e0c000000

def z28 : W := mkw 0x1001b6809280f800 0x604006da024a03e0 0x6001ff800000f801 0xc18007fe000003e0

def z29 : W := mkw 0x05796c7ab67cd6b3 0x5815e5b1ead9f35a 0xff79fc7ffe7cffff 0xfffde7f1fff9f3ff

def z30 : W := mkw 0x000305858281b948 0x24000c16160a06e5 0xa39f1f8f8f8fffff 0xfe8e7c7e3e3e3fff

def z31 : W := mkw 0x0128082200000010 0x0004a02088000000 0xa3691c7300000003 0x768da471cc000000

def z32 : W := mkw 0x057e018524ef294b 0xa415f8061493bca5 0x80fe038f01ffffff 0xfa03f80e3c07ffff

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0x8010000c0008e72e 0xea0040003000239c

def z34 : W := mkw 0x045361ddb0d9ef6a 0x74114d8776c367bd 0xdcffe3fff1ffffff 0xff73ff8fffc7ffff

def z35 : W := mkw 0x2ffedbef00812978 0x24bffb6fbc0204a5 0xefffffff018fffff 0xffbffffffc063fff

def z36 : W := mkw 0x0ffd0c32ef7e9497 0x983ff430cbbdfa52 0xbfff1c73ffff9cff 0x7efffc71cffffe73

def z37 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0x7f01fc00fe000000 0x05fc07f003f80000

def z38 : W := mkw 0x0450405820580622 0x1011410160816018 0x0070007c00780722 0x2001c001f001e01c

def z39 : W := mkw 0x01292c329634d491 0x5804a4b0ca58d352 0xff69fc73fe74fcff 0xfffda7f1cff9d3f3

def z40 : W := mkw 0x0002018500812948 0x24000806140204a5 0x8080038f0180ffdf 0xda02000e3c0603ff

def z41 : W := mkw 0x0ed400006d6e0007 0x803b500001b5b800 0x1c960000ffff003c 0x0872580003fffc00

def z42 : W := mkw 0x0003059586b5bdc9 0x3c000c16561ad6f7 0x809e038f8fffffff 0xfa02780e3e3fffff

def z43 : W := mkw 0x000160589010c620 0x5000058162404318 0x4001e07c0000e702 0xc1000781f000039c

def z44 : W := mkw 0x0ffd6058fd7ec627 0xd03ff58163f5fb18 0xdfffe07cffffe73e 0xff7fff81f3ffff9c

def z45 : W := mkw 0x045241cd00812968 0x24114907340204a5 0xccffe3ff018fffff 0xff33ff8ffc063fff

def z46 : W := mkw 0x0450404800000020 0x0011410120000000 0xcc71e07c00000002 0xef31c781f0000000

def z47 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe000cffffe73e 0xfe7ff80033ffff9c

def z48 : W := mkw 0x000160589010c620 0x5000058162404318 0x4001e07000000000 0x01000781c0000000

def z49 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3ff1c738fff9cff 0x7e8ffc71ce3ffe73

def z50 : W := mkw 0x2fffdf7f863494b9 0x18bfff7dfe18d252 0xefffffff8e749cf7 0xffbffffffe39d273

def z51 : W := mkw 0x1a8297854b81394c 0x246a0a5e152e04e5 0xa39e1f8f0f8fffff 0xfa8e787e3c3e3fff

def z52 : W := mkw 0x0450405820580622 0x1011410160816018 0x9c70007cf078072e 0x2e71c001f3c1e01c

def z53 : W := mkw 0x2ffcda6a6d6e0037 0x80bff369a9b5b800 0x7f61fc70fe700000 0x05fd87f1c3f9c000

def z54 : W := mkw 0x012b0db786b5bdd9 0x3c04ac36de1ad6f7 0xa3ff1fff8fffffff 0xfe8ffc7ffe3fffff

def z55 : W := mkw 0x0002018500812948 0x24000806140204a5 0x8096038c018bfb1d 0xda02580e30062fec

def z56 : W := mkw 0x2ffe496f6d6e003f 0x80bff925bdb5b800 0x9ffe007fffff003e 0x3e7ff801fffffc00

def z57 : W := mkw 0x1ba9beb2dfb4fc95 0x786ea6facb7ed3f2 0xffe1fff0fff0f81d 0xdfff87ffc3ffc3e0

def z58 : W := mkw 0x2ed6db6f00000038 0x00bb5b6dbc000000 0x6c97ffff00000003 0xc9b25ffffc000000

def z59 : W := mkw 0x0002010500010148 0x0400080414000405 0x801e000f000fe7ee 0xea0078003c003f9f

def z60 : W := mkw 0x2002496f00000038 0x00800925bc000000 0x0000007f00000002 0x00000001fc000000

def z61 : W := mkw 0x00010c3286349491 0x18000430ca18d252 0x20011c738e749cf7 0x40800471ce39d273

def z62 : W := mkw 0x01290c2282009010 0x0004a4308a080240 0xa3691c738e009817 0x768da471ce380260

def z63 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1f600000fe700000 0x047d800003f9c000

def z64 : W := mkw 0x0002010500010148 0x0400080414000405 0x001e000f000f07e2 0x200078003c003c1f

def z65 : W := mkw 0x0000008000812940 0x24000002000204a5 0x00000000018ffffc 0x0000000000063fff

def z66 : W := mkw 0x0002018500812948 0x24000806140204a5 0x8096038c018be72e 0xea02580e30062f9c

def z67 : W := mkw 0x10012490dfb4fc85 0x78400492437ed3f2 0x10000000fff4fcfc 0x0040000003ffd3f3

def z68 : W := mkw 0x0450000020480002 0x0011400000812000 0x9c700000f078002c 0x2e71c00003c1e000

def z69 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c71e07cf0786308 0x8d71c781f3c1e18c

def z70 : W := mkw 0x0a82930500000008 0x002a0a4c14000000 0xef9fff8f00000003 0xffbe7ffe3c000000

def z71 : W := mkw 0x00010c3282109490 0x18000430ca084252 0xa0611c7380709ce7 0x66818471ce01c273

def z72 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdcffe07cf1ffe73e 0xff73ff81f3c7ff9c

def z73 : W := mkw 0x1ba9bea2db80f814 0x606ea6fa8b6e03e0 0xffe9fff3ff80f81f 0xffffa7ffcffe03e0

def z74 : W := mkw 0x0128000000000000 0x0004a00000000000 0x8368000000000000 0x360da00000000000

def z75 : W := mkw 0x3a83ffefdb80f83c 0x60ea0fffbf6e03e0 0xff81ffffff80f81f 0xdffe07fffffe03e0

def z76 : W := mkw 0x0000008000802800 0x20000002000200a0 0x808003800180f81d 0xda02000e000603e0

def z77 : W := mkw 0x1a83b785db81f94c 0x646a0ede176e07e5 0xff9fff8fff8fffff 0xfffe7ffe3ffe3fff

def z78 : W := mkw 0x1003b7859281f948 0x64400ede164a07e5 0x6001ff8f0000ffc3 0xc18007fe3c0003ff

def z79 : W := mkw 0x2456414d00000028 0x0091590534000000 0x0016000c00000000 0x0000580030000000

def z80 : W := mkw 0x057c0000246e0003 0x8015f0000091b800 0x007e0000007f0020 0x2001f8000001fc00

def z81 : W := mkw 0x0a80920000000000 0x002a024800000000 0xef81ff8000000001 0xdfbe07fe00000000

def z82 : W := mkw 0x257e496f00000038 0x0095f925bc000000 0x007e007f00000002 0x2001f801fc000000

def z83 : W := mkw 0x1badb680dfa6f805 0xe06eb6da037e9be0 0xff8fff80ff87f81d 0xdffe3ffe03fe1fe0

def z84 : W := mkw 0x2ffffb7ffd7ec63f 0xd0bfffedfff5fb18 0xffffffffffffe73f 0xffffffffffffff9c

def z85 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f81ff80ff801811 0x15fe07fe03fe0060

def z86 : W := mkw 0x1ed1f2d8f9d8ee26 0x707b47cb63e763b8 0xdcf1e3fcf1f8e72e 0xef73c78ff3c7e39c

def z87 : W := mkw 0x000000004d260005 0x8000000001349800 0x000000000f870010 0x00000000003e1c00

def z88 : W := mkw 0x1ed1f6d8fbd8fe26 0x707b47db63ef63f8 0xfff1fffcfff8ff3f 0xffffc7fff3ffe3fc

def z89 : W := mkw 0x1ffdb680db80f804 0x607ff6da036e03e0 0xffffff80ff80f81d 0xfffffffe03fe03e0

def z90 : W := mkw 0x00012010b058c602 0x5000048042c16318 0x10000000f078e72c 0x0040000003c1e39c

def z91 : W := mkw 0x2ffedb6f4900003c 0x00bffb6dbd240000 0xffffffffff80001f 0xfffffffffffe0000

def z92 : W := mkw 0x0002018500812948 0x24000806140204a5 0x008e0383018718d1 0x1002380e0c061c63

def z93 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c61e070f0700000 0x05718781c3c1c000

def z94 : W := mkw 0x0450404800000020 0x0011410120000000 0x4c10e00c00000000 0x8930438030000000

def z95 : W := mkw 0x0ed0000069480006 0x003b400001a52000 0x9ff00000fff8003c 0x3e7fc00003ffe000

def z96 : W := mkw 0x0002018500812948 0x24000806140204a5 0x0000038f0000ffc3 0xc000000e3c0003ff

def z97 : W := mkw 0x2a86930500000008 0x00aa1a4c14000000 0x0086038000000000 0x0002180e00000000

def z98 : W := mkw 0x0000008000802800 0x20000002000200a0 0x808803830184fcff 0xfa02200e0c0613f3

def z99 : W := mkw 0x0002010500000008 0x0000080414000000 0x809e038f018f003f 0xfa02780e3c063c00

def z100 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0xe09fffff00000003 0xfb827ffffc000000

def z101 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x03fe00000fff0030 0x300ff800003ffc00

def z102 : W := mkw 0x10012490fbd8fe06 0x7040049243ef63f8 0x10000000fff8ff3c 0x0040000003ffe3fc

def z103 : W := mkw 0x1ba99eb2cfb4bc95 0x386ea67acb3ed2f2 0xa3e91ff38ff49cf7 0x768fa47fce3fd273

def z104 : W := mkw 0x0ffe018500812948 0x243ff806140204a5 0x8ffe038f018fffff 0xfe3ff80e3c063fff

def z105 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xfffffffffe700003 0xfffffffffff9c000

def z106 : W := mkw 0x0ed40000694a0006 0x803b500001a52800 0x1c960000718b0008 0x0872580001c62c00

def z107 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x6381ff800f80f811 0xd18e07fe003e03e0

def z108 : W := mkw 0x0000008000802800 0x20000002000200a0 0x809e0380018ff83d 0xfa02780e00063fe0

def z109 : W := mkw 0x2fffff7fb67cd6bb 0x58bffffdfed9f35a 0xfffffffffe7cffff 0xfffffffffff9f3ff

def z110 : W := mkw 0x0002018500812948 0x24000806140204a5 0x8008038f0004fff7 0xf200200e3c0013ff

def z111 : W := mkw 0x2ffdde7a863494b1 0x18bff779ea18d252 0x6f61fc708e700000 0x05bd87f1c239c000

def z112 : W := mkw 0x0128082204240011 0x0004a02088109000 0xa3691c738e740037 0x768da471ce39d000

def z113 : W := mkw 0x0ffd2000fd6ec007 0xc03ff48003f5bb00 0xdfffe000ffffe03c 0xff7fff8003ffff80

def z114 : W := mkw 0x1ed1f6c8db80f824 0x607b47db236e03e0 0xfff1fffcff80f81f 0xffffc7fff3fe03e0

def z115 : W := mkw 0x0002018500812948 0x24000806140204a5 0x809e038f0000ffc3 0xfa02780e3c0003ff

def z116 : W := mkw 0x0ba99e3286349491 0x182ea678ca18d252 0xefe9fff38e749cf7 0xffbfa7ffce39d273

def z117 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3791c7f8e7cffff 0xfe8de471fe39f3ff

def z118 : W := mkw 0x0ffc40586d7e0627 0x903ff10161b5f818 0x9ffe007cffff073e 0x3e7ff801f3fffc1c

def z119 : W := mkw 0x10012480db80f804 0x60400492036e03e0 0xdc01e000ff80f81c 0xcf70078003fe03e0

def z120 : W := mkw 0x0000082200000010 0x0000002088000000 0x20011c7300000003 0x40800471cc000000

def z121 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23611c708e700000 0x048d8471c239c000

def z122 : W := mkw 0x0128000004240001 0x0004a00000109000 0x836800008e740034 0x360da0000239d000

def z123 : W := mkw 0x0001040082009000 0x0000041002080240 0xa3011c008e009815 0x568c047002380260

def z124 : W := mkw 0x1ba9beb2dfb4fc95 0x786ea6facb7ed3f2 0xffe9fff3fff4fcff 0xffffa7ffcfffd3f3

def z125 : W := mkw 0x012a09a700812958 0x2404a8269c0204a5 0xa3ff1fff018fffff 0xfe8ffc7ffc063fff

def z126 : W := mkw 0x2452db6f00000038 0x00914b6dbc000000 0xec71ffff00000003 0xefb1c7fffc000000

def z127 : W := mkw 0x0450404820480022 0x0011410120812000 0xdc71e07cf078002e 0xef71c781f3c1e000

def z128 : W := mkw 0x2bae9b2700000018 0x00aeba6c9c000000 0xa39e1f8f00000003 0xfa8e787e3c000000

def z129 : W := mkw 0x012b0d37863595d9 0x1c04ac34de18d657 0xa37f1c7f8e7f9ff7 0x768dfc71fe39fe7f

def z130 : W := mkw 0x0000405800100620 0x1000010160004018 0x0000007c00000702 0x00000001f000001c

def z131 : W := mkw 0x0450404800000020 0x0011410120000000 0x0070007c00000002 0x2001c001f0000000

def z132 : W := mkw 0x0000008000802800 0x20000002000200a0 0x0080038001806008 0x8802000e00060180

def z133 : W := mkw 0x2ffedbef6def297f 0xa4bffb6fbdb7bca5 0xffffffffffffffff 0xffffffffffffffff

def z134 : W := mkw 0x0450604830484222 0x4011418120c12108 0x5c00e00070000000 0x0170038001c00000

def z135 : W := mkw 0x0001041086349481 0x180004104218d252 0x000000008e749cf4 0x000000000239d273

def z136 : W := mkw 0x012b0db786b5bdd9 0x3c04ac36de1ad6f7 0xa3691fff8e74fff7 0xf68da47ffe39d3ff

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0x830000008e000014 0x160c000002380000

def z138 : W := mkw 0x057c0832247e0493 0x9815f020c891f812 0x007e0073007f04e2 0x2001f801cc01fc13

def z139 : W := mkw 0x2ffffb7fb058c63a 0x50bfffedfec16318 0xfffffffff078e72f 0xffffffffffc1e39c

def z140 : W := mkw 0x1a8096004b001004 0x006a0258012c0040 0x23001c000e000000 0x008c007000380000

def z141 : W := mkw 0x0000000000000000 0x0000000000000000 0x809e0000018f003c 0x3a02780000063c00

def z142 : W := mkw 0x1a80b28059806804 0x606a02ca016601a0 0x5c80e38071806008 0x8972038e01c60180

def z143 : W := mkw 0x0ffc08326d7e0497 0x983ff020c9b5f812 0x9ffe0073ffff04fe 0x3e7ff801cffffc13

def z144 : W := mkw 0x0002018500812948 0x24000806140204a5 0x0000038c00006300 0x8000000e3000018c

def z145 : W := mkw 0x0ffc0c226f6e1097 0x883ff03089bdb842 0xbffe1c03ffff18fd 0x3efff8700ffffc63

def z146 : W := mkw 0x0ffc40486d6e0027 0x803ff10121b5b800 0xdfffe07cffff003e 0xff7fff81f3fffc00

def z147 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x20691c7300749ce3 0x6081a471cc01d273

def z148 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23691c738e7418d1 0x148da471ce39d063

def z149 : W := mkw 0x04514058a0588622 0x1011450162816218 0x8071007c80788726 0x6601c401f201e21c

def z150 : W := mkw 0x000120009000c000 0x4000048002400300 0xdc01e000f000e00c 0xcf70078003c00380

def z151 : W := mkw 0x0002010500010148 0x0400080414000405 0x809e000f018f07fe 0x3a0278003c063c1f

def z152 : W := mkw 0x0128000004240001 0x0004a00000109000 0x036000008e700000 0x040d80000239c000

def z153 : W := mkw 0x045261cd30c96b6a 0x6411498734c325ad 0xdc9ee38f718fffff 0xfb727b8e3dc63fff

def z154 : W := mkw 0x0ffc920000000000 0x003ff24800000000 0xefffff8000000001 0xffbffffe00000000

def z155 : W := mkw 0x3ed6f3cd5980682c 0x60fb5bcf356601a0 0x5c96e38c71806008 0x89725b8e31c60180

def z156 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6ff7fffc00000000 0x8dbfdffff0000000

def z157 : W := mkw 0x1a80b28059806804 0x606a02ca016601a0 0xdc80e3807180f81d 0xdb72038e01c603e0

def z158 : W := mkw 0x0000200010004000 0x4000008000400100 0x5c00e00070006008 0x8970038001c00180

def z159 : W := mkw 0x2003df7f821094b8 0x18800f7dfe084252 0x6001ffff00009cc3 0xc18007fffc000273

def z160 : W := mkw 0x0450604830484222 0x4011418120c12108 0x5c10e00c70086308 0x8970438031c0218c

def z161 : W := mkw 0x0002018500812948 0x24000806140204a5 0x001e000f018ffffe 0x200078003c063fff

def z162 : W := mkw 0x0450000000000000 0x0011400000000000 0x8c70000000000000 0x2e31c00000000000

def z163 : W := mkw 0x0bac00004d260005 0x802eb00001349800 0x9f8e0000ff87001c 0x1e7e380003fe1c00

def z164 : W := mkw 0x0000008000812940 0x24000002000204a5 0x000000000000ffc0 0x00000000000003ff

def z165 : W := mkw 0x2ffdde7a863494b1 0x18bff779ea18d252 0xef69fc738e749cf7 0x77bda7f1ce39d273

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc01e00000000000 0xcf30078000000000

def z167 : W := mkw 0x3fffffef9280f838 0x60ffffffbe4a03e0 0xefffffff0000f803 0xffbffffffc0003e0

def z168 : W := mkw 0x0ffc000000000000 0x003ff00000000000 0x8ffe000000000000 0x3e3ff80000000000

def z169 : W := mkw 0x0a80920049000004 0x002a024801240000 0xff81ff80ff80001d 0xdffe07fe03fe0000

def z170 : W := mkw 0x3ffdfe6adb00d034 0x40fff7f9ab6c0340 0x7f61fc70fe000000 0x05fd87f1c3f80000

def z171 : W := mkw 0x10012480db80f804 0x60400492036e03e0 0x10000000ff80f81c 0x0040000003fe03e0

def z172 : W := mkw 0x3fffffefdb80f83c 0x60ffffffbf6e03e0 0xffffffffff80f81f 0xfffffffffffe03e0

def z173 : W := mkw 0x2002dbef00812978 0x24800b6fbc0204a5 0xe09fffff018fffff 0xfb827ffffc063fff

def z174 : W := mkw 0x257e496f00000038 0x0095f925bc000000 0xcc7fe07f00000002 0xef31ff81fc000000

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000018f003c 0x0000000000063c00

def z176 : W := mkw 0x0ed0d24800000020 0x003b434920000000 0xeff1fffc00000003 0xffbfc7fff0000000

def z177 : W := mkw 0x01290c3282109490 0x1804a430ca084252 0xa3691c7300009cc3 0x768da471cc000273

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0x00960000018b0008 0x0802580000062c00

def z179 : W := mkw 0x0128083204340491 0x1804a020c810d012 0x00680073007404e2 0x2001a001cc01d013

def z180 : W := mkw 0x3ed7f7cddb80f82c 0x60fb5fdf376e03e0 0xff97ff8cff80f81d 0xdffe5ffe33fe03e0

def z181 : W := mkw 0x0002010500000008 0x0000080414000000 0x0000038f00000003 0xc000000e3c000000

def z182 : W := mkw 0x1a812480db80f804 0x606a0492036e03e0 0x9f800000ff80f81c 0x1e7e000003fe03e0

def z183 : W := mkw 0x2ffffb7fb058c63a 0x50bfffedfec16318 0xfffffffff0700003 0xffffffffffc1c000

def z184 : W := mkw 0x0ffe01056d6f014f 0x843ff80415b5bc05 0x9ffe000fffff07fe 0x3e7ff8003ffffc1f

def z185 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0xefe1fff000000001 0xdfbf87ffc0000000

def z186 : W := mkw 0x2ffedb6f694a003e 0x80bffb6dbda52800 0xffffffff718b000b 0xfffffffffdc62c00

def z187 : W := mkw 0x2baedb6f00000038 0x00aebb6dbc000000 0x638fffff00000003 0xd18e3ffffc000000

def z188 : W := mkw 0x2ffedb6f4d26003d 0x80bffb6dbd349800 0xefffffff0f870013 0xffbffffffc3e1c00

def z189 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff91ff8cff88ff3f 0xfffe47fe33fe23fc

def z190 : W := mkw 0x1a819680cb80b804 0x206a065a032e02e0 0xa3811f808f809815 0x568e047e023e0260

def z191 : W := mkw 0x01296c7a9634d6b1 0x5804a5b1ea58d35a 0xe369fc7f8e74fff7 0xf78da7f1fe39d3ff

def z192 : W := mkw 0x2ffcda6a6d6e0037 0x80bff369a9b5b800 0xfffffc70ffff003c 0x3ffffff1c3fffc00

def z193 : W := mkw 0x04516048b048c222 0x4011458122c12308 0xdc11e00cf008e30c 0xcf70478033c0238c

def z194 : W := mkw 0x1a8096804b803804 0x206a025a012e00e0 0x23801f800f801811 0x108e007e003e0060

def z195 : W := mkw 0x0002010500010148 0x0400080414000405 0x0016000c000b0300 0x0000580030002c0c

def z196 : W := mkw 0x0ffc00806def2947 0xa43ff00201b7bca5 0x9ffe0000fffffffc 0x3e7ff80003ffffff

def z197 : W := mkw 0x00010c3282109490 0x18000430ca084252 0x20011c7300009cc3 0x40800471cc000273

def z198 : W := mkw 0x0bac000000000000 0x002eb00000000000 0x038e000000000000 0x100e380000000000

def z199 : W := mkw 0x2bae9ba700812958 0x24aeba6e9c0204a5 0xa39e1f8f018fffff 0xfa8e787e3c063fff

def z200 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0003ffff9cff 0x7e7ff8000ffffe73

def z201 : W := mkw 0x0579687ab47cc6b3 0x5815e5a1ead1f31a 0xdc79e07ff07ce7ee 0xef71e781ffc1f39f

def z202 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6f9eff8f00000001 0x99be7bfe3c000000

def z203 : W := mkw 0x0001041086349481 0x180004104218d252 0x806100708e749cf6 0x66018401c239d273

def z204 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6feffff300000001 0x15bfbfffcc000000

def z205 : W := mkw 0x045160d8b0d8ee22 0x7011458362c363b8 0xdcf1e3fcf1f8ff3f 0xff73c78ff3c7e3fc

def z206 : W := mkw 0x1a83b785db80f80c 0x606a0ede176e03e0 0xff9fff8fff80f81f 0xfffe7ffe3ffe03e0

def z207 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1cfe000071ff0028 0x2873f80001c7fc00

def z208 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x5c80e380ff80f81c 0x8972038e03fe03e0

def z209 : W := mkw 0x05796c7ab67cd6b3 0x5815e5b1ead9f35a 0xff71fc7cfe78e72e 0xeffdc7f1f3f9e39c

def z210 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff9fff80ff8ff83d 0xfffe7ffe03fe3fe0

def z211 : W := mkw 0x2ffedbef00802838 0x20bffb6fbc0200a0 0xefffffff0180f81f 0xffbffffffc0603e0

def z212 : W := mkw 0x0000200030484202 0x4000008000c12108 0x1000000070086308 0x0040000001c0218c

def z213 : W := mkw 0x0002010500000008 0x0000080414000000 0x809e038f0008e72f 0xfa02780e3c00239c

def z214 : W := mkw 0x00030db78291bdd8 0x3c000c36de0a46f7 0x20011fff0000ffc3 0xc080047ffc0003ff

def z215 : W := mkw 0x0a80000049000004 0x002a000001240000 0x1f000000fe000000 0x047c000003f80000

def z216 : W := mkw 0x1ed5b680fbcaf806 0xe07b56da03ef2be0 0xff97ff80ff8bf81d 0xdffe5ffe03fe2fe0

def z217 : W := mkw 0x0002018500812948 0x24000806140204a5 0x0000038f018fffff 0xc000000e3c063fff

def z218 : W := mkw 0x0ffe01856def294f 0xa43ff80615b7bca5 0x9ffe038fffffffff 0xfe7ff80e3fffffff

def z219 : W := mkw 0x0002018500812948 0x24000806140204a5 0x808e038301879cf7 0x7202380e0c061e73

def z220 : W := mkw 0x0000000004240001 0x0000000000109000 0x000000008e740034 0x000000000239d000

def z221 : W := mkw 0x0000920000000000 0x0000024800000000 0x6001ff8000000001 0xc18007fe00000000

def z222 : W := mkw 0x3fffffefdb81f97c 0x64ffffffbf6e07e5 0xffffffffff8fffff 0xfffffffffffe3fff

def z223 : W := mkw 0x2ffedb6f04240039 0x00bffb6dbc109000 0xefffffff8e740037 0xffbffffffe39d000

def z224 : W := mkw 0x04510010a0588402 0x1011440042816210 0x9c710070f078842e 0x6e71c401c3c1e210

def z225 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c10e00cf078e72c 0x8970438033c1e39c

def z226 : W := mkw 0x2ffedb6f2048003a 0x00bffb6dbc812000 0xfffffffff078002f 0xffffffffffc1e000

def z227 : W := mkw 0x0bac00004d260005 0x802eb00001349800 0x030000000e000000 0x000c000000380000

def z228 : W := mkw 0x1ffdb680ffeef807 0xe07ff6da03ffbbe0 0xffe1ff80fff0f81d 0xdfff87fe03ffc3e0

def z229 : W := mkw 0x0000000000000000 0x0000000000000000 0x8060000080700024 0x260180000201c000

def z230 : W := mkw 0x1001b6809280f800 0x604006da024a03e0 0xfc01ff80f000f80d 0xcff007fe03c003e0

def z231 : W := mkw 0x257edb6f00000038 0x0095fb6dbc000000 0x607fffff00000003 0xe181fffffc000000

def z232 : W := mkw 0x0002018500812948 0x24000806140204a5 0x00000383000018c1 0x0000000e0c000063

def z233 : W := mkw 0x1ff9fefafffcfeb7 0x787fe7fbebfff3fa 0xfff9fffffffcffff 0xffffe7fffffff3ff

def z234 : W := mkw 0x0000000000000000 0x0000000000000000 0x9c000000f000000c 0x0e70000003c00000

def z235 : W := mkw 0x1001f6d89290fe20 0x704007db624a43f8 0x6001fffc0000ff03 0xc18007fff00003fc

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0x00080003000418d1 0x100020000c001063

def z237 : W := mkw 0x000301958091ad48 0x34000c06560246b5 0x80ff03ff81ffffff 0xfe03fc0ffe07ffff

def z238 : W := mkw 0x3fffffffdfb4fcbd 0x78ffffffff7ed3f2 0xfffffffffff4fcff 0xffffffffffffd3f3

def z239 : W := mkw 0x01290c32ef7e9497 0x9804a430cbbdfa52 0xb3691c73ffff9cff 0x76cda471cffffe73

def z240 : W := mkw 0x0000008000802800 0x20000002000200a0 0x0080038001801811 0x1002000e00060060

def z241 : W := mkw 0x0000040002001000 0x0000001000080040 0x23001c000e001811 0x108c007000380060

def z242 : W := mkw 0x2ffedf6f062410b9 0x08bffb7dbc189042 0xefffffff0e0418d3 0xffbffffffc381063

def z243 : W := mkw 0x0ed40000694a0006 0x803b500001a52800 0x9f960000ff8b001c 0x1e7e580003fe2c00

def z244 : W := mkw 0x257e496f246e003b 0x8095f925bc91b800 0x007e007f007f0022 0x2001f801fc01fc00

def z245 : W := mkw 0x1a82b3855981694c 0x646a0ace156605a5 0x5c96e38c718b6308 0x89725b8e31c62d8c

def z246 : W := mkw 0x1001beb29290fc90 0x784006faca4a43f2 0x6001fff30000fcc3 0xc18007ffcc0003f3

def z247 : W := mkw 0x0452018520c9294a 0x24114806148324a5 0x9cfe038ff1ffffff 0xfe73f80e3fc7ffff

def z248 : W := mkw 0x0ffc404800000020 0x003ff10120000000 0xcfffe07c00000002 0xff3fff81f0000000

def z249 : W := mkw 0x0001001080108400 0x1000040042004210 0x8071007c8078e72e 0xee01c401f201e39c

def z250 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3611c708e709815 0x568d8471c239c260

def z251 : W := mkw 0x0453615db059c76a 0x54114d8576c1671d 0xdc7fe07ff07fe7ee 0xef71ff81ffc1ff9f

def z252 : W := mkw 0x2ffedb6f00010178 0x04bffb6dbc000405 0xefffffff000f07e3 0xffbffffffc003c1f

def z253 : W := mkw 0x0ed40000694a0006 0x803b500001a52800 0x9cf60000f1fb002c 0x2e73d80003c7ec00

def z254 : W := mkw 0x2ed6d34d00000028 0x00bb5b4d34000000 0xccf7e3fc00000002 0xef33df8ff0000000

def z255 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff00049cf7 0xffbffffffc001273

def z256 : W := mkw 0x0000000000000000 0x0000000000000000 0x008e000001870010 0x1002380000061c00

def z257 : W := mkw 0x045000006d6e0007 0x8011400001b5b800 0x9c700000ffff003c 0x2e71c00003fffc00

def z258 : W := mkw 0x2ffe496f00000038 0x00bff925bc000000 0x8ffe007f00000002 0x3e3ff801fc000000

def z259 : W := mkw 0x0452414d00000028 0x0011490534000000 0xccffe3ff00000003 0xff33ff8ffc000000

def z260 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23611c738e709cc3 0x448d8471ce39c273

def z261 : W := mkw 0x0a80000000000000 0x002a000000000000 0x8f80000000000000 0x1e3e000000000000

def z262 : W := mkw 0x1ed4b28079ca6806 0xe07b52ca01e729a0 0x5c96e380718b6008 0x89725b8e01c62d80

def z263 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x1070007cf078e72e 0x2041c001f3c1e39c

def z264 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1fee0000fff70010 0x147fb80003ffdc00

def z265 : W := mkw 0x012b0d3786349499 0x1804ac34de18d252 0xa3ff1fff8e749cf7 0xfe8ffc7ffe39d273

def z266 : W := mkw 0x2a82db6f00000038 0x00aa0b6dbc000000 0xef81ffff00000003 0xdfbe07fffc000000

def z267 : W := mkw 0x0ffc92006d6e0007 0x803ff24801b5b800 0xffffff80ffff003d 0xfffffffe03fffc00

def z268 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000008e72c 0x000000000000239c

def z269 : W := mkw 0x0002018500812948 0x24000806140204a5 0x809e038f018b630b 0xfa02780e3c062d8c

def z270 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c71e07cf0780722 0x2571c781f3c1e01c

def z271 : W := mkw 0x0002018500812948 0x24000806140204a5 0x008e0383018ffffd 0x1002380e0c063fff

def z272 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1ff60000fffb0008 0x0c7fd80003ffec00

def z273 : W := mkw 0x1a81b690db90fc04 0x706a06da436e43f0 0xffe1fff0fff0fc3f 0xffff87ffc3ffc3f0

def z274 : W := mkw 0x0a80920000000000 0x002a024800000000 0x4c80e38000000000 0x8932038e00000000

def z275 : W := mkw 0x1ed1f658fb58d626 0x507b47d963ed6358 0x7f61fc70fe700000 0x05fd87f1c3f9c000

def z276 : W := mkw 0x00000000246e0003 0x800000000091b800 0x00000000007f0020 0x000000000001fc00

def z277 : W := mkw 0x0002010500000008 0x0000080414000000 0x809e038f00000003 0xfa02780e3c000000

def z278 : W := mkw 0x01280c2206241091 0x0804a03088189042 0x23001c000e000000 0x008c007000380000

def z279 : W := mkw 0x0002018500812948 0x24000806140204a5 0x0096038c018ffffc 0x8802580e30063fff

def z280 : W := mkw 0x0002010500010148 0x0400080414000405 0x809e038f000f07e3 0xfa02780e3c003c1f

def z281 : W := mkw 0x3ffffffffbd8fe3e 0x70ffffffffef63f8 0xfffffffffff8ff3f 0xffffffffffffe3fc

def z282 : W := mkw 0x0578487a247c06b3 0x1815e121e891f01a 0x0078007f007c07e2 0x2001e001fc01f01f

def z283 : W := mkw 0x0a812000d900c004 0x402a048003640300 0xdf81e000ff80e01c 0xdf7e078003fe0380

def z284 : W := mkw 0x012c000004260001 0x8004b00000109800 0x000e000000070000 0x0000380000001c00

def z285 : W := mkw 0x100004804b803804 0x20400012012e00e0 0x000000000f801810 0x00000000003e0060

def z286 : W := mkw 0x3bafbfa7db80f81c 0x60eebefe9f6e03e0 0xff8fff83ff80f81d 0xdffe3ffe0ffe03e0

def z287 : W := mkw 0x0001040082009000 0x0000041002080240 0xa3091c038e049cf7 0x768c24700e381273

def z288 : W := mkw 0x0000008000812940 0x24000002000204a5 0x80080003018fffff 0x720020000c063fff

def z289 : W := mkw 0x0002018500812948 0x24000806140204a5 0x001e038f000fffe3 0xe000780e3c003fff

def z290 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff0008e72f 0xffbffffffc00239c

def z291 : W := mkw 0x04512010b058c602 0x5011448042c16318 0x9c700000f078e72c 0x2e71c00003c1e39c

def z292 : W := mkw 0x0128000004240001 0x0004a00000109000 0x83fe00008fff003c 0x3e0ff800023ffc00

def z293 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff018f003f 0xffbffffffc063c00

def z294 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c11e07c7008e70a 0xc9704781f1c0239c

def z295 : W := mkw 0x1ffdf6d8fffefe27 0xf07ff7db63fffbf8 0xfffffffcffffff3f 0xfffffffff3fffffc

def z296 : W := mkw 0x0000008000812940 0x24000002000204a5 0x8010000c018ffffe 0xea00400030063fff

def z297 : W := mkw 0x057d0c32a67e9493 0x9815f430ca99fa52 0xa37f1c738e7f9cf7 0x768dfc71ce39fe73

def z298 : W := mkw 0x2ed6d34d00000028 0x00bb5b4d34000000 0xcc9ee38f00000003 0xfb327b8e3c000000

def z299 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6f61ffff00000003 0xc5bd87fffc000000

def z300 : W := mkw 0x0bac0c224f261095 0x882eb030893c9842 0x238e1c030f8718d1 0x108e38700c3e1c63

def z301 : W := mkw 0x000160589010c620 0x5000058162404318 0xc061e07c8070e726 0xe7018781f201c39c

def z302 : W := mkw 0x1a82b3855981694c 0x646a0ace156605a5 0xdc9ee38f718fffff 0xfb727b8e3dc63fff

def z303 : W := mkw 0x057b6dffb6fdfffb 0x7c15edb7fedbf7ff 0xffffffffffffffff 0xffffffffffffffff

def z304 : W := mkw 0x000160589010c620 0x5000058162404318 0xdc01e07cf000e70e 0xcf700781f3c0039c

def z305 : W := mkw 0x257f697fb058c63a 0x5095fda5fec16318 0xdc7fe07ff078e72e 0xef71ff81ffc1e39c

def z306 : W := mkw 0x0000404800000020 0x0000010120000000 0x4001e07c00000002 0xc1000781f0000000

def z307 : W := mkw 0x0000008000812940 0x24000002000204a5 0x00000000018b6308 0x0000000000062d8c

def z308 : W := mkw 0x0001040082009000 0x0000041002080240 0x23011c008e000000 0x048c047002380000

def z309 : W := mkw 0x00010c3282109490 0x18000430ca084252 0xa0091c7300049cf7 0x72802471cc001273

def z310 : W := mkw 0x1a81b680db81f944 0x646a06da036e07e5 0xff81ff80ff8ffffd 0xdffe07fe03fe3fff

def z311 : W := mkw 0x1ffcb2807dee6807 0xe07ff2ca01f7b9a0 0xdffee380ffff603c 0xbf7ffb8e03fffd80

def z312 : W := mkw 0x012800006d6e0007 0x8004a00001b5b800 0x93680000ffff003c 0x364da00003fffc00

def z313 : W := mkw 0x012a0937043505d9 0x1c04a824dc10d417 0x007e007f007f07e2 0x2001f801fc01fc1f

def z314 : W := mkw 0x0bae01854da7294d 0xa42eb80615369ca5 0x038e03830f8718d1 0x100e380e0c3e1c63

def z315 : W := mkw 0x0002018500812948 0x24000806140204a5 0x809e038c018f633c 0xba02780e30063d8c

def z316 : W := mkw 0x000120109010c400 0x5000048042404310 0xdc61e070f070e42e 0xef718781c3c1c390

def z317 : W := mkw 0x012a09b704b52dd9 0x3c04a826dc12d4b7 0x80fe03ff01ffffff 0xfa03f80ffc07ffff

def z318 : W := mkw 0x0000000000010140 0x0400000000000405 0x00000000000f07e0 0x0000000000003c1f

def z319 : W := mkw 0x0000083200100490 0x18000020c8004012 0x00000073000004c2 0x00000001cc000013

def z320 : W := mkw 0x0ffd6058fd7ec627 0xd03ff58163f5fb18 0x5f61e070fe700000 0x057d8781c3f9c000

def z321 : W := mkw 0x1a81f6d8db90fe24 0x706a07db636e43f8 0xff81fffcff80ff1f 0xdffe07fff3fe03fc

def z322 : W := mkw 0x1a8096804b803804 0x206a025a012e00e0 0xbf801f80ff80181d 0x1efe007e03fe0060

def z323 : W := mkw 0x0ed6018569cb294e 0xa43b580615a72ca5 0x1c96038c718b6308 0x8872580e31c62d8c

def z324 : W := mkw 0x0a80920000000000 0x002a024800000000 0x6f01fc0000000000 0x05bc07f000000000

def z325 : W := mkw 0x0452415d2059076a 0x141149057481641d 0x007e007f007f07e2 0x2001f801fc01fc1f

def z326 : W := mkw 0x0ffc08226d6e0017 0x803ff02089b5b800 0xbfff1c73ffff003f 0x7efffc71cffffc00

def z327 : W := mkw 0x1a81b690dfb4fc85 0x786a06da437ed3f2 0xff81ff80fff4fcfd 0xdffe07fe03ffd3f3

def z328 : W := mkw 0x000120009000c000 0x4000048002400300 0x5c01e000f0000000 0x0570078003c00000

def z329 : W := mkw 0x04516458b258d622 0x5011459162c96358 0xff71fc7cfe78ff3f 0xfffdc7f1f3f9e3fc

def z330 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff89ff83ff84fcff 0xfffe27fe0ffe13f3

def z331 : W := mkw 0x05780000246c0003 0x0015e0000091b000 0x9f780000fe7c003c 0x3e7de00003f9f000

def z332 : W := mkw 0x05796058b47cc623 0x5015e58162d1f318 0xdf79e07cfe7ce73e 0xff7de781f3f9f39c

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z334 : W := mkw 0x0000008000812940 0x24000002000204a5 0x809e0000018ffffc 0x3a02780000063fff

def z335 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6f7ffc7f00000002 0x25bdfff1fc000000

def z336 : W := mkw 0x0a80000049000004 0x002a000001240000 0x9f9e0000ff8f003c 0x3e7e780003fe3c00

def z337 : W := mkw 0x0450000020480002 0x0011400000812000 0x1c10000070080008 0x0870400001c02000

def z338 : W := mkw 0x000321859081e948 0x64000c86164207a5 0xdc9fe38ff18fffff 0xff727f8e3fc63fff

def z339 : W := mkw 0x0bac00006d6e0007 0x802eb00001b5b800 0x138e0000ffff003c 0x104e380003fffc00

def z340 : W := mkw 0x10012480ffeef807 0xe040049203ffbbe0 0x10000000fffff83c 0x0040000003ffffe0

def z341 : W := mkw 0x1a8096804b803804 0x206a025a012e00e0 0xa3801f800f80f81d 0xda8e007e003e03e0

def z342 : W := mkw 0x0bac00004d260005 0x802eb00001349800 0x839e00000f8f003c 0x3a0e7800003e3c00

def z343 : W := mkw 0x000000806def2947 0xa400000201b7bca5 0x10000000fffffffc 0x0040000003ffffff

def z344 : W := mkw 0x00030db78291bdd8 0x3c000c36de0a46f7 0xa09f1fff018fffff 0xfa827c7ffc063fff

def z345 : W := mkw 0x04512000b048c002 0x4011448002c12300 0xdc71e000f078e02c 0xef71c78003c1e380

def z346 : W := mkw 0x2002dbef00812978 0x24800b6fbc0204a5 0x6001ffff0000ffc3 0xc18007fffc0003ff

def z347 : W := mkw 0x0000001000100400 0x1000000040004010 0x0060007000700422 0x20018001c001c010

def z348 : W := mkw 0x1a81b280d980e804 0x606a06ca036603a0 0xdc81e380f180e00c 0xcf72078e03c60380

def z349 : W := mkw 0x0a80000049000004 0x002a000001240000 0x038000000f800010 0x100e0000003e0000

def z350 : W := mkw 0x257e496f00000038 0x0095f925bc000000 0x80fe03ff00000003 0xfa03f80ffc000000

def z351 : W := mkw 0x3ffdfeeadb80f834 0x60fff7fbab6e03e0 0xffe1fff0ff80f81d 0xdfff87ffc3fe03e0

def z352 : W := mkw 0x0ffc60487d6e4227 0xc03ff18121f5b908 0xdffee00cffff633c 0xbf7ffb8033fffd8c

def z353 : W := mkw 0x1a81beb2db90fc94 0x786a06facb6e43f2 0xff81fff3ff80fcdf 0xdffe07ffcffe03f3

def z354 : W := mkw 0x0002018500812948 0x24000806140204a5 0x009e038f018f1ff3 0x3002780e3c063c7f

def z355 : W := mkw 0x1a81b690fbd8fe06 0x706a06da43ef63f8 0xff81ff80fff8ff3d 0xdffe07fe03ffe3fc

def z356 : W := mkw 0x1a81b680ffeef807 0xe06a06da03ffbbe0 0xff81ff80fffff83d 0xdffe07fe03ffffe0

def z357 : W := mkw 0x257f4d7f863494b9 0x1895fd35fe18d252 0xa37f1c7f8e749cf7 0x768dfc71fe39d273

def z358 : W := mkw 0x0128082204240091 0x0804a02088109002 0x00080003000400c0 0x000020000c001003

def z359 : W := mkw 0x2ed7f35db058c62a 0x50bb5fcd76c16318 0xdcf7e3fcf078e72e 0xef73df8ff3c1e39c

def z360 : W := mkw 0x3fffffefffeef83f 0xe0ffffffbfffbbe0 0xfffffffffffff83f 0xffffffffffffffe0

def z361 : W := mkw 0x00012010b058c602 0x5000048042c16318 0x9010000cf078e72e 0xea40400033c1e39c

def z362 : W := mkw 0x00012410b67cd683 0x5800049042d9f35a 0x10000000fe7cfffc 0x0040000003f9f3ff

def z363 : W := mkw 0x1ed1b680fbc8f806 0x607b46da03ef23e0 0xfff1ff80fff8f83d 0xffffc7fe03ffe3e0

def z364 : W := mkw 0x2ffedb6f246e003b 0x80bffb6dbc91b800 0xefffffff007f0023 0xffbffffffc01fc00

def z365 : W := mkw 0x000104808280b800 0x20000412020a02e0 0xa3811f808f80f81d 0xde8e047e023e03e0

def z366 : W := mkw 0x0450405820580622 0x1011410160816018 0x8070007c0078e72e 0xea01c001f001e39c

def z367 : W := mkw 0x2fffdb7f80108438 0x10bfff6dfe004210 0xefffffff80708427 0xffbffffffe01c210

def z368 : W := mkw 0x057c0000246e0003 0x8015f0000091b800 0x837e00008e7f0034 0x360df8000239fc00

def z369 : W := mkw 0x2ffe9b276d6e001f 0x80bffa6c9db5b800 0xbffe1f83ffff003d 0x3efff87e0ffffc00

def z370 : W := mkw 0x0ffc0000694a0006 0x803ff00001a52800 0x9ffe0000718b0008 0x3e7ff80001c62c00

def z371 : W := mkw 0x20029b2700000018 0x00800a6c9c000000 0x20001f8300000001 0x0080007e0c000000

def z372 : W := mkw 0x0ffc000049000004 0x003ff00001240000 0x9ffe0000ff80001c 0x3e7ff80003fe0000

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x801000000008002c 0x2a00400000002000

def z374 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f01ff80fe00f801 0xc5fc07fe03f803e0

def z375 : W := mkw 0x2baf9f3786349499 0x18aebe7cde18d252 0xa3ef1ff38e749cf7 0x768fbc7fce39d273

def z376 : W := mkw 0x3003ffef9280f838 0x60c00fffbe4a03e0 0x6001ffff0000f803 0xc18007fffc0003e0

def z377 : W := mkw 0x0450405820580622 0x1011410160816018 0xcc71e07c00780722 0xef31c781f001e01c

def z378 : W := mkw 0x0001001080108400 0x1000040042004210 0x8069007380749cf7 0x7601a401ce01d273

def z379 : W := mkw 0x012b0db786b5bdd9 0x3c04ac36de1ad6f7 0xa3ef1ff38ff79cf7 0x768fbc7fce3fde73

def z380 : W := mkw 0x0002018500812948 0x24000806140204a5 0x809e0383018f18fd 0x3a02780e0c063c63

def z381 : W := mkw 0x3ffedfef4b80383c 0x20fffb7fbd2e00e0 0xefffffff0f801813 0xffbffffffc3e0060

def z382 : W := mkw 0x0000008000812940 0x24000002000204a5 0x80800380018ffffd 0xda02000e00063fff

def z383 : W := mkw 0x0fff61ddfdffef6f 0xf43ffd8777f7ffbd 0xdfffe3ffffffffff 0xff7fff8fffffffff

def z384 : W := mkw 0x04516c7ab258d6b2 0x581145b1eac9635a 0xfc71fc7ff078ffef 0xeff1c7f1ffc1e3ff

def z385 : W := mkw 0x0450604830484222 0x4011418120c12108 0xdc70e00cf078632c 0xaf71c38033c1e18c

def z386 : W := mkw 0x1a80b28059806804 0x606a02ca016601a0 0xff81ff8071806009 0xdffe07fe01c60180

def z387 : W := mkw 0x10012480db80f804 0x60400492036e03e0 0xb3011c00ff80f81d 0x56cc047003fe03e0

def z388 : W := mkw 0x0001041082109400 0x1000041042084250 0xa3611c708e709c37 0x768d8471c239c270

def z389 : W := mkw 0x145164d8fbd8fe26 0x7051459363ef63f8 0xdc71e07cfff8ff3e 0xef71c781f3ffe3fc

def z390 : W := mkw 0x2ffdfa7ab058c632 0x50bff7e9eac16318 0x7f61fc70f0700000 0x05fd87f1c3c1c000

def z391 : W := mkw 0x000120809080e800 0x60000482024203a0 0xdc81e380f180f81d 0xdf72078e03c603e0

def z392 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1f9e00007f8f0018 0x187e780001fe3c00

def z393 : W := mkw 0x000124009200d000 0x4000049002480340 0xff01fc00fe00f81d 0xdffc07f003f803e0

def z394 : W := mkw 0x2fffdf7f821094b8 0x18bfff7dfe084252 0xefffffff00009cc3 0xffbffffffc000273

def z395 : W := mkw 0x257e497f043404b9 0x1895f925fc10d012 0x007e007f007404e2 0x2001f801fc01d013

def z396 : W := mkw 0x2fffdf6f82009038 0x00bfff7dbe080240 0xefffffff8e009817 0xffbffffffe380260

def z397 : W := mkw 0x0000001004340481 0x180000004010d012 0x00000000007404e0 0x000000000001d013

def z398 : W := mkw 0x0ffc000000000000 0x003ff00000000000 0x0f60000000000000 0x043d800000000000

def z399 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0xff01fc00fe009815 0x57fc07f003f80260

def z400 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0xff81fc00ff80001c 0x1ffe07f003fe0000

def z401 : W := mkw 0x257e496f00010178 0x0495f925bc000405 0x007e007f000f07e2 0x2001f801fc003c1f

def z402 : W := mkw 0x0a81960082009000 0x002a065802080240 0xef81ff808e009815 0xdfbe07fe02380260

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000000008426 0x6200000000000210

def z404 : W := mkw 0x2ffffbffb0d9ef7a 0x74bfffeffec367bd 0xfffffffff1ffffff 0xffffffffffc7ffff

def z405 : W := mkw 0x0128000004240001 0x0004a00000109000 0x836800038e749cf7 0x760da0000e39d273

def z406 : W := mkw 0x0453615db058c62a 0x50114d8576c16318 0xdcffe3fff078e72f 0xff73ff8fffc1e39c

def z407 : W := mkw 0x2ffedb7f043404b9 0x18bffb6dfc10d012 0xefffffff007404e3 0xffbffffffc01d013

def z408 : W := mkw 0x1001b680db80f804 0x604006da036e03e0 0x7001ff80ff80f81d 0xc1c007fe03fe03e0

def z409 : W := mkw 0x0129041086349481 0x1804a4104218d252 0x836800008e749cf4 0x360da0000239d273

def z410 : W := mkw 0x0002018500812948 0x24000806140204a5 0x0096038f018bffcb 0xc802580e3c062fff

def z411 : W := mkw 0x00012090b0d9ef42 0x7400048242c367bd 0x10000000f1fffffc 0x0040000003c7ffff

def z412 : W := mkw 0x0ffc082200000010 0x003ff02088000000 0xafff1c7300000003 0x7ebffc71cc000000

def z413 : W := mkw 0x0450605830584622 0x5011418160c16118 0x5c70e07c7078672a 0xa971c381f1c1e19c

def z414 : W := mkw 0x00012010fd7ec607 0xd000048043f5fb18 0x10000000ffffe73c 0x0040000003ffff9c

def z415 : W := mkw 0x2ed6f34d3048422a 0x40bb5bcd34c12108 0x5c96e38c70086308 0x89725b8e31c0218c

def z416 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9f680000fe740034 0x367da00003f9d000

def z417 : W := mkw 0x1ed1f658fb58d626 0x507b47d963ed6358 0xff71fc7cfe78e72e 0xeffdc7f1f3f9e39c

def z418 : W := mkw 0x0001040082009000 0x0000041002080240 0x000000008e009814 0x0000000002380260

def z419 : W := mkw 0x0578486a00000030 0x0015e121a8000000 0xef79fc7f00000003 0xffbde7f1fc000000

def z420 : W := mkw 0x04540000204a0002 0x8011500000812800 0x00160000000b0000 0x0000580000002c00

def z421 : W := mkw 0x01292c32b67cd693 0x5804a4b0cad9f35a 0xb3691c73fe7cffff 0x76cda471cff9f3ff

def z422 : W := mkw 0x212bdf7f863494b9 0x1884af7dfe18d252 0xe369ffff8e749cf7 0xf78da7fffe39d273

def z423 : W := mkw 0x00000000694a0006 0x8000000001a52800 0x10000000718b0008 0x0040000001c62c00

def z424 : W := mkw 0x00032195b0d9ef4a 0x74000c8656c367bd 0x909e038ff1ffffff 0xfa42780e3fc7ffff

def z425 : W := mkw 0x2bae9b274d26001d 0x80aeba6c9d349800 0x238e1f830f870011 0x108e387e0c3e1c00

def z426 : W := mkw 0x045261cd30c96b6a 0x6411498734c325ad 0x5c96e38c718b6308 0x89725b8e31c62d8c

def z427 : W := mkw 0x100124809280f800 0x60400492024a03e0 0x000000000000f800 0x00000000000003e0

def z428 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f81ff80ff806008 0x8dfe07fe03fe0180

def z429 : W := mkw 0x0128082200000010 0x0004a02088000000 0x23611c7000000000 0x048d8471c0000000

def z430 : W := mkw 0x0002010500010148 0x0400080414000405 0x000e0003000700c0 0x000038000c001c03

def z431 : W := mkw 0x05790c32a67c9493 0x1815e430ca99f252 0xbf791c73fe7c9cff 0x7efde471cff9f273

def z432 : W := mkw 0x0129083280108410 0x1004a420ca004210 0xa3691c7380708427 0x768da471ce01c210

def z433 : W := mkw 0x257e497f2058063a 0x1095f925fc816018 0x007e007f00780722 0x2001f801fc01e01c

def z434 : W := mkw 0x2ed6d34d694a002e 0x80bb5b4d35a52800 0x5c96e38c718b0008 0x89725b8e31c62c00

def z435 : W := mkw 0x0002018500812948 0x24000806140204a5 0x0086038001830000 0x0002180e00060c00

def z436 : W := mkw 0x2bae9f2706241099 0x08aeba7c9c189042 0x238e1f830e0418d1 0x108e387e0c381063

def z437 : W := mkw 0x000120109010c600 0x5000048042404318 0x000000000000e700 0x000000000000039c

def z438 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0xff81ff80fe000001 0xdffe07fe03f80000

def z439 : W := mkw 0x0ffc00004d260005 0x803ff00001349800 0x8ffe00000f870010 0x3e3ff800003e1c00

def z440 : W := mkw 0x0128083204340491 0x1804a020c810d012 0x0060007000700000 0x00018001c001c000

def z441 : W := mkw 0x01280c2206241091 0x0804a03088189042 0xa3691c730e0418d3 0x768da471cc381063

def z442 : W := mkw 0x0002018500812948 0x24000806140204a5 0x009e038f018f7bd9 0x9802780e3c063def

def z443 : W := mkw 0x2ffedb7f2058063a 0x10bffb6dfc816018 0xefffffff00780723 0xffbffffffc01e01c

def z444 : W := mkw 0x0a8000006d6e0007 0x802a000001b5b800 0x9f800000ffff003c 0x1e7e000003fffc00

def z445 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0xeffffc7000000000 0x3fbffff1c0000000

def z446 : W := mkw 0x000160589010c620 0x5000058162404318 0xc011e07c0008e72e 0xeb004781f000239c

def z447 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e07cf0700002 0xef71c781f3c1c000

def z448 : W := mkw 0x0002018500812948 0x24000806140204a5 0x009e038f018f67ea 0xa802780e3c063d9f

def z449 : W := mkw 0x0450604830484222 0x4011418120c12108 0xdc71e07c7008630a 0xef71c781f1c0218c

def z450 : W := mkw 0x0001049086b5bdc1 0x3c000412421ad6f7 0x000000008ffffffc 0x00000000023fffff

def z451 : W := mkw 0x0a80008049802804 0x202a0002012600a0 0x9f800380ff80f81d 0xde7e000e03fe03e0

def z452 : W := mkw 0x0450404820480222 0x0011410120812008 0x0010000c00080300 0x000040003000200c

def z453 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x33801f80ff80f81d 0x10ce007e03fe03e0

def z454 : W := mkw 0x0ed40000694a0006 0x803b500001a52800 0x1c00000070000000 0x0070000001c00000

def z455 : W := mkw 0x1ed1f6d8fbd8fe26 0x707b47db63ef63f8 0xffe1fff0fff0f81d 0xdfff87ffc3ffc3e0

def z456 : W := mkw 0x1fffb785ffeff94f 0xe47ffede17ffbfe5 0xffffff8fffffffff 0xfffffffe3fffffff

def z457 : W := mkw 0x0128082200000010 0x0004a02088000000 0x0068007300000002 0x2001a001cc000000

def z458 : W := mkw 0x0129001084348401 0x1004a4004210d210 0x836900708e748436 0x760da401c239d210

def z459 : W := mkw 0x057d6058b47ec623 0xd015f58162d1fb18 0xdc7fe07cf07fe72e 0xef71ff81f3c1ff9c

def z460 : W := mkw 0x3bae9fa74b80381c 0x20eeba7e9d2e00e0 0x238e1f830f801811 0x108e387e0c3e0060

def z461 : W := mkw 0x2000da6a00000030 0x00800369a8000000 0x6001fc7000000000 0x018007f1c0000000

def z462 : W := mkw 0x0002010500000008 0x0000080414000000 0x001e000f00000002 0x200078003c000000

def z463 : W := mkw 0x0ffd0410ef7e9487 0x983ff41043bdfa52 0x9ffe0000ffff9cfc 0x3e7ff80003fffe73

def z464 : W := mkw 0x00000c2202001090 0x0800003088080042 0x20001c03000018c1 0x008000700c000063

def z465 : W := mkw 0x0002018500812948 0x24000806140204a5 0x008e038f0187ffd3 0xd002380e3c061fff

def z466 : W := mkw 0x0450000020480002 0x0011400000812000 0x9cfe0000f1ff003c 0x3e73f80003c7fc00

def z467 : W := mkw 0x0450405820580622 0x1011410160816018 0x0060007000700000 0x00018001c001c000

def z468 : W := mkw 0x057c0000246e0003 0x8015f0000091b800 0x0060000000700000 0x000180000001c000

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0xa3011c0000000001 0x568c047000000000

def z470 : W := mkw 0x1451f6d8b2d8fe22 0x705147db62cb63f8 0xfc71fffcf078ff2f 0xeff1c7fff3c1e3fc

def z471 : W := mkw 0x1001b6809280f800 0x604006da024a03e0 0xe301ff808e00f815 0xd78c07fe023803e0

def z472 : W := mkw 0x0a84000049020004 0x802a100001240800 0x0086000001830000 0x0002180000060c00

def z473 : W := mkw 0x2ffed34d6d6e002f 0x80bffb4d35b5b800 0xdffee38cffff003c 0xbf7ffb8e33fffc00

def z474 : W := mkw 0x00012010b058c602 0x5000048042c16318 0xdc01e000f078e72c 0xcf70078003c1e39c

def z475 : W := mkw 0x2bac9a2200000010 0x00aeb26888000000 0x23001c0000000000 0x008c007000000000

def z476 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c61e07cf070e702 0xc5718781f3c1c39c

def z477 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9fe00000fff0001c 0x1e7f800003ffc000

def z478 : W := mkw 0x1a80928049802804 0x206a024a012600a0 0x0080038001800000 0x0002000e00060000

def z479 : W := mkw 0x2002d34d00000028 0x00800b4d34000000 0x4000e38c00000000 0x8100038e30000000

def z480 : W := mkw 0x0ba89a2200000010 0x002ea26888000000 0xefe9fff300000003 0xffbfa7ffcc000000

def z481 : W := mkw 0x1a83b785db81f94c 0x646a0ede176e07e5 0xff81ff8fff80ffdf 0xdffe07fe3ffe03ff

def z482 : W := mkw 0x2ed6d3cd00812968 0x24bb5b4f340204a5 0x4c96e38c018b6308 0x89325b8e30062d8c

def z483 : W := mkw 0x0ba90c32cf349495 0x182ea430cb3cd252 0xbfe91c73fff49cff 0x7effa471cfffd273

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000000000e00c 0xca00000000000380

def z485 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c708e740034 0x368da471c239d000

def z486 : W := mkw 0x0002018500812948 0x24000806140204a5 0x808e03830187f8dd 0xda02380e0c061fe3

def z487 : W := mkw 0x0ffc000020480002 0x003ff00000812000 0x9ffe0000f078002c 0x3e7ff80003c1e000

def z488 : W := mkw 0x0128083204340491 0x1804a020c810d012 0x836800738e7404f6 0x360da001ce39d013

def z489 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23691c738e7404e2 0x248da471ce39d013

def z490 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc79e07ff07cffff 0xff71e781ffc1f3ff

def z491 : W := mkw 0x01280c3206341491 0x1804a030c818d052 0x23681c730e741cf3 0x308da071cc39d073

def z492 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x23fe1fff00000003 0x308ff87ffc000000

def z493 : W := mkw 0x1babbfb7dfb5fddd 0x7c6eaefedf7ed7f7 0xffffffffffffffff 0xffffffffffffffff

def z494 : W := mkw 0x1a83b785db81f94c 0x646a0ede176e07e5 0xff8fff83ff87f8dd 0xdffe3ffe0ffe1fe3

def z495 : W := mkw 0x2ffedbef00812978 0x24bffb6fbc0204a5 0xefffffff0000ffc3 0xffbffffffc0003ff

def z496 : W := mkw 0x01290cb286b5bdd1 0x3c04a432ca1ad6f7 0xa3691c738fffffff 0x768da471ce3fffff

def z497 : W := mkw 0x2ffedbef00812978 0x24bffb6fbc0204a5 0xefffffff018718d3 0xffbffffffc061c63

def z498 : W := mkw 0x01280c2206241091 0x0804a03088189042 0xa3081c030e049cf7 0x728c20700c381273

def z499 : W := mkw 0x10012400db00d004 0x40400490036c0340 0x10000000fe000000 0x0040000003f80000

def z500 : W := mkw 0x1ffdbeb2fffefc97 0xf87ff6facbfffbf2 0xfffffff3fffffcff 0xffffffffcffffff3

def z501 : W := mkw 0x1a8096804b803804 0x206a025a012e00e0 0xef81ff800f801811 0xdfbe07fe003e0060

def z502 : W := mkw 0x00010c3282109490 0x18000430ca084252 0x20011c7000000000 0x00800471c0000000

def z503 : W := mkw 0x0ffc000000000000 0x003ff00000000000 0x8ffe0000018f003c 0x3e3ff80000063c00

def z504 : W := mkw 0x0000001020580602 0x1000000040816018 0x0000000000780720 0x000000000001e01c

def z505 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9f700000fe78002c 0x2e7dc00003f9e000

def z506 : W := mkw 0x2ed6d34d00000028 0x00bb5b4d34000000 0xef97ff8c00000001 0xdfbe5ffe30000000

def z507 : W := mkw 0x11292cb2dfb4fc95 0x7844a4b2cb7ed3f2 0xb3691c73fff4fcff 0x76cda471cfffd3f3

def z508 : W := mkw 0x0a8201854981294c 0x242a0806152604a5 0x9f9e038fff8fffff 0xfe7e780e3ffe3fff

def z509 : W := mkw 0x0450404800000020 0x0011410120000000 0xcc71e07c0008e72e 0xef31c781f000239c

def z510 : W := mkw 0x0451405880108420 0x1011450162004210 0xcc71e07c80708426 0xef31c781f201c210

def z511 : W := mkw 0x1a80b28059806804 0x606a02ca016601a0 0xdf80e380ff80601c 0x9f7e038e03fe0180

def z512 : W := mkw 0x0450000020480002 0x0011400000812000 0x1c600000f0700000 0x0471800003c1c000

def z513 : W := mkw 0x0ed46048794a4226 0xc03b518121e52908 0x5c96e00c718b6308 0x89725b8031c62d8c

def z514 : W := mkw 0x057c4058247e0623 0x9015f1016091f818 0x007e007c007f0722 0x2001f801f001fc1c

def z515 : W := mkw 0x0bae01854da7294d 0xa42eb80615369ca5 0x839e038f0f8fffff 0xfa0e780e3c3e3fff

def z516 : W := mkw 0x0002018500802808 0x20000806140200a0 0x809e038f0180f81f 0xfa02780e3c0603e0

def z517 : W := mkw 0x00016c7a9210d6b0 0x580005b1ea48435a 0x6001fc7f0000ffc3 0xc18007f1fc0003ff

def z518 : W := mkw 0x2ed6d3cd00812968 0x24bb5b4f340204a5 0xcc9ee38f018fffff 0xfb327b8e3c063fff

def z519 : W := mkw 0x0bad0c32cf369495 0x982eb430cb3cda52 0xa3ef1c738ff79cf7 0x768fbc71ce3fde73

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010000c00080722 0x200040003000201c

def z521 : W := mkw 0x0ffd0c32ef7e9497 0x983ff430cbbdfa52 0xbf691c73fe749cf7 0x76fda471cff9d273

def z522 : W := mkw 0x00010c3282109490 0x18000430ca084252 0xa3011c738e009cd7 0x568c0471ce380273

def z523 : W := mkw 0x2ffedbef00812978 0x24bffb6fbc0204a5 0xefffffff018b630b 0xffbffffffc062d8c

def z524 : W := mkw 0x0002010500000008 0x0000080414000000 0x809e038f00049cf7 0xfa02780e3c001273

def z525 : W := mkw 0x2ffe9b2700000018 0x00bffa6c9c000000 0xaffe1f8300000001 0x3ebff87e0c000000

def z526 : W := mkw 0x0ffd0c3286349491 0x183ff430ca18d252 0xafff1c738e749cf7 0x7ebffc71ce39d273

def z527 : W := mkw 0x057e0105246f014b 0x8415f8041491bc05 0x007e000f007f07e2 0x2001f8003c01fc1f

def z528 : W := mkw 0x0ffd6c7aff7ed6b7 0xd83ff5b1ebfdfb5a 0xfffffc7fffffffff 0xfffffff1ffffffff

def z529 : W := mkw 0x2fffdf7f863494b9 0x18bfff7dfe18d252 0xefffffff8e700003 0xffbffffffe39c000

def z530 : W := mkw 0x00012010b058c602 0x5000048042c16318 0x90610070f078e72e 0x66418401c3c1e39c

def z531 : W := mkw 0x0a80928000802800 0x202a024a000200a0 0xef81ff800180f81d 0xdfbe07fe000603e0

def z532 : W := mkw 0x1000968002803800 0x2040025a000a00e0 0x20001f8000001801 0x0080007e00000060

def z533 : W := mkw 0x057c000000000000 0x0015f00000000000 0x007e000000000000 0x2001f80000000000

def z534 : W := mkw 0x0ffc000004240001 0x003ff00000109000 0x8ffe00008e740034 0x3e3ff8000239d000

def z535 : W := mkw 0x045241dd20d92f6a 0x34114907748364bd 0x80fe03ff01ffffff 0xfa03f80ffc07ffff

def z536 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x4071e07c0078e722 0xe101c781f001e39c

def z537 : W := mkw 0x0ffc0000246e0003 0x803ff0000091b800 0x8ffe0000007f0020 0x3e3ff8000001fc00

def z538 : W := mkw 0x0002010500000008 0x0000080414000000 0x008e038300000001 0x1002380e0c000000

def z539 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc61e070f0708426 0x67718781c3c1c210

def z540 : W := mkw 0x0ffe01856def294f 0xa43ff80615b7bca5 0x9ffe038cffff633c 0xbe7ff80e33fffd8c

def z541 : W := mkw 0x0000000049000004 0x0000000001240000 0x10000000ff80001c 0x0040000003fe0000

def z542 : W := mkw 0x0ffe01056d6e000f 0x803ff80415b5b800 0x9ffe038fffff003f 0xfe7ff80e3ffffc00

def z543 : W := mkw 0x00010410ef7e9487 0x9800041043bdfa52 0x10000000ffff9cfc 0x0040000003fffe73

def z544 : W := mkw 0x057c00006d6e0007 0x8015f00001b5b800 0x107e0000ffff003c 0x2041f80003fffc00

def z545 : W := mkw 0x2fffdf7fef7e94bf 0x98bfff7dffbdfa52 0xffffffffffff9cff 0xfffffffffffffe73

def z546 : W := mkw 0x0a81b2009000c000 0x402a06c802400300 0xff81ff80f000e00d 0xdffe07fe03c00380

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x8008000300000003 0x720020000c000000

def z548 : W := mkw 0x0ed40000694a0006 0x803b500001a52800 0x9c9e0000718f003c 0x3a72780001c63c00

def z549 : W := mkw 0x012a0da706a539d9 0x2c04a8369c1a94e7 0xa39e1f8f0f8fffff 0xfa8e787e3c3e3fff

def z550 : W := mkw 0x0ba800004d240005 0x002ea00001349000 0x9fe80000fff4003c 0x3e7fa00003ffd000

def z551 : W := mkw 0x1ffdb600ff6ed007 0xc07ff6d803fdbb40 0xfffffc00ffff003c 0x3ffffff003fffc00

def z552 : W := mkw 0x0ffd0c32ef7e9497 0x983ff430cbbdfa52 0xbfff1c70ffff003c 0x3efffc71c3fffc00

def z553 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x006800738e749cf6 0x2001a001ce39d273

def z554 : W := mkw 0x10032585db81f94c 0x64400c96176e07e5 0x909e038fff8fffff 0xfa42780e3ffe3fff

def z555 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000000009815 0x5200000000000260

def z556 : W := mkw 0x0000000000000000 0x0000000000000000 0x8010000c00000002 0xea00400030000000

def z557 : W := mkw 0x0001001080108400 0x1000040042004210 0x0001007000008402 0x40000401c0000210

def z558 : W := mkw 0x0000040006241081 0x0800001000189042 0x000000000e0418d0 0x0000000000381063

def z559 : W := mkw 0x045361ddb0d9ef6a 0x74114d8776c367bd 0xdc71e3fff078ffef 0xef71c78fffc1e3ff

def z560 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1f600000ffff003c 0x047d800003fffc00

def z561 : W := mkw 0x212adb6f00000038 0x0084ab6dbc000000 0xe369ffff00000003 0xf78da7fffc000000

def z562 : W := mkw 0x000120009000c000 0x4000048002400300 0x4001e0000000e000 0xc100078000000380

def z563 : W := mkw 0x0002018500812948 0x24000806140204a5 0x809e038f018718d3 0xfa02780e3c061c63

def z564 : W := mkw 0x0129040086249001 0x0004a41002189240 0xa3691c008e749835 0x768da4700239d260

def z565 : W := mkw 0x057c0000246e0003 0x8015f0000091b800 0x80fe000001ff003c 0x3a03f8000007fc00

def z566 : W := mkw 0x0001041082109480 0x1800041042084252 0x0000000000009cc0 0x0000000000000273

def z567 : W := mkw 0x0001001080108400 0x1000040042004210 0x0061007080700000 0x04018401c201c000

def z568 : W := mkw 0x0002018500812948 0x24000806140204a5 0x8010038f0008ffef 0xea00400e3c0023ff

def z569 : W := mkw 0x045160489000c020 0x4011458122400300 0xdc71e07cf000e00e 0xef71c781f3c00380

def z570 : W := mkw 0x0128083204340491 0x1804a020c810d012 0xa3691c73007404e3 0x768da471cc01d013

def z571 : W := mkw 0x257e49ef00812978 0x2495f927bc0204a5 0x80fe03ff018fffff 0xfa03f80ffc063fff

def z572 : W := mkw 0x0ed4000000000000 0x003b500000000000 0x0c96000000000000 0x0832580000000000

def z573 : W := mkw 0x05794c7aa67c96b3 0x1815e531ea99f25a 0xa3791c7f8e7c9ff7 0x768de471fe39f27f

def z574 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0000fe700000 0x3e7ff80003f9c000

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x8018000f000cffff 0xfa0060003c0033ff

def z576 : W := mkw 0x1ba9be32df34d495 0x586ea6f8cb7cd352 0x7f61fc70fe700000 0x05fd87f1c3f9c000

def z577 : W := mkw 0x0450000020480002 0x0011400000812000 0x0070000000780020 0x2001c0000001e000

def z578 : W := mkw 0x00016058b058c622 0x5000058162c16318 0x5001e07cf078e72e 0xc1400781f3c1e39c

def z579 : W := mkw 0x0000008000802800 0x20000002000200a0 0x8090038c0188ff3f 0xfa02400e300623fc

def z580 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f01fc00ff80f81c 0x05fc07f003fe03e0

def z581 : W := mkw 0x04516058fd7ec627 0xd011458163f5fb18 0xdc71e07cffffe73e 0xef71c781f3ffff9c

def z582 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0xef71fc7c00000002 0xefbdc7f1f0000000

def z583 : W := mkw 0x0ffd6058fd7ec627 0xd03ff58163f5fb18 0xdf71e07cfe78e72e 0xef7dc781f3f9e39c

def z584 : W := mkw 0x1129beb296b4fc91 0x7844a6faca5ad3f2 0xe369fff38e74fcf7 0xf78da7ffce39d3f3

def z585 : W := mkw 0x0450000020480002 0x0011400000812000 0x9c70000cf078e72e 0xee71c00033c1e39c

def z586 : W := mkw 0x2453fb7fb058c63a 0x50914fedfec16318 0xfc71fffff078e72f 0xeff1c7ffffc1e39c

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x809e000c018fe73e 0xfa02780030063f9c

def z588 : W := mkw 0x01290cb286b4bc91 0x3804a432ca1ad2f2 0xa3e91ff38ff4fcff 0xfe8fa47fce3fd3f3

def z589 : W := mkw 0x0bac00004d260005 0x802eb00001349800 0x83ee00008ff70034 0x360fb800023fdc00

def z590 : W := mkw 0x0a80000049000004 0x002a000001240000 0x1c80000071800008 0x0872000001c60000

def z591 : W := mkw 0x0001041086349481 0x180004104218d252 0xa3011c008e749cf5 0x568c04700239d273

def z592 : W := mkw 0x05796c7ab67cd6b3 0x5815e5b1ead9f35a 0xff69fc73fe749cf7 0x77fda7f1cff9d273

def z593 : W := mkw 0x01280c2206241091 0x0804a03088189042 0xa3681c038e7418f5 0x368da0700e39d063

def z594 : W := mkw 0x0a82938500812948 0x242a0a4e140204a5 0xef9fff8f018fffff 0xffbe7ffe3c063fff

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x8008000000040034 0x3200200000001000

def z596 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010000c00086308 0x880040003000218c

def z597 : W := mkw 0x2ffefb6f3048423a 0x40bffbedbcc12108 0xffffffff7008630b 0xfffffffffdc0218c

def z598 : W := mkw 0x1ffd2480ffeef807 0xe07ff49203ffbbe0 0x9ffe0000fffff83c 0x3e7ff80003ffffe0

def z599 : W := mkw 0x0450404800000020 0x0011410120000000 0x4c61e07000000000 0x05318781c0000000

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x809e000000000000 0x3a02780000000000

def z601 : W := mkw 0x0ffd0010ed7e8407 0x903ff40043b5fa10 0x9fff0070ffff843e 0x7e7ffc01c3fffe10

def z602 : W := mkw 0x2ed4d24800000020 0x00bb534920000000 0x4c00e00000000000 0x0130038000000000

def z603 : W := mkw 0x0000008000812940 0x24000002000204a5 0x00000000018718d0 0x0000000000061c63

def z604 : W := mkw 0x0ffd0400ef6e9007 0x803ff41003bdba40 0xbfff1c00ffff983d 0x7efffc7003fffe60

def z605 : W := mkw 0x2ffffb7f9010c638 0x50bfffedfe404318 0xefffffff0000e703 0xffbffffffc00039c

def z606 : W := mkw 0x1001b6009200d000 0x404006d802480340 0x6001fc0000000000 0x018007f000000000

def z607 : W := mkw 0x1001b6809280f800 0x604006da024a03e0 0xe081ff800180f81d 0xdb8207fe000603e0

def z608 : W := mkw 0x0128082200000010 0x0004a02088000000 0x23081c0300000001 0x108c20700c000000

def z609 : W := mkw 0x000120009000c000 0x4000048002400300 0x10000000f000e00c 0x0040000003c00380

def z610 : W := mkw 0x000000006d6e0007 0x8000000001b5b800 0x10000000fe700000 0x0040000003f9c000

def z611 : W := mkw 0x1a8297854b81394c 0x246a0a5e152e04e5 0x238e1f830f8718d1 0x108e387e0c3e1c63

def z612 : W := mkw 0x0ffd2010fd7ec607 0xd03ff48043f5fb18 0x9ffe0000ffffe73c 0x3e7ff80003ffff9c

def z613 : W := mkw 0x0ed16058f958c626 0x503b458163e56318 0xdff1e07cfff8e73e 0xff7fc781f3ffe39c

def z614 : W := mkw 0x1ed1f6c8fbc8fa26 0x607b47db23ef23e8 0xff91ff8cff88fb1d 0xdffe47fe33fe23ec

def z615 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x4cfee3ff00000002 0xa933fb8ffc000000

def z616 : W := mkw 0x000361dd9091ef68 0x74000d87764247bd 0xc09fe3ff018fffff 0xfb027f8ffc063fff

def z617 : W := mkw 0x057c0000246e0003 0x8015f0000091b800 0x9c7e0000f07f002c 0x2e71f80003c1fc00

def z618 : W := mkw 0x0a80920000000000 0x002a024800000000 0x23801f8000000001 0x108e007e00000000

def z619 : W := mkw 0x1ba9be32df34d495 0x586ea6f8cb7cd352 0xff69fc73fe749cf7 0x77fda7f1cff9d273

def z620 : W := mkw 0x045160589010c620 0x5011458162404318 0xcc71e07c0000e702 0xef31c781f000039c

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000c0000e702 0xc00000003000039c

def z622 : W := mkw 0x0001000080008000 0x0000040002000200 0x8001000080008004 0x4600040002000200

def z623 : W := mkw 0x2ffed34d00000028 0x00bffb4d34000000 0xcffee38c00000000 0xbf3ffb8e30000000

def z624 : W := mkw 0x0ffe010500000008 0x003ff80414000000 0x8ffe038f00000003 0xfe3ff80e3c000000

def z625 : W := mkw 0x0ffd6058b058c622 0x503ff58162c16318 0xdfffe07cf078e72e 0xff7fff81f3c1e39c

def z626 : W := mkw 0x1a81b6809280f800 0x606a06da024a03e0 0xef81ff800000f801 0xdfbe07fe000003e0

def z627 : W := mkw 0x2bae9b2700000018 0x00aeba6c9c000000 0xef8fff8300000001 0xdfbe3ffe0c000000

def z628 : W := mkw 0x2003fb7f9010c638 0x50800fedfe404318 0x6001ffff0000e703 0xc18007fffc00039c

def z629 : W := mkw 0x045361ddb0d9ef6a 0x74114d8776c367bd 0xdcf7e3fcf1fbe72e 0xef73df8ff3c7ef9c

def z630 : W := mkw 0x0128000004240001 0x0004a00000109000 0x030800000e040010 0x100c200000381000

def z631 : W := mkw 0x0128082200000010 0x0004a02088000000 0xa3691c7300049cf7 0x768da471cc001273

def z632 : W := mkw 0x0000604810004220 0x4000018120400108 0x4000e00c00006300 0x810003803000018c

def z633 : W := mkw 0x04516458b67cd6a3 0x5811459162d9f35a 0xdc71e07cfe7cfffe 0xef71c781f3f9f3ff

def z634 : W := mkw 0x012a092700000018 0x0004a8249c000000 0xa3ff1fff00000003 0xfe8ffc7ffc000000

def z635 : W := mkw 0x1000208059806804 0x60400082016601a0 0x1000000071806008 0x0040000001c60180

def z636 : W := mkw 0x0129083284348491 0x1804a420ca10d212 0x80690073807484e6 0x6601a401ce01d213

def z637 : W := mkw 0x012a0da706a539d9 0x2c04a8369c1a94e7 0x238e1f830f8718d1 0x108e387e0c3e1c63

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0x8080038000000001 0xda02000e00000000

def z639 : W := mkw 0x0128083204340491 0x1804a020c810d012 0x8068007300749cf7 0x7201a001cc01d273

def z640 : W := mkw 0x1ed0f2c879c86a26 0x607b43cb21e721a8 0x5c90e38c71886308 0x8972438e31c6218c

def z641 : W := mkw 0x000201856def294f 0xa400080615b7bca5 0x909e038fffffffff 0xfa42780e3fffffff

def z642 : W := mkw 0x0ffd0c32ef7e9497 0x983ff430cbbdfa52 0x3f611c70fe700000 0x04fd8471c3f9c000

def z643 : W := mkw 0x0000008000802800 0x20000002000200a0 0x000003800000f801 0xc000000e000003e0

def z644 : W := mkw 0x1a80b20059004004 0x406a02c801640100 0x5c00e00070000000 0x0170038001c00000

def z645 : W := mkw 0x000120009000c000 0x4000048002400300 0xdc11e00cf008e72e 0xef70478033c0239c

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x809e0003018f9cff 0x7a0278000c063e73

def z647 : W := mkw 0x1ed3f7ddfbd9ff6e 0x747b4fdf77ef67fd 0xffffffffffffffff 0xffffffffffffffff

def z648 : W := mkw 0x10012480db81f944 0x64400492036e07e5 0x10000000ff8ffffc 0x0040000003fe3fff

def z649 : W := mkw 0x257c486a00000030 0x0095f121a8000000 0x0060007000000000 0x00018001c0000000

def z650 : W := mkw 0x01290c2286249091 0x0804a4308a189242 0xa3091c038e0498d5 0x568c24700e381263

def z651 : W := mkw 0x10012480db80f804 0x60400492036e03e0 0x90800380ff80f81d 0xda42000e03fe03e0

def z652 : W := mkw 0x05796c7ab67cd6b3 0x5815e5b1ead9f35a 0x7f61fc70fe700000 0x05fd87f1c3f9c000

def z653 : W := mkw 0x1ba89ea24fa43895 0x286ea27a893e90e2 0x23881f830f8418d1 0x108e207e0c3e1063

def z654 : W := mkw 0x0002010500010148 0x0400080414000405 0x801e000f000f9ff7 0x720078003c003e7f

def z655 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e070f078002c 0x2f71c781c3c1e000

def z656 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1f7e0000fe7f0020 0x247df80003f9fc00

def z657 : W := mkw 0x000361dd9091ef68 0x74000d87764247bd 0x4001e3ff0000ffc3 0xc100078ffc0003ff

def z658 : W := mkw 0x0ffe01856def294f 0xa43ff80615b7bca5 0x9ffe0383ffff18fd 0x3e7ff80e0ffffc63

def z659 : W := mkw 0x00012010b058c602 0x5000048042c16318 0x10000000f0700000 0x0040000003c1c000

def z660 : W := mkw 0x1003b7859281f948 0x64400ede164a07e5 0xe09fff8f018fffff 0xfb827ffe3c063fff

def z661 : W := mkw 0x1ffc96806fee3807 0xa07ff25a01bfb8e0 0xbffe1f80ffff183d 0x3efff87e03fffc60

def z662 : W := mkw 0x0002010500010148 0x0400080414000405 0x0000000f000007c2 0x000000003c00001f

def z663 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c738e700003 0x768da471ce39c000

def z664 : W := mkw 0x0000000020480002 0x0000000000812000 0x10000000f078002c 0x0040000003c1e000

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000300009cc3 0x400000000c000273

def z666 : W := mkw 0x3fffff6fdb00d03c 0x40fffffdbf6c0340 0xfffffffffe000003 0xfffffffffff80000

def z667 : W := mkw 0x0001041086349481 0x180004104218d252 0x800800038e749cf7 0x720020000e39d273

def z668 : W := mkw 0x2ffdfa7ab058c632 0x50bff7e9eac16318 0xff71fc7cf078e72e 0xeffdc7f1f3c1e39c

def z669 : W := mkw 0x012a018504a52949 0x2404a806141294a5 0x83fe038f8fffffff 0xfe0ff80e3e3fffff

def z670 : W := mkw 0x05794c7a863494b1 0x1815e531ea18d252 0xef79fc7f8e749cf7 0xffbde7f1fe39d273

def z671 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0xff01fc00fe00e00c 0xcffc07f003f80380

def z672 : W := mkw 0x3ffefbef5980683c 0x60fffbefbd6601a0 0xffffffff7180600b 0xfffffffffdc60180

def z673 : W := mkw 0x1a83b785db81f94c 0x646a0ede176e07e5 0xff97ff8cff8bfb1d 0xdffe5ffe33fe2fec

def z674 : W := mkw 0x0ffd6058fd7ec627 0xd03ff58163f5fb18 0xdfffe070ffff003c 0x3f7fff81c3fffc00

def z675 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23611c708e749cf4 0x048d8471c239d273

def z676 : W := mkw 0x0001040082009000 0x0000041002080240 0x20011c0000009801 0x4080047000000260

def z677 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc61e070f070e00c 0xcf718781c3c1c380

def z678 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c61e070f078e72c 0x05718781c3c1e39c

def z679 : W := mkw 0x2ffffb6f9000c038 0x40bfffedbe400300 0xfffffffff000e00f 0xffffffffffc00380

def z680 : W := mkw 0x1ffdb600ff6ed007 0xc07ff6d803fdbb40 0x7f61fc00fe700000 0x05fd87f003f9c000

def z681 : W := mkw 0x0001041086349481 0x180004104218d252 0x000000008e700000 0x000000000239c000

def z682 : W := mkw 0x0001001080108400 0x1000040042004210 0x0000000080708424 0x000000000201c210

def z683 : W := mkw 0x257e496f00000038 0x0095f925bc000000 0xa37f1c7f00000003 0x768dfc71fc000000

def z684 : W := mkw 0x0fff0db7efffbddf 0xbc3ffc36dfbffef7 0xbfff1fffffffffff 0xfefffc7fffffffff

def z685 : W := mkw 0x0002010500000008 0x0000080414000000 0x0096038c00000000 0x8802580e30000000

def z686 : W := mkw 0x0000000000000000 0x0000000000000000 0x808000000180001c 0x1a02000000060000

def z687 : W := mkw 0x1ba9bea2dfa4f895 0x686ea6fa8b7e93e2 0xff89ff83ff84f8dd 0xdffe27fe0ffe13e3

def z688 : W := mkw 0x0579687ab058c632 0x5015e5a1eac16318 0xff79fc7ff078e72f 0xfffde7f1ffc1e39c

def z689 : W := mkw 0x0ed1f258b058c622 0x503b47c962c16318 0xfff1fffcf078e72f 0xffffc7fff3c1e39c

def z690 : W := mkw 0x0450604830484222 0x4011418120c12108 0xdc10e00c7008e72e 0xeb70438031c0239c

def z691 : W := mkw 0x0a810400cb009004 0x002a0410032c0240 0xbf811c00ff80981d 0x5efe047003fe0260

def z692 : W := mkw 0x2fffdfff86b5bdf9 0x3cbfff7ffe1ad6f7 0xefffffff8fffffff 0xffbffffffe3fffff

def z693 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0xef69fc7300000003 0x77bda7f1cc000000

def z694 : W := mkw 0x0ffc00806dee2807 0xa03ff00201b7b8a0 0x9ffe0380fffff83d 0xfe7ff80e03ffffe0

def z695 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23091c730e049cd3 0x508c2471cc381273

def z696 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23081c038e749cf5 0x108c20700e39d273

def z697 : W := mkw 0x1bac96804fa63805 0xa06eb25a013e98e0 0x238e1f800f871811 0x108e387e003e1c60

def z698 : W := mkw 0x0000008000802800 0x20000002000200a0 0x000000000180f81c 0x00000000000603e0

def z699 : W := mkw 0x2bae9ba700812958 0x24aeba6e9c0204a5 0x238e1f83018718d1 0x108e387e0c061c63

def z700 : W := mkw 0x0000000000000000 0x0000000000000000 0x00080003000404e2 0x200020000c001013

def z701 : W := mkw 0x045160d8b0d9ef62 0x7411458362c367bd 0xdc71e07cf1fffffe 0xef71c781f3c7ffff

def z702 : W := mkw 0x1000b28010806800 0x604002ca004201a0 0x4000e38000006000 0x8100038e00000180

def z703 : W := mkw 0x0ed6018569cb294e 0xa43b580615a72ca5 0x9c9e038f718fffff 0xfa72780e3dc63fff

def z704 : W := mkw 0x212e092700000018 0x0084b8249c000000 0x000e000300000000 0x000038000c000000

def z705 : W := mkw 0x0000000000000000 0x0000000000000000 0x8061007000000002 0x66018401c0000000

def z706 : W := mkw 0x1ba9b680dfa4f805 0x606ea6da037e93e0 0xffe9ff80fff4f83d 0xffffa7fe03ffd3e0

def z707 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c71e07cf078e72c 0x8d71c781f3c1e39c

def z708 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff91ff8cff80f81f 0xfffe47fe33fe03e0

def z709 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0xff81ff80ff80001d 0xdffe07fe03fe0000

def z710 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff80700027 0xffbffffffe01c000

def z711 : W := mkw 0x0002018500812948 0x24000806140204a5 0x009e038f018ffffd 0x9802780e3c063fff

def z712 : W := mkw 0x2ffedb6f4900003c 0x00bffb6dbd240000 0xffffffffff8f003f 0xfffffffffffe3c00

def z713 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f81ff80ff800000 0x05fe07fe03fe0000

def z714 : W := mkw 0x0ffc40486d6e0227 0x803ff10121b5b808 0x9ffe000cffff033c 0x3e7ff80033fffc0c

def z715 : W := mkw 0x2a82db6f00000038 0x00aa0b6dbc000000 0x6c81ffff00000003 0xc9b207fffc000000

def z716 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0xe009ffff00000003 0xf38027fffc000000

def z717 : W := mkw 0x10012490fbd9ff46 0x7440049243ef67fd 0x10000000fffffffc 0x0040000003ffffff

def z718 : W := mkw 0x157db680b6eef803 0xe055f6da02dbbbe0 0x607fff80007ff821 0xe181fffe0001ffe0

def z719 : W := mkw 0x2002db6f6d6e003f 0x80800b6dbdb5b800 0x7001ffffffff003f 0xc1c007fffffffc00

def z720 : W := mkw 0x2ffedb6f246f017b 0x84bffb6dbc91bc05 0xefffffff007f07e3 0xffbffffffc01fc1f

def z721 : W := mkw 0x04516458b258d622 0x5011459162c96358 0xff79fc7ffe7cffff 0xfffde7f1fff9f3ff

def z722 : W := mkw 0x2ffcdaea00812970 0x24bff36ba80204a5 0x6f61fc70018ffffc 0x05bd87f1c0063fff

def z723 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6ff7ffff00000003 0xcdbfdffffc000000

def z724 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc79e07ff078e72f 0xff71e781ffc1e39c

def z725 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c738e74fcff 0xfe8da471ce39d3f3

def z726 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff80181d 0x1ffe07fe03fe0060

def z727 : W := mkw 0x1a80b6805b807804 0x606a02da016e01e0 0x7f80ff807f806008 0x89fe03fe01fe0180

def z728 : W := mkw 0x0ffe01856def294f 0xa43ff80615b7bca5 0x1f60038ffe70ffc3 0xc47d800e3ff9c3ff

def z729 : W := mkw 0x0ffc08226d6e0097 0x883ff02089b5b802 0x9ffe0003ffff00fc 0x3e7ff8000ffffc03

def z730 : W := mkw 0x257edb6f00000038 0x0095fb6dbc000000 0xe37fffff00000003 0xf78dfffffc000000

def z731 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff00008427 0xffbffffffc000210

def z732 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xfffffffffffb000b 0xffffffffffffec00

def z733 : W := mkw 0x01280c3206341491 0x1804a030c818d052 0xa3681c730e749cf7 0x728da071cc39d273

def z734 : W := mkw 0x2ffedb6f246c003b 0x00bffb6dbc91b000 0xfffffffffe7c003f 0xfffffffffff9f000

def z735 : W := mkw 0x2bae9ba74da7295d 0xa4aeba6e9d369ca5 0x238e1f830f8718d1 0x108e387e0c3e1c63

def z736 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6f61fff300000001 0x05bd87ffcc000000

def z737 : W := mkw 0x257edb6f246e003b 0x8095fb6dbc91b800 0x607fffff007f0023 0xe181fffffc01fc00

def z738 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff000418d3 0xffbffffffc001063

def z739 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff84fcfd 0xdffe07fe03fe13f3

def z740 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c738e7cffff 0x768da471ce39f3ff

def z741 : W := mkw 0x2ffedb6f4d26003d 0x80bffb6dbd349800 0xefffffff0e000003 0xffbffffffc380000

def z742 : W := mkw 0x05786c6a366c52b3 0x4815e1b1a8d9b14a 0x7f18fc0f7e0c7bd9 0x99fc63f03df831ef

def z743 : W := mkw 0x1ffd2490fffefe07 0xf07ff49243fffbf8 0x9ffe0000ffffff3c 0x3e7ff80003fffffc

def z744 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff01ff80fe00f815 0xd7fc07fe03f803e0

def z745 : W := mkw 0x10012490db90fe04 0x70400492436e43f8 0x10000000ff80ff1c 0x0040000003fe03fc

def z746 : W := mkw 0x0ba800004d240005 0x002ea00001349000 0x9ffe0000ffff003c 0x3e7ff80003fffc00

def z747 : W := mkw 0x2ffedb6f6d6f017f 0x84bffb6dbdb5bc05 0xffffffffffff07ff 0xfffffffffffffc1f

def z748 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xeffffffc00000000 0xbfbffffff0000000

def z749 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc61e07cf070e726 0xe7718781f3c1c39c

def z750 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80fe00f801 0xdffe07fe03f803e0

def z751 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9fff0070ffff003e 0x7e7ffc01c3fffc00

def z752 : W := mkw 0x0ed400006d6e0007 0x803b500001b5b800 0x1c960000fffb0008 0x0872580003ffec00

def z753 : W := mkw 0x2452db6f2048003a 0x00914b6dbc812000 0xfc71fffff078002f 0xeff1c7ffffc1e000

def z754 : W := mkw 0x0ba89a2200000010 0x002ea26888000000 0xefe1fff000000001 0xdfbf87ffc0000000

def z755 : W := mkw 0x05780000246c0003 0x0015e0000091b000 0x9ffe0000ffff003c 0x3e7ff80003fffc00

def z756 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xfffffffffff70013 0xffffffffffffdc00

def z757 : W := mkw 0x2ffcda6a6d6e0037 0x80bff369a9b5b800 0xfffffff0ffff003d 0xffffffffc3fffc00

def z758 : W := mkw 0x0ed50c32eb5a9496 0x983b5430cbad6a52 0x3c971c73718b9ccb 0x48f25c71cdc62e73

def z759 : W := mkw 0x0a80920000000000 0x002a024800000000 0xefe1fff000000003 0xffbf87ffc0000000

def z760 : W := mkw 0x0450604830484222 0x4011418120c12108 0xdc71e07cf078632e 0xef71c781f3c1e18c

def z761 : W := mkw 0x1ba92490dfb4fc85 0x786ea492437ed3f2 0x9fe80000fff4fcfc 0x3e7fa00003ffd3f3

def z762 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff9fff8cff8fff3f 0xfffe7ffe33fe3ffc

def z763 : W := mkw 0x257e497f247e063b 0x9095f925fc91f818 0x007e007f007f0722 0x2001f801fc01fc1c

def z764 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c71e07cf078e70a 0xcd71c781f3c1e39c

def z765 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0x7f61fffffe700003 0xc5fd87fffff9c000

def z766 : W := mkw 0x257e497f247e04bb 0x9895f925fc91f812 0x007e007f007f04e2 0x2001f801fc01fc13

def z767 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff89ff83ff80f81f 0xfffe27fe0ffe03e0

def z768 : W := mkw 0x1a81b680db81f944 0x646a06da036e07e5 0xff81ff80ff8bfb1d 0xdffe07fe03fe2fec

def z769 : W := mkw 0x2002db6f00010178 0x04800b6dbc000405 0x6001ffff000007c3 0xc18007fffc00001f

def z770 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff8cff80ff1f 0xdffe07fe33fe03fc

def z771 : W := mkw 0x2a82db6f00000038 0x00aa0b6dbc000000 0x6f01ffff00000003 0xc5bc07fffc000000

def z772 : W := mkw 0x1ed0d6d86bd83e26 0x307b435b61af60f8 0x23f01ffc0ff81f33 0x308fc07ff03fe07c

def z773 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1cfe0000ffff003c 0x2873f80003fffc00

def z774 : W := mkw 0x2ffedb6f2048003a 0x00bffb6dbc812000 0xefffffff00780023 0xffbffffffc01e000

def z775 : W := mkw 0x2bafbb37b058c61a 0x50aebeecdec16318 0x338e1f83f078e72d 0x10ce387e0fc1e39c

def z776 : W := mkw 0x0ed400006d6e0007 0x803b500001b5b800 0x9c9e0000ffff003c 0x3a72780003fffc00

def z777 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0xe301ffff00000003 0xd78c07fffc000000

def z778 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xef69ffff00000003 0xf7bda7fffc000000

def z779 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff0000e00f 0xffbffffffc000380

def z780 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23691c738e741cf3 0x348da471ce39d073

def z781 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff8fff80ff87f81d 0xdffe3ffe03fe1fe0

def z782 : W := mkw 0x2000da6a00000030 0x00800369a8000000 0x6001fff000000001 0xc18007ffc0000000

def z783 : W := mkw 0x0002018500812948 0x24000806140204a5 0xcc9fe38f018fffff 0xff327f8e3c063fff

def z784 : W := mkw 0x2ffedb6f04240039 0x00bffb6dbc109000 0xefffffff8e700003 0xffbffffffe39c000

def z785 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xffe1fff0ff80f81f 0xffff87ffc3fe03e0

def z786 : W := mkw 0x2a86db6f00000038 0x00aa1b6dbc000000 0x6087ffff00000003 0xc1821ffffc000000

def z787 : W := mkw 0x2ffedb6f4900003c 0x00bffb6dbd240000 0xffffffff7180000b 0xfffffffffdc60000

def z788 : W := mkw 0x000160589010c620 0x5000058162404318 0xdc61e07cf070e72e 0xef718781f3c1c39c

def z789 : W := mkw 0x057c00006d6e0007 0x8015f00001b5b800 0x937e0000ffff003c 0x364df80003fffc00

def z790 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff80601c 0x9ffe07fe03fe0180

def z791 : W := mkw 0x0a819600cb009004 0x002a0658032c0240 0xff81ff80ff80981d 0xdffe07fe03fe0260

def z792 : W := mkw 0x2ed7d75d863494a9 0x18bb5f5d7618d252 0x4c96e38c8e749cf4 0x89325b8e3239d273

def z793 : W := mkw 0x2ffedb6f4d26003d 0x80bffb6dbd349800 0xffffffffff87001f 0xfffffffffffe1c00

def z794 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff000404e3 0xffbffffffc001013

def z795 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xfffffff3ffff003d 0x3fffffffcffffc00

def z796 : W := mkw 0x2ed6db6f694a003e 0x80bb5b6dbda52800 0x7c97ffff718b000b 0xc9f25ffffdc62c00

def z797 : W := mkw 0x2ffedb6f6948003e 0x00bffb6dbda52000 0xfffffffffff8003f 0xffffffffffffe000

def z798 : W := mkw 0x0ffc9a226d6e0017 0x803ff26889b5b800 0xfffffff3ffff003f 0xffffffffcffffc00

def z799 : W := mkw 0x2452db6f00000038 0x00914b6dbc000000 0x6071ffff00000003 0xe181c7fffc000000

def z800 : W := mkw 0x1a83b705db01d14c 0x446a0edc176c0745 0x7f1ffc0ffe0f07e2 0x25fc7ff03ff83c1f

def z801 : W := mkw 0x01292c329634d691 0x5804a4b0ca58d35a 0xa3691c738e74fff7 0x768da471ce39d3ff

def z802 : W := mkw 0x0ed40000694a0006 0x803b500001a52800 0x9ff60000fffb003c 0x3e7fd80003ffec00

def z803 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff00040037 0xffbffffffc001000

def z804 : W := mkw 0x000120109010c400 0x5000048042404310 0xdc71e07cf078e72e 0xef71c781f3c1e39c

def z805 : W := mkw 0x045361ddb0d9ef6a 0x74114d8776c367bd 0x5cefe3f3f1f718d1 0x1573bf8fcfc7dc63

def z806 : W := mkw 0x0ed0d24800000020 0x003b434920000000 0xefe1fff000000001 0xdfbf87ffc0000000

def z807 : W := mkw 0x257e496f246f017b 0x8495f925bc91bc05 0x007e007f007f07e2 0x2001f801fc01fc1f

def z808 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff00009cc3 0xffbffffffc000273

def z809 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0x601fffff00000003 0xe1807ffffc000000

def z810 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e07cf07cfffe 0xef71c781f3c1f3ff

def z811 : W := mkw 0x2ed6db6f00000038 0x00bb5b6dbc000000 0xecf7ffff00000003 0xefb3dffffc000000

def z812 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0x6097ffff00000003 0xc9825ffffc000000

def z813 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c738e709cc3 0x768da471ce39c273

def z814 : W := mkw 0x1a80b28059806804 0x606a02ca016601a0 0xff81ff80ff80601d 0xdffe07fe03fe0180

def z815 : W := mkw 0x2ffedb6f00010178 0x04bffb6dbc000405 0xefffffff018f07ff 0xffbffffffc063c1f

def z816 : W := mkw 0x2ffc9a226d6e0017 0x80bff26889b5b800 0xbffe1c00ffff003c 0x3efff87003fffc00

def z817 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6cffffff00000003 0xe9b3fffffc000000

def z818 : W := mkw 0x045000006d6e0007 0x8011400001b5b800 0x9cfe0000ffff003c 0x3e73f80003fffc00

def z819 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdcf1e3fcf078e72f 0xff73c78ff3c1e39c

def z820 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0x6001fff300000001 0x018007ffcc000000

def z821 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3791c7f8e749cf7 0xfe8de471fe39d273

def z822 : W := mkw 0x0ff8da6a00000030 0x003fe369a8000000 0xeff9ffff00000003 0xffbfe7fffc000000

def z823 : W := mkw 0x0ffc9a2200000010 0x003ff26888000000 0xeffffff300000003 0xffbfffffcc000000

def z824 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c61e07cf078e72e 0xc5718781f3c1e39c

def z825 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3e91ff38e749cf7 0xfe8fa47fce39d273

def z826 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdcffe07ff1ffffff 0xff73ff81ffc7ffff

def z827 : W := mkw 0x10012490fffefe07 0xf040049243fffbf8 0x10000000ffffff3c 0x0040000003fffffc

def z828 : W := mkw 0x1a80b6805b807804 0x606a02da016e01e0 0x7f80ff807f801811 0x11fe03fe01fe0060

def z829 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe000cffff003e 0xfe7ff80033fffc00

def z830 : W := mkw 0x2ffedb6f2048003a 0x00bffb6dbc812000 0xfffffffff078e72f 0xffffffffffc1e39c

def z831 : W := mkw 0x10012490fffefc87 0xf840049243fffbf2 0x10000000fffffcfc 0x0040000003fffff3

def z832 : W := mkw 0x212adb6f04240039 0x0084ab6dbc109000 0xe369ffff8e740037 0xf78da7fffe39d000

def z833 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1ff60000ffff003c 0x0c7fd80003fffc00

def z834 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3791c7f8e7c9ff7 0x768de471fe39f27f

def z835 : W := mkw 0x2002db6f00010178 0x04800b6dbc000405 0x601fffff000f07e3 0xe1807ffffc003c1f

def z836 : W := mkw 0x2baadb6f00000038 0x00aeab6dbc000000 0xefe9ffff00000003 0xffbfa7fffc000000

def z837 : W := mkw 0x2ffedb6f2048003a 0x00bffb6dbc812000 0xfffffffff1ff003f 0xffffffffffc7fc00

def z838 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff01870013 0xffbffffffc061c00

def z839 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3611c738e709cd7 0x568d8471ce39c273

def z840 : W := mkw 0x0ed400006d6e0007 0x803b500001b5b800 0x9f960000ffff003c 0x1e7e580003fffc00

def z841 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0x6fe1fff000000000 0x8dbf87ffc0000000

def z842 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1ffe0000ffff0028 0x2c7ff80003fffc00

def z843 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1fee0000ffff003c 0x147fb80003fffc00

def z844 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0xec01ffff00000003 0xcfb007fffc000000

def z845 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0x7f01ff80fe000001 0xc5fc07fe03f80000

def z846 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff018b000b 0xffbffffffc062c00

def z847 : W := mkw 0x0ed0d24869480026 0x003b434921a52000 0xfff1fffcfff8003f 0xffffc7fff3ffe000

def z848 : W := mkw 0x2ffcda6a6d6e0037 0x80bff369a9b5b800 0xffe1fff0fff0001d 0xdfff87ffc3ffc000

def z849 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0xe011ffff0008e72f 0xeb8047fffc00239c

def z850 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0000ffff9cfc 0x3e7ff80003fffe73

def z851 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f01ff80fe001801 0x05fc07fe03f80060

def z852 : W := mkw 0x01292c329634d491 0x5804a4b0ca58d352 0xe369fc738e74fcf7 0xf78da7f1ce39d3f3

def z853 : W := mkw 0x000000006d6e0007 0x8000000001b5b800 0x108e0000ffff003c 0x1042380003fffc00

def z854 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0003ffff003f 0x7e7ff8000ffffc00

def z855 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff00080723 0xffbffffffc00201c

def z856 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6fffffff00000002 0xadbffffffc000000

def z857 : W := mkw 0x357f6defdb80f83c 0x60d5fdb7bf6e03e0 0x107e007fff80f81e 0x2041f801fffe03e0

def z858 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23691c738e749cf6 0x248da471ce39d273

def z859 : W := mkw 0x0002018500812948 0x24000806140204a5 0x009e038f018ffffe 0xa802780e3c063fff

def z860 : W := mkw 0x1baa9fa74fa539dd 0x2c6eaa7e9d3e94e7 0x238e1f830f8718d1 0x108e387e0c3e1c63

def z861 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0xff81ff80fe009815 0xdffe07fe03f80260

def z862 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xfffffffffff0001f 0xffffffffffffc000

def z863 : W := mkw 0x0bad6058dd36c625 0xd02eb5816374db18 0x438fe07c0f87e712 0xd10e3f81f03e1f9c

def z864 : W := mkw 0x2ffedb6f00010178 0x04bffb6dbc000405 0xefffffff000700c3 0xffbffffffc001c03

def z865 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6f7fffff00000003 0xe5bdfffffc000000

def z866 : W := mkw 0x0bac00006d6e0007 0x802eb00001b5b800 0x138e0000fff70010 0x104e380003ffdc00

def z867 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xfffffffcffff003c 0xbffffffff3fffc00

def z868 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff97ff80ff8bf81d 0xdffe5ffe03fe2fe0

def z869 : W := mkw 0x0ffc40486d6e0027 0x803ff10121b5b800 0xdfffe07cffffe73e 0xff7fff81f3ffff9c

def z870 : W := mkw 0x1a81b690db90fc04 0x706a06da436e43f0 0xff81fff0ff80fc1f 0xdffe07ffc3fe03f0

def z871 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff9fff80ff80f81d 0xfffe7ffe03fe03e0

def z872 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1fe60000fff30000 0x047f980003ffcc00

def z873 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xbf691c73fe749cff 0x7efda471cff9d273

def z874 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0xeff1fffc00000003 0xffbfc7fff0000000

def z875 : W := mkw 0x2baedb6f00000038 0x00aebb6dbc000000 0xe39fffff00000003 0xfb8e7ffffc000000

def z876 : W := mkw 0x2ffedb6f04240039 0x00bffb6dbc109000 0xefffffff0e040013 0xffbffffffc381000

def z877 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff80fc3f 0xfffe07fe03fe03f0

def z878 : W := mkw 0x012b0db786b5bdd9 0x3c04ac36de1ad6f7 0x23f71ffc8ffb6308 0x8c8fdc7ff23fed8c

def z879 : W := mkw 0x0a80920049000004 0x002a024801240000 0xff81ff80fe000001 0xdffe07fe03f80000

def z880 : W := mkw 0x257edb6f00000038 0x0095fb6dbc000000 0x6061ffff00000003 0xc18187fffc000000

def z881 : W := mkw 0x257e497f247c06bb 0x1895f925fc91f01a 0x007e007f007c07e2 0x2001f801fc01f01f

def z882 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdf71e07cfe78e73e 0xff7dc781f3f9e39c

def z883 : W := mkw 0x2ffedb6f204a003a 0x80bffb6dbc812800 0xefffffff000b0003 0xffbffffffc002c00

def z884 : W := mkw 0x1a81b690db90fc04 0x706a06da436e43f0 0xff81ff80fff0fc3d 0xdffe07fe03ffc3f0

def z885 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0xe009ffff00049cf7 0xf38027fffc001273

def z886 : W := mkw 0x2baedb6f00000038 0x00aebb6dbc000000 0xe3efffff00000003 0xf78fbffffc000000

def z887 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c71e07c7078e72a 0xe971c781f1c1e39c

def z888 : W := mkw 0x1003f7dd9291ff68 0x74400fdf764a47fd 0x6001ffff0000ffc3 0xc18007fffc0003ff

def z889 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0x6001fffc00000000 0x818007fff0000000

def z890 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xffffffff71ff002b 0xfffffffffdc7fc00

def z891 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c70e07cf078e72e 0xa971c381f3c1e39c

def z892 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3ff1c7f8fffffff 0xfe8ffc71fe3fffff

def z893 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xeff7fffc00000002 0xefbfdffff0000000

def z894 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3e91c738ff49cff 0x7e8fa471ce3fd273

def z895 : W := mkw 0x0002018500812948 0x24000806140204a5 0x009e038f018fffdb 0xd802780e3c063fff

def z896 : W := mkw 0x2bae9b2700000018 0x00aeba6c9c000000 0xefeffff300000003 0xffbfbfffcc000000

def z897 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff0008630b 0xffbffffffc00218c

def z898 : W := mkw 0x01280c2206241091 0x0804a03088189042 0xa3691c738e7418f7 0x768da471ce39d063

def z899 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9fee0000fff70034 0x367fb80003ffdc00

def z900 : W := mkw 0x012d0c3286369491 0x9804b430ca18da52 0xa36f1c738e779cf7 0x768dbc71ce39de73

def z901 : W := mkw 0x212edb6f00000038 0x0084bb6dbc000000 0x600fffff00000003 0xc1803ffffc000000

def z902 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0000ffffe73c 0x3e7ff80003ffff9c

def z903 : W := mkw 0x0450404820480022 0x0011410120812000 0xdc71e07cf078e72e 0xef71c781f3c1e39c

def z904 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c71e07cf078e72e 0x2571c781f3c1e39c

def z905 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff91ff80ff88f83d 0xfffe47fe03fe23e0

def z906 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f01ff80fe006000 0x85fc07fe03f80180

def z907 : W := mkw 0x01280c3206341491 0x1804a030c818d052 0xa3681c738e741cf7 0x368da071ce39d073

def z908 : W := mkw 0x1a80b6805b807804 0x606a02da016e01e0 0xff80ff80ff80781d 0x9ffe03fe03fe01e0

def z909 : W := mkw 0x212adb6f00000038 0x0084ab6dbc000000 0xe3ffffff00000003 0xff8ffffffc000000

def z910 : W := mkw 0x2ffedb6f04240039 0x00bffb6dbc109000 0xefffffff00740023 0xffbffffffc01d000

def z911 : W := mkw 0x2ed6db6f00000038 0x00bb5b6dbc000000 0xef97ffff00000003 0xdfbe5ffffc000000

def z912 : W := mkw 0x1a81b680db81f944 0x646a06da036e07e5 0xff91ff8cff8fffff 0xfffe47fe33fe3fff

def z913 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c71e07cf078e722 0xe571c781f3c1e39c

def z914 : W := mkw 0x01280c3206341491 0x1804a030c818d052 0x23681c730e7418d1 0x108da071cc39d063

def z915 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6f9fffff00000003 0xd9be7ffffc000000

def z916 : W := mkw 0x2ffedb6f00010178 0x04bffb6dbc000405 0xefffffff000b0303 0xffbffffffc002c0c

def z917 : W := mkw 0x257edb6f00000038 0x0095fb6dbc000000 0xec7fffff00000003 0xefb1fffffc000000

def z918 : W := mkw 0x1ba8bab25db46c95 0x786ea2eac976d1b2 0x5ce8e3f371f464ea 0xa973a38fcdc7d193

def z919 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f81ff80ff80f81d 0x15fe07fe03fe03e0

def z920 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xffffffffffff9cff 0xfffffffffffffe73

def z921 : W := mkw 0x2ffedb6f4d26003d 0x80bffb6dbd349800 0xefffffff0f8f003f 0xffbffffffc3e3c00

def z922 : W := mkw 0x2ffedb6f4900003c 0x00bffb6dbd240000 0xefffffff0f800013 0xffbffffffc3e0000

def z923 : W := mkw 0x0ffc08226d6e0017 0x803ff02089b5b800 0xbfff1c70ffff003c 0x3efffc71c3fffc00

def z924 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c738e7418d3 0x768da471ce39d063

def z925 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff0180001f 0xffbffffffc060000

def z926 : W := mkw 0x000000006d6e0007 0x8000000001b5b800 0x101e0000ffff003c 0x2040780003fffc00

def z927 : W := mkw 0x0ffc08226d6e0017 0x803ff02089b5b800 0xbfff1c73ffff9cff 0x7efffc71cffffe73

def z928 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23611c738e7018c1 0x048d8471ce39c063

def z929 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0x7ff7fffcfffb0008 0x8dffdffff3ffec00

def z930 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff91ff8cff88fb1d 0xdffe47fe33fe23ec

def z931 : W := mkw 0x2baedb6f00000038 0x00aebb6dbc000000 0x6301ffff00000003 0xc18c07fffc000000

def z932 : W := mkw 0x1a81b680db81f944 0x646a06da036e07e5 0xff81ff80ff87f8dd 0xdffe07fe03fe1fe3

def z933 : W := mkw 0x0bac00006d6e0007 0x802eb00001b5b800 0x93ee0000ffff003c 0x364fb80003fffc00

def z934 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6fefffff00000003 0xd5bfbffffc000000

def z935 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefeffff300000001 0xdfbfbfffcc000000

def z936 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23691c738e749ce3 0x648da471ce39d273

def z937 : W := mkw 0x257e496f246e003b 0x8095f925bc91b800 0x007e007f00700002 0x2001f801fc01c000

def z938 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3791c738e7c9cff 0x7e8de471ce39f273

def z939 : W := mkw 0x0450605830584622 0x5011418160c16118 0xdc70e07cf078672e 0xaf71c381f3c1e19c

def z940 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1ffe0000ffff0030 0x347ff80003fffc00

def z941 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x13fe0000ffff003c 0x304ff80003fffc00

def z942 : W := mkw 0x100124909290fe00 0x70400492424a43f8 0x000000000000ff00 0x00000000000003fc

def z943 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6f61fffc00000000 0x85bd87fff0000000

def z944 : W := mkw 0x100124909290fc80 0x78400492424a43f2 0x000000000000fcc0 0x00000000000003f3

def z945 : W := mkw 0x1ed2f3cd79c96b6e 0x647b4bcf35e725ad 0x5c96e38c718b6308 0x89725b8e31c62d8c

def z946 : W := mkw 0x2ffedb6f04240039 0x00bffb6dbc109000 0xefffffff8e749cf7 0xffbffffffe39d273

def z947 : W := mkw 0x0ed0000069480006 0x003b400001a52000 0x9ffe0000ffff003c 0x3e7ff80003fffc00

def z948 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0x6001ffff00009cc3 0xc18007fffc000273

def z949 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23611c738e749cf7 0x448d8471ce39d273

def z950 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff8ff83d 0xdffe07fe03fe3fe0

def z951 : W := mkw 0x1ffd2490fffefc87 0xf87ff49243fffbf2 0x9ffe0000fffffcfc 0x3e7ff80003fffff3

def z952 : W := mkw 0x0a81b200d900c004 0x402a06c803640300 0xff81ff80ff80e01d 0xdffe07fe03fe0380

def z953 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff89ff80ff84f83d 0xfffe27fe03fe13e0

def z954 : W := mkw 0x057a496f00000038 0x0015e925bc000000 0xefffffff00000003 0xffbffffffc000000

def z955 : W := mkw 0x2ffcda6a6d6e0037 0x80bff369a9b5b800 0xfffffc7cffff003e 0xfffffff1f3fffc00

def z956 : W := mkw 0x1001249096b4fc81 0x78400492425ad3f2 0x000000008e74fcf4 0x000000000239d3f3

def z957 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff0000e703 0xffbffffffc00039c

def z958 : W := mkw 0x0a80928049802804 0x202a024a012600a0 0xff81ff80ff80f81d 0xdffe07fe03fe03e0

def z959 : W := mkw 0x10012490b2d8fe02 0x7040049242cb63f8 0x10000000f078ff2c 0x0040000003c1e3fc

def z960 : W := mkw 0x0002018500812948 0x24000806140204a5 0x9c9e038ff18fffff 0xfe72780e3fc63fff

def z961 : W := mkw 0x1a8096804b803804 0x206a025a012e00e0 0xff81ff80ff80181d 0xdffe07fe03fe0060

def z962 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e07cf078632c 0xaf71c781f3c1e18c

def z963 : W := mkw 0x000124809280f800 0x60000492024a03e0 0xff81ff80ff80f81d 0xdffe07fe03fe03e0

def z964 : W := mkw 0x0128082204240011 0x0004a02088109000 0xa3691c738e749cf7 0x768da471ce39d273

def z965 : W := mkw 0x1a81b680db81f944 0x646a06da036e07e5 0xff89ff83ff8fffff 0xfffe27fe0ffe3fff

def z966 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ff60000fffb001c 0x1e7fd80003ffec00

def z967 : W := mkw 0x1003bfb79291fdd8 0x7c400efede4a47f7 0x6001ffff0000ffc3 0xc18007fffc0003ff

def z968 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f81ff80ff80f811 0xd5fe07fe03fe03e0

def z969 : W := mkw 0x0ffc40486d6e0027 0x803ff10121b5b800 0xdfffe070ffff003c 0x3f7fff81c3fffc00

def z970 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0000fffb0008 0x3e7ff80003ffec00

def z971 : W := mkw 0x2ffedb6f694a003e 0x80bffb6dbda52800 0xffffffff70000003 0xfffffffffdc00000

def z972 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xffffffffffffe73f 0xffffffffffffff9c

def z973 : W := mkw 0x2ffedb6f4d26003d 0x80bffb6dbd349800 0xefffffff8ff70037 0xffbffffffe3fdc00

def z974 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff01ff80fe00f80d 0xcffc07fe03f803e0

def z975 : W := mkw 0x2a82db6f4900003c 0x00aa0b6dbd240000 0xff81ffffff80001f 0xdffe07fffffe0000

def z976 : W := mkw 0x212adb6f00000038 0x0084ab6dbc000000 0x6361ffff00000003 0xc58d87fffc000000

def z977 : W := mkw 0x10012490db90fc04 0x70400492436e43f0 0x10000000fff0fc3c 0x0040000003ffc3f0

def z978 : W := mkw 0x04556058b05ac622 0xd011558162c16b18 0xdc77e07cf07be72e 0xef71df81f3c1ef9c

def z979 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xff71fc7cf078e72f 0xfffdc7f1f3c1e39c

def z980 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff80e00c 0xcffe07fe03fe0380

def z981 : W := mkw 0x0002018500812948 0x24000806140204a5 0xa39f1f8f018fffff 0xfe8e7c7e3c063fff

def z982 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff806009 0xdffe07fe03fe0180

def z983 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1f7e0000ffff003c 0x247df80003fffc00

def z984 : W := mkw 0x10012490dfb4fc85 0x78400492437ed3f2 0x10000000fff0f81c 0x0040000003ffc3e0

def z985 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c738e7418f5 0x368da471ce39d063

def z986 : W := mkw 0x1a81b690db90fc04 0x706a06da436e43f0 0xffe9fff3fff4fcff 0xffffa7ffcfffd3f3

def z987 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff018f9cff 0xffbffffffc063e73

def z988 : W := mkw 0x2ed6db6f00000038 0x00bb5b6dbc000000 0xec9fffff00000003 0xfbb27ffffc000000

def z989 : W := mkw 0x0ffc486a6d6e0037 0x803ff121a9b5b800 0xfffffc7fffff003f 0xfffffff1fffffc00

def z990 : W := mkw 0x0000d24800000020 0x0000034920000000 0x6001fffc00000003 0xc18007fff0000000

def z991 : W := mkw 0x00009a2200000010 0x0000026888000000 0x6001fff300000003 0xc18007ffcc000000

def z992 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f81ff80ff80f81c 0x8dfe07fe03fe03e0

def z993 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f81ff80ff807819 0x9dfe07fe03fe01e0

def z994 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc79e07cf07ce73e 0xff71e781f3c1f39c

def z995 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e07cf078630a 0xef71c781f3c1e18c

def z996 : W := mkw 0x045400006d6e0007 0x8011500001b5b800 0x10160000ffff003c 0x0040580003fffc00

def z997 : W := mkw 0x04516458b258d622 0x5011459162c96358 0xff71fc7cfe78e72e 0xeffdc7f1f3f9e39c

def z998 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0x608fffff00000003 0xd1823ffffc000000

def z999 : W := mkw 0x000000006d6e0007 0x8000000001b5b800 0x10960000ffff003c 0x0842580003fffc00

def z1000 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xfffffffffe7f0023 0xfffffffffff9fc00

def z1001 : W := mkw 0x0a809a2200000010 0x002a026888000000 0xef81fff300000003 0xdfbe07ffcc000000

def z1002 : W := mkw 0x2ffedb6f2048003a 0x00bffb6dbc812000 0xfffffffff0700003 0xffffffffffc1c000

def z1003 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0x7f81ff80fe000000 0x8dfe07fe03f80000

def z1004 : W := mkw 0x2ffedb6f246e003b 0x80bffb6dbc91b800 0xfffffffff07f002f 0xffffffffffc1fc00

def z1005 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefeffff300000003 0x77bfbfffcc000000

def z1006 : W := mkw 0x0002018500812948 0x24000806140204a5 0x80fe038f81ffffff 0xfe03f80e3e07ffff

def z1007 : W := mkw 0x1a81b690db90fe04 0x706a06da436e43f8 0xff81ff80ff80ff1d 0xdffe07fe03fe03fc

def z1008 : W := mkw 0x2baedb6f00000038 0x00aebb6dbc000000 0x638ffff300000001 0x118e3fffcc000000

def z1009 : W := mkw 0x0ffc08226d6e0017 0x803ff02089b5b800 0xbffe1c03ffff003d 0x3efff8700ffffc00

def z1010 : W := mkw 0x1a81b690db90fc84 0x786a06da436e43f2 0xff81ff80ff80fcdd 0xdffe07fe03fe03f3

def z1011 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xefffffff0fff0033 0xffbffffffc3ffc00

def z1012 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0x6fe1fff000000001 0x15bf87ffc0000000

def z1013 : W := mkw 0x2ffedb6f246e003b 0x80bffb6dbc91b800 0xefffffff01ff003f 0xffbffffffc07fc00

def z1014 : W := mkw 0x2ffedb6f694a003e 0x80bffb6dbda52800 0xffffffffff8b001f 0xfffffffffffe2c00

def z1015 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0xe011ffff00000003 0xeb8047fffc000000

def z1016 : W := mkw 0x2452db6f00000038 0x00914b6dbc000000 0xecffffff00000003 0xffb3fffffc000000

def z1017 : W := mkw 0x0ed400006d6e0007 0x803b500001b5b800 0x9cf60000ffff003c 0x2e73d80003fffc00

def z1018 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3ff1c738e749cf7 0x7e8ffc71ce39d273

def z1019 : W := mkw 0x1a80b6805b807804 0x606a02da016e01e0 0xff81ff807f807819 0xdffe07fe01fe01e0

def z1020 : W := mkw 0x04516458b258d622 0x5011459162c96358 0xfc71fc7cf078ff2f 0xeff1c7f1f3c1e3fc

def z1021 : W := mkw 0x0ffcd2486d6e0027 0x803ff34921b5b800 0xfffffffcffff003f 0xfffffffff3fffc00

def z1022 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e07cf078ff3f 0xff71c781f3c1e3fc

def z1023 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0000ffffe03c 0xfe7ff80003ffff80

def z1024 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc7fe07cf07fe72e 0xef71ff81f3c1ff9c

def z1025 : W := mkw 0x2ed6d3cd69cb296e 0xa4bb5b4f35a72ca5 0x5c96e38c718b6308 0x89725b8e31c62d8c

def z1026 : W := mkw 0x0a80d24800000020 0x002a034920000000 0xef81fffc00000003 0xdfbe07fff0000000

def z1027 : W := mkw 0x10012490fbd8fe06 0x7040049243ef63f8 0x10000000fff0f81c 0x0040000003ffc3e0

def z1028 : W := mkw 0x0ffc40486d6e0027 0x803ff10121b5b800 0xdffee00cffff003c 0xbf7ffb8033fffc00

def z1029 : W := mkw 0x012c00006d6e0007 0x8004b00001b5b800 0x100e0000ffff003c 0x0040380003fffc00

def z1030 : W := mkw 0x2ffedb6f4900003c 0x00bffb6dbd240000 0xfffffffffe000003 0xfffffffffff80000

def z1031 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e07ff078ffef 0xef71c781ffc1e3ff

def z1032 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f80ff80ff80f81d 0x99fe03fe03fe03e0

def z1033 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xfffffffff000000f 0xffffffffffc00000

def z1034 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xeffffff300000001 0x3fbfffffcc000000

def z1035 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6fffffff00000003 0x35bffffffc000000

def z1036 : W := mkw 0x2a82db6f00000038 0x00aa0b6dbc000000 0x6381ffff00000003 0xd18e07fffc000000

def z1037 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0x7feffff3fff70011 0x15ffbfffcfffdc00

def z1038 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e07cf1ffe73e 0xef71c781f3c7ff9c

def z1039 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0xe061ffff00000003 0xe78187fffc000000

def z1040 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff8e000017 0xffbffffffe380000

def z1041 : W := mkw 0x00012490b6fdffc3 0x7c00049242dbf7ff 0x10000000fffffffc 0x0040000003ffffff

def z1042 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff000cffff 0xffbffffffc0033ff

def z1043 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdcffe07cf078e72e 0xff73ff81f3c1e39c

def z1044 : W := mkw 0x10012490fffcfe87 0x7840049243fff3fa 0x10000000fffcfffc 0x0040000003fff3ff

def z1045 : W := mkw 0x212adb6f00000038 0x0084ab6dbc000000 0x6069ffff00000003 0xe181a7fffc000000

def z1046 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff9fff83ff8ffcff 0xfffe7ffe0ffe3ff3

def z1047 : W := mkw 0x2ffedb6f4d24003d 0x00bffb6dbd349000 0xfffffffffff4003f 0xffffffffffffd000

def z1048 : W := mkw 0x1a81b680db81f944 0x646a06da036e07e5 0xff9fff80ff8ffffd 0xfffe7ffe03fe3fff

def z1049 : W := mkw 0x00010c3282109490 0x18000430ca084252 0xa3611c738e709cf7 0x768d8471ce39c273

def z1050 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff83ff80fcdf 0xdffe07fe0ffe03f3

def z1051 : W := mkw 0x012800006d6e0007 0x8004a00001b5b800 0x93fe0000ffff003c 0x3e4ff80003fffc00

def z1052 : W := mkw 0x2a80da6a00000030 0x00aa0369a8000000 0xef81fff000000001 0xdfbe07ffc0000000

def z1053 : W := mkw 0x0ffc92006d6e0007 0x803ff24801b5b800 0xdffee380ffff003c 0xbf7ffb8e03fffc00

def z1054 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdcf1e07cf1f8e73e 0xff73c781f3c7e39c

def z1055 : W := mkw 0x1a81b680db81f944 0x646a06da036e07e5 0xff81ff80ff80ffdd 0xdffe07fe03fe03ff

def z1056 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe000cffff633c 0xbe7ff80033fffd8c

def z1057 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe000fffffffff 0xfe7ff8003fffffff

def z1058 : W := mkw 0x0450605830584622 0x5011418160c16118 0xdc71e07c7078672a 0xef71c781f1c1e19c

def z1059 : W := mkw 0x0bac00006d6e0007 0x802eb00001b5b800 0x9f8e0000ffff003c 0x1e7e380003fffc00

def z1060 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff809815 0x57fe07fe03fe0260

def z1061 : W := mkw 0x2ed2db6f00000038 0x00bb4b6dbc000000 0xeff1ffff00000003 0xffbfc7fffc000000

def z1062 : W := mkw 0x2ffedb6f694a003e 0x80bffb6dbda52800 0xfffffffff1fb002f 0xffffffffffc7ec00

def z1063 : W := mkw 0x0ffc92006d6e0007 0x803ff24801b5b800 0xbffe1f80ffff003d 0x3efff87e03fffc00

def z1064 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0x7f81ff80fe000001 0x15fe07fe03f80000

def z1065 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9fee0000fff7001c 0x1e7fb80003ffdc00

def z1066 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1f9e0000ffff003c 0x187e780003fffc00

def z1067 : W := mkw 0x04516458b258d622 0x5011459162c96358 0xdc71e07cfe78ff3e 0xef71c781f3f9e3fc

def z1068 : W := mkw 0x2ffedb6f00010178 0x04bffb6dbc000405 0xefffffff000f9ff7 0xffbffffffc003e7f

def z1069 : W := mkw 0x2452db6f00000038 0x00914b6dbc000000 0x6c11ffff00000003 0xc9b047fffc000000

def z1070 : W := mkw 0x00036dff9291fff8 0x7c000db7fe4a47ff 0x6001ffff0000ffc3 0xc18007fffc0003ff

def z1071 : W := mkw 0x1a80b6805b807804 0x606a02da016e01e0 0xff80ff807f80f81d 0xdbfe03fe01fe03e0

def z1072 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff000f0023 0xffbffffffc003c00

def z1073 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff88ff3d 0xdffe07fe03fe23fc

def z1074 : W := mkw 0x2a82db6f00000038 0x00aa0b6dbc000000 0xef9fffff00000003 0xffbe7ffffc000000

def z1075 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xef71ffff00000003 0xefbdc7fffc000000

def z1076 : W := mkw 0x057c00006d6e0007 0x8015f00001b5b800 0x90fe0000ffff003c 0x3a43f80003fffc00

def z1077 : W := mkw 0x01292c329634d491 0x5804a4b0ca58d352 0xb3691c73fe74fcff 0x76cda471cff9d3f3

def z1078 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6fffffff00000001 0x9dbffffffc000000

def z1079 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0x6001ffff0000e703 0xc18007fffc00039c

def z1080 : W := mkw 0x2452db6f00000038 0x00914b6dbc000000 0x6c61ffff00000003 0xc5b187fffc000000

def z1081 : W := mkw 0x0a81b6009200d000 0x402a06d802480340 0xff81ff80fe00f81d 0xdffe07fe03f803e0

def z1082 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0380ffff003d 0xfe7ff80e03fffc00

def z1083 : W := mkw 0x04516458b258d6a2 0x5811459162c9635a 0xdc71e07cf078ffee 0xef71c781f3c1e3ff

def z1084 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e07cf078e30c 0xcf71c781f3c1e38c

def z1085 : W := mkw 0x2ffedb6f04240039 0x00bffb6dbc109000 0xefffffff8fff003f 0xffbffffffe3ffc00

def z1086 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdcf7e07cf1fbe72e 0xef73df81f3c7ef9c

def z1087 : W := mkw 0x0450605830584622 0x5011418160c16118 0x5c70e07c70786308 0x8971c381f1c1e18c

def z1088 : W := mkw 0x2ffedb6f2048003a 0x00bffb6dbc812000 0xffffffff7008000b 0xfffffffffdc02000

def z1089 : W := mkw 0x057a497f247d07fb 0x1c15e925fc91f41f 0x007e007f007f07e2 0x2001f801fc01fc1f

def z1090 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0xe081ffff00000003 0xdb8207fffc000000

def z1091 : W := mkw 0x0ffc08226d6e0017 0x803ff02089b5b800 0x9ffe0073ffff003e 0x3e7ff801cffffc00

def z1092 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xfffffffffe740037 0xfffffffffff9d000

def z1093 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc61e07cf070e70e 0xcf718781f3c1c39c

def z1094 : W := mkw 0x0a8000006d6e0007 0x802a000001b5b800 0x9f9e0000ffff003c 0x3e7e780003fffc00

def z1095 : W := mkw 0x01292c329634d491 0x5804a4b0ca58d352 0xff69fc73fe749cf7 0x77fda7f1cff9d273

def z1096 : W := mkw 0x0002018500812948 0x24000806140204a5 0x009e038f018fffff 0x3002780e3c063fff

def z1097 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xfffffffffe78002f 0xfffffffffff9e000

def z1098 : W := mkw 0x0ed2d34d00000028 0x003b4b4d34000000 0xefffffff00000003 0xffbffffffc000000

def z1099 : W := mkw 0x10012490db90fc84 0x78400492436e43f2 0x10000000ff80fcdc 0x0040000003fe03f3

def z1100 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x1ffe0000ffff0018 0x1c7ff80003fffc00

def z1101 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3611c738e709ce7 0x668d8471ce39c273

def z1102 : W := mkw 0x2ffcda6a6d6e0037 0x80bff369a9b5b800 0xfffffc73ffff003f 0x7ffffff1cffffc00

def z1103 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0003ffff04fe 0x3e7ff8000ffffc13

def z1104 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff99ff8fff8cffff 0xfffe67fe3ffe33ff

def z1105 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c7f8e74fff7 0xf68da471fe39d3ff

def z1106 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23691c730e749cf3 0x708da471cc39d273

def z1107 : W := mkw 0x057c00006d6e0007 0x8015f00001b5b800 0x9c7e0000ffff003c 0x2e71f80003fffc00

def z1108 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c71e07cf078672a 0xad71c781f3c1e19c

def z1109 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xef69fc738e749cf7 0xffbda7f1ce39d273

def z1110 : W := mkw 0x0ffc40486d6e0027 0x803ff10121b5b800 0x9ffe007cffff003e 0x3e7ff801f3fffc00

def z1111 : W := mkw 0x2ffedb6f00010178 0x04bffb6dbc000405 0xefffffff000007c3 0xffbffffffc00001f

def z1112 : W := mkw 0x2ffedb6f042400b9 0x08bffb6dbc109002 0xefffffff000400c3 0xffbffffffc001003

def z1113 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xeff7fffc00000001 0xdfbfdffff0000000

def z1114 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x63ffffff00000003 0xf18ffffffc000000

def z1115 : W := mkw 0x0ffc92006d6e0007 0x803ff24801b5b800 0xfffffc00ffff003c 0x3ffffff003fffc00

def z1116 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc79e07ff07ce7ee 0xef71e781ffc1f39f

def z1117 : W := mkw 0x2baedb6f4d26003d 0x80aebb6dbd349800 0x638fffff0f870013 0xd18e3ffffc3e1c00

def z1118 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff018fe73f 0xffbffffffc063f9c

def z1119 : W := mkw 0x01289a2200000010 0x0004a26888000000 0xe369fff300000003 0xf78da7ffcc000000

def z1120 : W := mkw 0x2456db6f00000038 0x00915b6dbc000000 0x6017ffff00000003 0xc1805ffffc000000

def z1121 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff89ff83ff84f8dd 0xdffe27fe0ffe13e3

def z1122 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23691c738e749cd3 0x548da471ce39d273

def z1123 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xff81ff80ff801811 0xdffe07fe03fe0060

def z1124 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0xeffffff000000001 0xffbfffffc0000000

def z1125 : W := mkw 0x2ffedb6f04260039 0x80bffb6dbc109800 0xefffffff00070003 0xffbffffffc001c00

def z1126 : W := mkw 0x1a81b690db90fc04 0x706a06da436e43f0 0xfff1fffcfff8ff3f 0xffffc7fff3ffe3fc

def z1127 : W := mkw 0x2ffedb6f694a003e 0x80bffb6dbda52800 0xffffffff718f003f 0xfffffffffdc63c00

def z1128 : W := mkw 0x0001041082109400 0x1000041042084250 0xa3691c738e749cf7 0x768da471ce39d273

def z1129 : W := mkw 0x2ffedb6f246e003b 0x80bffb6dbc91b800 0xefffffff8e7f0037 0xffbffffffe39fc00

def z1130 : W := mkw 0x2ed6db6f00000038 0x00bb5b6dbc000000 0x6c97fffc00000000 0x89b25ffff0000000

def z1131 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3ef1c738ff79cf7 0x768fbc71ce3fde73

def z1132 : W := mkw 0x212adb6f00000038 0x0084ab6dbc000000 0x6309ffff00000003 0xd18c27fffc000000

def z1133 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefe1ffff00000003 0xdfbf87fffc000000

def z1134 : W := mkw 0x04516058b058c622 0x5011458162c16318 0x5c61e07cf0706300 0x85718781f3c1c18c

def z1135 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0000ffff843e 0x7e7ff80003fffe10

def z1136 : W := mkw 0x2ffedb6f2048023a 0x00bffb6dbc812008 0xefffffff00080303 0xffbffffffc00200c

def z1137 : W := mkw 0x0002018500812948 0x24000806140204a5 0x009e038f018fffeb 0xe802780e3c063fff

def z1138 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0xdfffe000ffff003c 0xff7fff8003fffc00

def z1139 : W := mkw 0x0ffcd24800000020 0x003ff34920000000 0xeffffffc00000003 0xffbffffff0000000

def z1140 : W := mkw 0x1ed12490fbd8fe06 0x707b449243ef63f8 0x9ff00000fff8ff3c 0x3e7fc00003ffe3fc

def z1141 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0003ffff18fd 0x3e7ff8000ffffc63

def z1142 : W := mkw 0x0002018500812948 0x24000806140204a5 0x009e038f018ffff3 0xf002780e3c063fff

def z1143 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0xefe9fff300000003 0xffbfa7ffcc000000

def z1144 : W := mkw 0x1a81b690db90fc04 0x706a06da436e43f0 0xffe1fff0fff0f81d 0xdfff87ffc3ffc3e0

def z1145 : W := mkw 0x2baedb6f00000038 0x00aebb6dbc000000 0xef8fffff00000003 0xdfbe3ffffc000000

def z1146 : W := mkw 0x2ffedb6f00010178 0x04bffb6dbc000405 0xefffffff000fe7ef 0xffbffffffc003f9f

def z1147 : W := mkw 0x2002db6f00000038 0x00800b6dbc000000 0xe09fffff018f003f 0xfb827ffffc063c00

def z1148 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f81ff807f80f819 0xd9fe07fe01fe03e0

def z1149 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0xbfff1c00ffff003d 0x7efffc7003fffc00

def z1150 : W := mkw 0x0bac00006d6e0007 0x802eb00001b5b800 0x939e0000ffff003c 0x3a4e780003fffc00

def z1151 : W := mkw 0x10012490dfb5fdc5 0x7c400492437ed7f7 0x10000000fffffffc 0x0040000003ffffff

def z1152 : W := mkw 0x2ffc486a6d6e0037 0x80bff121a9b5b800 0x9ffe0070ffff003c 0x3e7ff801c3fffc00

def z1153 : W := mkw 0x257adb6f00000038 0x0095eb6dbc000000 0xef79ffff00000003 0xffbde7fffc000000

def z1154 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23681c738e749cf7 0x308da071ce39d273

def z1155 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ff60000fffb002c 0x2e7fd80003ffec00

def z1156 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff0008002f 0xffbffffffc002000

def z1157 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0xffe1ff80fff0f83d 0xffff87fe03ffc3e0

def z1158 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0x6fe7fff000000000 0x05bf9fffc0000000

def z1159 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0000fff70010 0x3e7ff80003ffdc00

def z1160 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe000cffff073e 0x3e7ff80033fffc1c

def z1161 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f01ff80ff80f81d 0xc5fc07fe03fe03e0

def z1162 : W := mkw 0x2ed6db6f00000038 0x00bb5b6dbc000000 0x6c01ffff00000003 0xc1b007fffc000000

def z1163 : W := mkw 0x2ffedb6f00000038 0x00bffb6dbc000000 0xefffffff00009817 0xffbffffffc000260

def z1164 : W := mkw 0x2ffcd2486d6e0027 0x80bff34921b5b800 0xdffee000ffff003c 0x3f7ffb8003fffc00

def z1165 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c738fff9cff 0x768da471ce3ffe73

def z1166 : W := mkw 0x1a81b680db80f804 0x606a06da036e03e0 0x7f81ff80ff80f809 0xcdfe07fe03fe03e0

def z1167 : W := mkw 0x257edb6f00000038 0x0095fb6dbc000000 0xe0ffffff00000003 0xfb83fffffc000000

def z1168 : W := mkw 0x0baa9b2700000018 0x002eaa6c9c000000 0xefffffff00000003 0xffbffffffc000000

def z1169 : W := mkw 0x0450605830584622 0x5011418160c16118 0xdc70e07c7078e72e 0xeb71c381f1c1e39c

def z1170 : W := mkw 0x1a81b600db00d004 0x406a06d8036c0340 0xff81ff80fe00e00d 0xdffe07fe03f80380

def z1171 : W := mkw 0x04516058b058c622 0x5011458162c16318 0xdc71e07cf070e702 0xef71c781f3c1c39c

def z1172 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa37f1c738e7f9cf7 0x768dfc71ce39fe73

def z1173 : W := mkw 0x2ffedb6f4902003c 0x80bffb6dbd240800 0xefffffff01830003 0xffbffffffc060c00

def z1174 : W := mkw 0x2ed6d34d00000028 0x00bb5b4d34000000 0xeff7fffc00000003 0xffbfdffff0000000

def z1175 : W := mkw 0x0ffc00006d6e0007 0x803ff00001b5b800 0x9ffe0000ffff983d 0x7e7ff80003fffe60

def z1176 : W := mkw 0x1001b6809280f800 0x604006da024a03e0 0xff01ff80fe00f81d 0xdffc07fe03f803e0

def z1177 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0x23691c738e749cf5 0x148da471ce39d273

def z1178 : W := mkw 0x1a85b680db82f804 0xe06a16da036e0be0 0xff87ff80ff83f81d 0xdffe1ffe03fe0fe0

def z1179 : W := mkw 0x2ffcda6a00000030 0x00bff369a8000000 0x6f61fff000000001 0xc5bd87ffc0000000

def z1180 : W := mkw 0x0450d24800000020 0x0011434920000000 0xec71fffc00000003 0xefb1c7fff0000000

def z1181 : W := mkw 0x0bac00004d260005 0x802eb00001349800 0x9fee0000fff7003c 0x3e7fb80003ffdc00

def z1182 : W := mkw 0x01290c3286349491 0x1804a430ca18d252 0xa3691c738e7498d5 0x568da471ce39d263

def z1183 : W := mkw 0x2ffedb6f246e003b 0x80bffb6dbc91b800 0xefffffff00700003 0xffbffffffc01c000

def z1184 : W := mkw 0x01292c329634d491 0x5804a4b0ca58d352 0xff79fc7ffe7cffff 0xfffde7f1fff9f3ff

def z1185 : W := mkw 0x0a8400006d6e0007 0x802a100001b5b800 0x10860000ffff003c 0x0042180003fffc00

def z1186 : W := mkw 0x0002018500812948 0x24000806140204a5 0x839e038f8f8fffff 0xfe0e780e3e3e3fff

def z1187 : W := mkw 0x2ffedb6f6d6e003f 0x80bffb6dbdb5b800 0xffffffff7f8f001b 0xfffffffffdfe3c00

def z1188 : W := mkw 0x01280c3206341491 0x1804a030c818d052 0xa3691c730e741cf3 0x768da471cc39d073

def z1189 : W := mkw 0x0002018500812948 0x24000806140204a5 0x80ff03ff018fffff 0xfe03fc0ffc063fff

def z1190 : W := mkw 0x0ba89a224d240015 0x002ea26889349000 0xffe9fff3fff4003f 0xffffa7ffcfffd000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z5,z10,z6]),(1,[z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z12,z6]),(0,[z1,z2,z3,z13,z4,z5,z6]),(0,[z1,z2,z3,z14,z4,z15,z6]),(0,[z1,z2,z3,z4,z5,z16,z16])],[(0,[z17,z18,z2,z3,z4,z5,z6]),(0,[z19,z1,z20,z3,z4,z5,z6]),(0,[z1,z21,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z22,z5,z6]),(0,[z1,z2,z3,z4,z5,z23,z24]),(0,[z25,z1,z2,z3,z26,z5,z6]),(0,[z1,z2,z3,z4,z5,z27,z24]),(0,[z1,z2,z3,z14,z4,z28,z6])],[(0,[z1,z2,z3,z4,z5,z23,z10]),(0,[z1,z20,z2,z29,z4,z5,z6]),(0,[z1,z30,z2,z3,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z23]),(0,[z1,z2,z3,z14,z4,z5,z24]),(0,[z1,z2,z3,z32,z4,z5,z6])],[(0,[z33,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z35]),(0,[z1,z2,z3,z4,z36,z5,z16])],[(0,[z1,z2,z3,z4,z37,z5,z16]),(0,[z1,z2,z3,z4,z5,z16,z35]),(0,[z1,z2,z38,z29,z4,z5,z6]),(0,[z1,z2,z3,z26,z4,z5,z24]),(0,[z1,z2,z39,z3,z4,z5,z6]),(0,[z40,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z41,z4,z5,z6]),(0,[z1,z42,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z44,z5,z6]),(0,[z1,z2,z3,z45,z4,z5,z6]),(0,[z1,z2,z46,z3,z4,z5,z6])],[(1,[z1,z2,z3,z47,z5,z6]),(0,[z48,z1,z2,z3,z4,z5,z6]),(1,[z1,z49,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z50]),(0,[z1,z2,z3,z4,z5,z51,z6]),(0,[z1,z2,z52,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z53,z24])],[(0,[z17,z1,z54,z3,z4,z5,z6]),(0,[z9,z1,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z56,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z57,z6]),(1,[z1,z2,z3,z4,z5,z58]),(0,[z59,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z60,z6]),(0,[z61,z1,z2,z3,z4,z5,z6]),(0,[z1,z62,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z63,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z24]),(1,[z65,z2,z3,z4,z5,z10]),(0,[z66,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z67,z5]),(0,[z1,z31,z2,z3,z4,z5,z24]),(1,[z1,z2,z68,z44,z5,z6])],[(1,[z1,z2,z69,z4,z5,z6]),(0,[z1,z2,z3,z70,z4,z5,z6]),(0,[z71,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z72,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z73,z6])],[(0,[z1,z74,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z75])],[(1,[z76,z2,z3,z4,z77,z6]),(0,[z1,z2,z3,z4,z78,z5,z6]),(0,[z1,z2,z3,z4,z5,z79,z6]),(0,[z1,z2,z68,z3,z44,z5,z6]),(1,[z1,z2,z3,z80,z5,z24]),(0,[z1,z2,z3,z81,z4,z5,z82])],[(0,[z1,z2,z3,z4,z77,z15,z6]),(0,[z1,z2,z3,z4,z28,z37,z6]),(0,[z2,z3,z4,z5,z10,z6,z35]),(1,[z1,z2,z3,z41,z5,z6]),(0,[z1,z2,z3,z4,z5,z83,z6]),(0,[z1,z2,z3,z4,z5,z24,z84]),(0,[z1,z2,z3,z5,z16,z6,z24])],[(0,[z1,z2,z3,z4,z85,z5,z6]),(0,[z1,z2,z3,z4,z5,z86,z6]),(0,[z1,z2,z3,z14,z4,z5,z16])]],
   [[(0,[z1,z2,z3,z36,z5,z6,z24]),(0,[z87,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z38,z3,z4,z88,z6]),(0,[z1,z2,z3,z4,z5,z89,z6])],[(0,[z1,z2,z3,z26,z4,z5,z16]),(0,[z90,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z14,z4,z5,z91])],[(0,[z92,z1,z2,z93,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z23,z35]),(0,[z1,z2,z3,z4,z5,z27,z35]),(0,[z1,z2,z94,z3,z4,z5,z6])],[(0,[z1,z2,z68,z4,z44,z5,z6])],[(0,[z19,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z95,z4,z5,z6])],[(0,[z96,z2,z3,z63,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z97,z6]),(0,[z98,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z26,z4,z5,z6]),(0,[z99,z1,z2,z3,z4,z5,z24])],[(0,[z1,z2,z3,z4,z5,z100,z6]),(0,[z64,z1,z2,z3,z4,z5,z16]),(0,[z1,z31,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z101,z4,z5,z6]),(1,[z1,z2,z3,z4,z102,z5]),(0,[z1,z2,z3,z4,z5,z103,z6]),(0,[z1,z2,z3,z4,z104,z5,z6])],[]],
   [[(1,[z1,z2,z3,z4,z5,z105]),(0,[z25,z1,z2,z3,z106,z5,z6]),(0,[z1,z2,z3,z4,z107,z5,z6]),(0,[z108,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z109]),(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z111,z6]),(0,[z1,z112,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z82,z6])],[(0,[z1,z2,z3,z4,z113,z5,z6]),(0,[z1,z2,z3,z4,z5,z114,z6]),(0,[z115,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z116,z4,z5,z6])],[(0,[z33,z1,z117,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z118,z5,z6]),(0,[z1,z2,z3,z4,z119,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z16])],[(0,[z1,z20,z121,z3,z4,z5,z6]),(0,[z1,z122,z2,z3,z4,z5,z6]),(0,[z123,z1,z2,z3,z4,z124,z6]),(0,[z1,z2,z125,z3,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z50]),(0,[z1,z2,z3,z26,z4,z5,z126]),(0,[z1,z2,z127,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z128,z6]),(0,[z1,z2,z129,z3,z4,z5,z6]),(0,[z130,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z26,z5,z24]),(0,[z1,z2,z131,z3,z4,z5,z6])],[(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z133])],[(0,[z1,z2,z134,z3,z4,z5,z6]),(0,[z135,z1,z3,z4,z5,z23,z6])]],
   [[(0,[z33,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z136,z3,z4,z5,z6]),(0,[z137,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z138,z4,z5,z6]),(1,[z1,z2,z46,z4,z5,z139]),(0,[z1,z2,z3,z5,z15,z6,z24])],[(0,[z1,z121,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z140,z5,z6]),(0,[z141,z1,z49,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z142,z37,z6]),(0,[z19,z1,z2,z3,z4,z5,z16]),(0,[z123,z1,z3,z4,z5,z124,z6]),(0,[z1,z2,z3,z4,z143,z5,z6])],[(0,[z144,z1,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z77,z6]),(0,[z1,z2,z3,z4,z145,z5,z6]),(0,[z1,z2,z3,z4,z146,z5,z6]),(0,[z1,z2,z46,z3,z4,z5,z27]),(0,[z1,z147,z2,z3,z4,z5,z6])],[(0,[z1,z148,z2,z3,z4,z5,z6]),(0,[z1,z2,z149,z3,z4,z5,z6]),(1,[z150,z1,z2,z4,z88,z6]),(0,[z151,z1,z2,z3,z4,z5,z6])],[(0,[z1,z152,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z153,z4,z5,z6]),(0,[z1,z2,z3,z4,z154,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z155])],[(0,[z1,z2,z3,z4,z5,z156,z6]),(0,[z1,z2,z3,z4,z157,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z67,z5,z124]),(0,[z1,z2,z3,z4,z5,z159,z6]),(0,[z135,z1,z2,z3,z81,z4,z5])],[(0,[z141,z1,z2,z72,z4,z5,z6]),(0,[z1,z160,z3,z29,z4,z5,z6]),(0,[z161,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z54,z3,z4,z5,z24]),(0,[z1,z2,z162,z3,z4,z5,z6])]],
   [[(0,[z17,z1,z2,z69,z4,z5,z6]),(0,[z25,z1,z2,z3,z44,z5,z6])],[(0,[z43,z1,z2,z93,z4,z5,z6]),(0,[z76,z2,z3,z4,z5,z77,z6]),(0,[z1,z2,z3,z163,z4,z5,z6])],[(0,[z18,z1,z2,z3,z4,z5,z24]),(0,[z164,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z165,z6]),(0,[z166,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z167]),(0,[z1,z2,z3,z168,z4,z5,z24]),(1,[z1,z2,z3,z169,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z170]),(0,[z1,z2,z3,z4,z171,z5,z172])],[(0,[z1,z2,z3,z80,z5,z6,z24]),(0,[z1,z2,z3,z4,z5,z173,z6])],[(0,[z1,z2,z3,z4,z5,z10,z6]),(0,[z135,z1,z31,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z174,z6]),(0,[z1,z2,z3,z4,z5,z16,z173])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z16]),(0,[z175,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z176,z4,z5]),(0,[z1,z177,z2,z3,z4,z5,z6])],[(0,[z178,z1,z2,z3,z4,z5,z6]),(0,[z1,z121,z2,z3,z4,z5,z16]),(0,[z1,z179,z3,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z180]),(0,[z90,z1,z2,z3,z4,z5,z27]),(0,[z181,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z182,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z183]),(0,[z1,z2,z3,z4,z184,z5,z6]),(1,[z1,z2,z3,z4,z5,z185]),(0,[z1,z2,z3,z81,z4,z37,z6]),(1,[z1,z2,z3,z4,z5,z186]),(1,[z1,z2,z3,z4,z5,z187]),(0,[z1,z2,z3,z4,z5,z6,z188]),(0,[z1,z2,z3,z4,z5,z6,z24])]],
   [[(1,[z1,z2,z3,z4,z189,z6]),(0,[z1,z2,z3,z4,z190,z5,z6]),(0,[z1,z2,z191,z3,z4,z5,z6])],[(0,[z1,z2,z3,z63,z4,z5,z100]),(0,[z65,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z5,z10,z192,z6]),(0,[z1,z20,z2,z160,z4,z5,z6]),(1,[z123,z1,z3,z4,z124,z6]),(0,[z1,z2,z193,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z194,z5,z6])],[(0,[z195,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z196,z5,z6]),(0,[z65,z1,z2,z3,z4,z5,z10]),(0,[z197,z1,z2,z3,z36,z5,z6]),(0,[z1,z2,z3,z198,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z199,z6]),(0,[z1,z2,z3,z169,z4,z5,z24])],[(0,[z1,z2,z3,z4,z200,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z76,z1,z2,z3,z4,z37,z6]),(0,[z1,z2,z38,z160,z4,z5,z6]),(0,[z1,z2,z3,z201,z4,z5,z6]),(0,[z1,z2,z68,z3,z4,z5,z187]),(0,[z1,z2,z46,z3,z4,z171,z5])],[(0,[z1,z2,z54,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z202,z6]),(1,[z1,z122,z3,z36,z5,z6]),(1,[z1,z2,z3,z106,z5,z24]),(0,[z203,z1,z2,z3,z4,z5,z6])],[(0,[z33,z1,z2,z3,z4,z5,z204]),(0,[z1,z2,z3,z205,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z206,z6]),(0,[z1,z2,z3,z207,z4,z5,z6]),(0,[z1,z2,z3,z4,z208,z5,z6])],[(0,[z1,z2,z3,z209,z4,z5,z6]),(0,[z197,z1,z3,z106,z4,z5,z6])],[(0,[z1,z20,z54,z3,z4,z5,z6]),(0,[z18,z1,z2,z3,z4,z5,z16]),(1,[z1,z2,z3,z4,z210,z6]),(0,[z1,z2,z3,z4,z5,z6,z211]),(0,[z212,z1,z2,z3,z4,z5,z6]),(0,[z213,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z168,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z24,z172])]],
   [[(0,[z1,z214,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z215,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z216,z6]),(0,[z1,z2,z3,z106,z4,z5,z186]),(0,[z1,z2,z3,z4,z5,z15,z6]),(0,[z217,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z172])],[(0,[z2,z3,z63,z4,z218,z5,z6]),(0,[z219,z1,z2,z3,z4,z5,z6]),(0,[z220,z1,z2,z3,z4,z5,z6]),(0,[z221,z1,z2,z3,z4,z5,z16])],[(1,[z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z200,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z222]),(0,[z1,z2,z3,z4,z37,z5,z24]),(1,[z19,z1,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z223]),(0,[z1,z2,z224,z3,z4,z5,z6]),(0,[z1,z2,z225,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z226]),(1,[z1,z2,z3,z4,z171,z82])],[(0,[z1,z2,z3,z227,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z228,z6]),(0,[z229,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z230,z5,z6]),(0,[z1,z2,z3,z14,z4,z5,z231]),(0,[z1,z2,z3,z80,z81,z4,z6])],[(0,[z232,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z233,z6]),(0,[z234,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z235,z5,z6])],[(0,[z1,z2,z3,z4,z44,z5,z24])],[(0,[z236,z1,z2,z3,z4,z5,z6]),(0,[z65,z1,z2,z3,z4,z5,z16]),(0,[z1,z237,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z238]),(0,[z1,z2,z68,z3,z4,z5,z226]),(0,[z1,z2,z239,z3,z4,z5,z6])],[(0,[z240,z1,z2,z3,z4,z5,z6]),(0,[z19,z1,z2,z160,z4,z5,z6]),(0,[z241,z1,z2,z3,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z171,z5]),(0,[z90,z1,z2,z3,z4,z171,z5])]],
   [[(0,[z33,z1,z148,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z35]),(0,[z1,z2,z3,z4,z5,z6,z242]),(0,[z1,z2,z46,z3,z4,z5,z24])],[(0,[z1,z2,z3,z243,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z244,z6])],[(0,[z1,z2,z3,z4,z5,z245,z6]),(0,[z1,z2,z3,z4,z37,z88,z6]),(0,[z65,z1,z2,z3,z4,z5,z35]),(0,[z1,z2,z3,z4,z246,z5,z6]),(0,[z1,z2,z3,z247,z4,z5,z6]),(0,[z1,z2,z3,z4,z248,z5,z6]),(0,[z1,z2,z3,z4,z171,z5,z82])],[(0,[z249,z1,z2,z3,z4,z5,z6]),(0,[z1,z250,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z251,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z252]),(0,[z1,z2,z3,z4,z11,z5,z6]),(0,[z19,z1,z3,z29,z4,z5,z6]),(0,[z1,z2,z3,z253,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z254,z6]),(0,[z1,z2,z3,z106,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z255]),(0,[z256,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z63,z4,z5,z24]),(1,[z1,z2,z3,z44,z5,z24]),(1,[z1,z39,z3,z4,z5,z6]),(0,[z1,z2,z257,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z258,z6])],[(0,[z1,z2,z3,z259,z4,z5,z6]),(0,[z1,z260,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z37,z6]),(0,[z1,z2,z3,z261,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z262,z6]),(0,[z1,z2,z263,z3,z4,z5,z6])],[(0,[z33,z1,z2,z3,z264,z5,z6]),(0,[z1,z2,z265,z3,z4,z5,z6]),(0,[z1,z2,z3,z80,z4,z5,z266]),(0,[z1,z2,z3,z81,z267,z5,z6])],[(0,[z268,z1,z2,z3,z4,z5,z6]),(1,[z96,z1,z2,z3,z5,z24]),(0,[z269,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z26,z4,z5,z188]),(0,[z1,z2,z3,z4,z267,z5,z6])]],
   [[(0,[z1,z2,z160,z93,z4,z5,z6]),(0,[z1,z2,z270,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z10,z139]),(0,[z271,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z75])],[(0,[z17,z1,z2,z3,z272,z5,z6]),(0,[z19,z1,z2,z3,z4,z273,z6]),(0,[z1,z2,z3,z274,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z275,z6]),(0,[z276,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z80,z4,z82,z6])],[(0,[z1,z2,z3,z26,z218,z5,z6]),(0,[z277,z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z44,z5,z16])],[(0,[z1,z278,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z4,z5,z6]),(0,[z279,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z84]),(0,[z280,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z281]),(0,[z90,z1,z2,z3,z4,z5,z24])],[(0,[z1,z2,z3,z4,z5,z192,z6]),(0,[z1,z2,z3,z282,z4,z5,z6]),(0,[z1,z2,z3,z283,z4,z5,z6]),(0,[z1,z2,z284,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z285,z5,z6]),(0,[z1,z2,z46,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z6,z286]),(0,[z1,z2,z3,z14,z81,z4,z6])],[(0,[z1,z2,z3,z63,z36,z5,z6]),(0,[z287,z1,z2,z3,z4,z5,z6]),(1,[z1,z20,z160,z4,z5,z6]),(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z289,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z267,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z290]),(0,[z1,z2,z3,z4,z67,z5,z6]),(0,[z1,z2,z291,z3,z4,z5,z6])]],
   [[(0,[z1,z121,z3,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z82])],[(0,[z1,z292,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z293]),(0,[z141,z1,z2,z3,z5,z6,z24]),(0,[z1,z2,z3,z63,z4,z5,z16]),(0,[z277,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z294,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z295,z6]),(0,[z296,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z297,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z266])],[(0,[z1,z2,z3,z4,z5,z298,z6]),(0,[z1,z2,z93,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z299,z6]),(0,[z19,z1,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z300,z4,z5,z6]),(0,[z301,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z302,z6])],[(0,[z1,z2,z3,z303,z4,z5,z6]),(1,[z141,z2,z3,z218,z5,z6]),(1,[z1,z2,z3,z5,z192,z6]),(0,[z1,z2,z3,z4,z28,z5,z6]),(0,[z304,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z82,z24]),(0,[z1,z2,z3,z4,z5,z305,z6])],[(0,[z1,z2,z160,z3,z4,z5,z6]),(0,[z306,z1,z2,z3,z4,z5,z6])],[],[(0,[z307,z1,z2,z3,z4,z5,z6]),(0,[z308,z1,z2,z3,z4,z5,z6]),(0,[z309,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z35,z50]),(0,[z65,z1,z2,z3,z4,z310,z6]),(0,[z1,z122,z2,z3,z4,z5,z24])]],
   [[(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z17,z1,z2,z3,z200,z5,z6]),(0,[z1,z2,z3,z4,z5,z311,z6]),(0,[z1,z312,z2,z3,z4,z5,z6])],[(0,[z1,z2,z313,z3,z4,z5,z6]),(0,[z1,z2,z3,z314,z4,z5,z6]),(0,[z315,z1,z2,z3,z4,z5,z6]),(0,[z90,z1,z2,z3,z4,z5,z16])],[(0,[z1,z2,z3,z4,z5,z204,z6]),(0,[z316,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z317,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z77,z88,z6]),(0,[z318,z1,z2,z3,z4,z5,z6]),(0,[z319,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z320,z5,z6]),(0,[z1,z2,z3,z4,z5,z321,z6]),(0,[z1,z2,z3,z4,z322,z5,z6])],[(0,[z1,z2,z3,z323,z4,z5,z6]),(0,[z1,z2,z3,z324,z4,z5,z6]),(0,[z19,z1,z2,z3,z4,z11,z6])],[(0,[z1,z2,z3,z325,z4,z5,z6]),(0,[z1,z2,z3,z4,z326,z5,z6]),(0,[z1,z2,z3,z4,z5,z327,z6])],[(0,[z17,z2,z54,z3,z4,z5,z6]),(0,[z328,z1,z2,z3,z4,z5,z6]),(1,[z1,z260,z3,z4,z5,z6]),(0,[z1,z2,z3,z329,z4,z5,z6]),(0,[z25,z1,z2,z3,z5,z15,z6])],[(0,[z1,z31,z2,z3,z41,z5,z6]),(0,[z150,z1,z39,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z330,z6]),(0,[z1,z2,z3,z4,z5,z310,z6]),(0,[z1,z2,z3,z331,z4,z5,z6]),(0,[z1,z2,z3,z332,z4,z5,z6])],[(0,[z333,z1,z2,z3,z4,z5,z6]),(0,[z1,z122,z2,z3,z36,z5,z6]),(1,[z1,z31,z3,z4,z5,z50]),(0,[z334,z1,z2,z3,z4,z5,z6])],[(0,[z92,z1,z2,z3,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z85,z6]),(1,[z1,z2,z3,z4,z5,z100]),(0,[z1,z2,z3,z4,z5,z335,z6]),(0,[z1,z2,z3,z336,z4,z5,z6]),(0,[z1,z2,z337,z3,z4,z5,z6]),(0,[z1,z338,z2,z3,z4,z5,z6]),(0,[z1,z2,z46,z3,z339,z5,z6])],[(0,[z1,z2,z3,z4,z340,z5,z6])],[(0,[z1,z121,z3,z4,z36,z5,z6]),(0,[z1,z2,z3,z4,z341,z5,z6]),(0,[z1,z122,z2,z3,z4,z5,z16]),(1,[z1,z2,z3,z326,z5,z6])],[(0,[z1,z2,z3,z342,z4,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z1,z344,z2,z3,z4,z5,z6]),(0,[z1,z2,z345,z3,z4,z5,z6])],[(0,[z141,z2,z3,z4,z218,z5,z6]),(0,[z1,z2,z3,z4,z5,z346,z6]),(0,[z347,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z348,z5,z6])],[(1,[z64,z2,z3,z4,z37,z6]),(0,[z1,z2,z3,z4,z142,z5,z6]),(0,[z1,z2,z3,z349,z4,z5,z6]),(0,[z90,z1,z2,z4,z5,z27,z6])]],
   [[(0,[z96,z1,z2,z3,z5,z6,z24]),(0,[z1,z2,z3,z106,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z350,z6])],[(0,[z1,z2,z3,z4,z37,z124,z6]),(0,[z1,z2,z3,z4,z5,z6,z351]),(0,[z1,z2,z3,z4,z352,z5,z6]),(0,[z1,z2,z3,z4,z5,z353,z6]),(0,[z1,z2,z3,z4,z5,z124,z6]),(0,[z354,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z355,z6]),(0,[z1,z2,z3,z4,z5,z356,z6]),(0,[z1,z2,z3,z4,z5,z357,z6])],[(0,[z141,z96,z2,z3,z4,z5,z6]),(0,[z1,z358,z2,z3,z4,z5,z6]),(0,[z197,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z359,z6]),(0,[z1,z2,z3,z4,z5,z24,z360])],[(0,[z361,z1,z2,z3,z4,z5,z6]),(0,[z362,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z363,z6]),(1,[z1,z2,z3,z146,z5,z6])],[],[(1,[z1,z2,z3,z272,z5,z6]),(0,[z1,z3,z106,z4,z36,z5,z6]),(1,[z1,z2,z3,z4,z5,z364])],[(0,[z365,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z366,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z367]),(0,[z1,z2,z3,z368,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z369,z6])],[(0,[z1,z2,z3,z44,z218,z5,z6]),(0,[z1,z2,z3,z370,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z371,z6]),(0,[z1,z2,z3,z372,z4,z5,z6])],[(0,[z373,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z374,z6]),(0,[z1,z2,z3,z4,z5,z375,z6]),(0,[z1,z2,z3,z80,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z376]),(0,[z1,z2,z377,z3,z4,z5,z6])],[(0,[z1,z2,z117,z3,z4,z5,z6]),(0,[z378,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z379,z3,z4,z5,z6]),(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z381]),(0,[z1,z2,z3,z4,z5,z15,z24]),(0,[z382,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z383,z5,z6]),(0,[z1,z2,z3,z384,z4,z5,z6]),(0,[z1,z2,z385,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z386,z5,z6]),(0,[z1,z2,z3,z4,z387,z5,z6]),(0,[z388,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z172]),(0,[z1,z2,z3,z4,z389,z5,z6])],[(1,[z96,z2,z3,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z390,z6]),(0,[z1,z2,z3,z81,z4,z5,z6])],[(0,[z391,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z392,z4,z5,z6]),(0,[z393,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z394]),(0,[z1,z2,z3,z339,z4,z5,z6]),(0,[z1,z2,z3,z4,z182,z5,z16]),(0,[z1,z2,z3,z4,z82,z6,z172])],[(0,[z1,z2,z3,z4,z5,z395,z6])]],
   [[(0,[z1,z2,z3,z4,z36,z5,z6]),(0,[z197,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z6,z396]),(0,[z397,z1,z2,z3,z4,z5,z6])],[(0,[z141,z1,z260,z3,z4,z5,z6]),(0,[z1,z2,z3,z398,z4,z5,z6]),(0,[z76,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z68,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z194,z5,z16]),(0,[z25,z1,z2,z3,z168,z5,z6])],[(0,[z1,z2,z3,z4,z399,z5,z6]),(0,[z1,z2,z3,z4,z400,z5,z6]),(0,[z1,z2,z3,z4,z5,z401,z6]),(0,[z1,z2,z3,z4,z5,z10,z50]),(0,[z1,z2,z3,z402,z4,z5,z6]),(1,[z1,z2,z3,z5,z15,z24])],[(0,[z403,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z404]),(0,[z1,z405,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z406,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z407]),(0,[z1,z2,z3,z4,z408,z5,z6]),(0,[z1,z409,z2,z3,z4,z5,z6])],[(0,[z410,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z244,z24]),(1,[z1,z2,z3,z4,z244,z6])],[(0,[z411,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z412,z5,z6]),(1,[z1,z2,z413,z4,z5,z6]),(0,[z414,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z106,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z415,z6])],[(0,[z1,z2,z3,z416,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z417,z6]),(0,[z65,z2,z3,z4,z5,z10,z6]),(0,[z418,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z92,z1,z2,z34,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z185]),(0,[z1,z2,z3,z419,z4,z5,z6]),(0,[z1,z2,z3,z420,z4,z5,z6]),(0,[z1,z2,z421,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z15,z16]),(0,[z1,z2,z3,z4,z5,z16,z422])],[(0,[z197,z1,z121,z3,z4,z5,z6]),(0,[z423,z1,z2,z3,z4,z5,z6]),(0,[z1,z179,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z194,z142,z6]),(0,[z1,z2,z68,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z171,z82,z6])],[(0,[z1,z2,z3,z4,z77,z124,z6]),(0,[z1,z2,z3,z26,z5,z6,z24]),(0,[z1,z424,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z425,z6])],[(0,[z18,z1,z121,z3,z4,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z290]),(0,[z1,z2,z3,z426,z4,z5,z6]),(0,[z1,z3,z4,z5,z23,z6,z50]),(0,[z1,z2,z3,z4,z5,z27,z6]),(0,[z1,z2,z3,z4,z427,z5,z6])],[(0,[z1,z2,z3,z4,z428,z5,z6]),(0,[z1,z429,z2,z3,z4,z5,z6]),(0,[z430,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z374,z5,z6]),(0,[z1,z2,z3,z431,z4,z5,z6]),(1,[z1,z2,z38,z4,z194,z6]),(0,[z1,z432,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z433,z6]),(1,[z1,z2,z3,z4,z5,z91]),(0,[z1,z2,z3,z4,z5,z434,z6])],[(0,[z435,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z436,z6]),(0,[z437,z1,z2,z3,z4,z5,z6]),(0,[z150,z1,z2,z3,z4,z194,z6]),(0,[z1,z2,z3,z4,z5,z88,z6])],[(0,[z1,z2,z3,z34,z4,z5,z24]),(1,[z1,z2,z3,z4,z438,z6]),(0,[z1,z2,z3,z439,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z231,z6])],[(0,[z1,z440,z2,z3,z4,z5,z6]),(0,[z1,z441,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z69,z3,z4,z5,z6]),(1,[z9,z1,z2,z3,z5,z6]),(0,[z1,z20,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z53,z6])],[(0,[z442,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z443]),(0,[z1,z2,z3,z14,z5,z15,z6]),(0,[z1,z2,z3,z444,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z445,z6]),(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z38,z3,z4,z5,z6])],[(0,[z33,z92,z2,z3,z4,z5,z6]),(0,[z1,z2,z447,z3,z4,z5,z6]),(0,[z1,z2,z3,z106,z4,z5,z16]),(0,[z448,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z449,z3,z4,z5,z6])],[(0,[z450,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z451,z4,z5,z6]),(0,[z277,z1,z2,z3,z4,z5,z24])],[(0,[z33,z2,z3,z34,z4,z5,z6]),(0,[z1,z2,z93,z3,z4,z5,z24])],[(0,[z1,z2,z452,z3,z4,z5,z6]),(0,[z1,z179,z2,z3,z4,z142,z6]),(0,[z1,z2,z3,z4,z453,z5,z6])],[(0,[z1,z2,z3,z454,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z455,z6]),(0,[z1,z2,z3,z4,z5,z456,z6]),(0,[z1,z2,z3,z4,z5,z6,z105]),(0,[z1,z457,z2,z3,z4,z5,z6]),(0,[z1,z458,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z459,z4,z5,z6]),(0,[z1,z2,z3,z4,z28,z5,z24])]],
   [[(1,[z92,z2,z93,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z139]),(0,[z1,z2,z3,z4,z5,z6,z460])],[(0,[z1,z2,z3,z4,z5,z461,z6]),(0,[z2,z3,z4,z37,z5,z77,z6]),(0,[z462,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z463,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z139])],[(0,[z464,z1,z2,z3,z4,z5,z6]),(0,[z465,z1,z2,z3,z4,z5,z6])],[(0,[z17,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z34,z4,z5,z16]),(0,[z1,z2,z3,z80,z28,z5,z6]),(0,[z1,z2,z3,z4,z5,z60,z16])],[(0,[z1,z2,z466,z3,z4,z5,z6]),(0,[z1,z2,z467,z3,z4,z5,z6]),(0,[z1,z2,z3,z468,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z252]),(0,[z1,z2,z413,z3,z4,z5,z6]),(0,[z469,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z46,z3,z81,z4,z5]),(0,[z1,z2,z3,z4,z470,z5,z6])],[(0,[z33,z1,z2,z93,z4,z5,z6]),(0,[z141,z1,z2,z3,z4,z210,z6]),(0,[z1,z2,z3,z36,z218,z5,z6]),(0,[z1,z2,z3,z63,z44,z5,z6]),(0,[z1,z2,z3,z4,z471,z5,z6]),(1,[z1,z2,z3,z168,z5,z24])],[(0,[z1,z2,z3,z4,z5,z77,z6]),(0,[z1,z2,z3,z472,z4,z5,z6]),(0,[z135,z1,z2,z3,z4,z5,z6])],[(0,[z43,z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z473,z6]),(1,[z1,z2,z3,z339,z5,z6]),(0,[z1,z2,z291,z3,z4,z5,z16]),(0,[z474,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z475,z6]),(0,[z141,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z476,z3,z4,z5,z6]),(0,[z1,z2,z3,z477,z4,z5,z6]),(0,[z1,z2,z3,z4,z478,z5,z6]),(0,[z1,z122,z2,z3,z106,z5,z6]),(0,[z1,z2,z3,z4,z5,z479,z6]),(1,[z1,z2,z3,z480,z4,z5]),(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z90,z1,z2,z46,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z481,z6]),(0,[z277,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z482,z6]),(0,[z1,z2,z3,z28,z5,z15,z6])],[(0,[z1,z2,z93,z3,z4,z5,z16]),(0,[z1,z122,z3,z4,z36,z5,z6]),(0,[z1,z2,z3,z483,z4,z5,z6]),(0,[z1,z2,z127,z3,z4,z5,z24]),(0,[z1,z2,z3,z81,z4,z171,z6])],[(1,[z1,z2,z3,z264,z5,z6]),(0,[z484,z1,z2,z3,z4,z5,z6]),(0,[z1,z485,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z310,z6])],[(0,[z486,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z487,z4,z5,z6]),(0,[z1,z488,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z28,z5,z16]),(0,[z25,z1,z2,z3,z4,z5,z6]),(0,[z333,z1,z2,z3,z4,z5,z24])],[(0,[z92,z1,z2,z3,z4,z5,z24]),(1,[z1,z2,z3,z4,z5,z299]),(0,[z1,z489,z2,z3,z4,z5,z6]),(0,[z277,z1,z2,z3,z4,z5,z35]),(0,[z306,z1,z2,z3,z4,z5,z16])],[(0,[z1,z2,z3,z490,z4,z5,z6]),(0,[z18,z1,z54,z3,z4,z5,z6]),(0,[z1,z491,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z492,z6]),(0,[z1,z2,z3,z14,z4,z82,z6])],[(0,[z1,z2,z3,z4,z5,z493,z6]),(0,[z1,z2,z3,z4,z5,z126,z6])]],
   [[(0,[z17,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z494,z6]),(0,[z1,z2,z3,z4,z5,z6,z495]),(0,[z1,z2,z496,z3,z4,z5,z6]),(0,[z1,z31,z2,z3,z81,z4,z5]),(0,[z90,z1,z2,z3,z81,z4,z5])],[(1,[z1,z491,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z497]),(0,[z1,z498,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z499,z5,z6]),(1,[z277,z2,z3,z4,z5,z35]),(0,[z197,z1,z122,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z500,z6]),(0,[z1,z2,z3,z4,z142,z5,z24]),(0,[z1,z2,z3,z4,z501,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z502,z1,z2,z3,z4,z5,z6]),(0,[z181,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z503,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z58,z6]),(0,[z504,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z80,z14,z5,z6])],[(1,[z33,z2,z34,z4,z5,z6]),(0,[z64,z2,z3,z4,z37,z5,z6]),(1,[z1,z2,z3,z14,z15,z6])],[(0,[z1,z2,z3,z505,z4,z5,z6]),(0,[z1,z122,z2,z3,z4,z5,z223]),(0,[z1,z2,z3,z4,z5,z506,z6]),(0,[z1,z2,z46,z4,z5,z6,z139]),(0,[z1,z2,z3,z4,z507,z5,z6])],[(0,[z1,z2,z29,z4,z5,z88,z6]),(0,[z1,z2,z3,z4,z5,z6,z186]),(0,[z1,z2,z3,z508,z4,z5,z6]),(0,[z1,z2,z3,z80,z4,z5,z364])],[(0,[z1,z2,z509,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z5,z6]),(0,[z1,z2,z510,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z102,z5,z88]),(0,[z1,z2,z3,z81,z4,z6,z172])]],
   [[(0,[z17,z1,z2,z3,z4,z428,z6]),(0,[z17,z1,z2,z3,z4,z5,z255]),(0,[z1,z2,z3,z4,z511,z5,z6]),(1,[z197,z1,z3,z106,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z360]),(0,[z1,z2,z3,z168,z5,z6,z24]),(0,[z164,z1,z2,z3,z4,z5,z24]),(1,[z1,z2,z3,z169,z4,z24])],[(0,[z1,z2,z512,z3,z4,z5,z6]),(0,[z76,z64,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z513,z4,z5,z6]),(0,[z1,z2,z3,z514,z4,z5,z6]),(0,[z1,z2,z3,z515,z4,z5,z6]),(0,[z334,z1,z2,z3,z4,z5,z16]),(0,[z333,z1,z2,z3,z4,z5,z16]),(0,[z516,z1,z2,z3,z4,z5,z6])],[(0,[z17,z1,z2,z3,z4,z5,z156]),(0,[z92,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z10,z24]),(0,[z517,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z518,z6]),(0,[z1,z2,z3,z519,z4,z5,z6]),(1,[z90,z1,z2,z4,z5,z27]),(0,[z1,z2,z3,z4,z171,z5,z6])],[(0,[z520,z1,z2,z3,z4,z5,z6]),(0,[z277,z2,z3,z4,z5,z6,z35]),(0,[z1,z2,z3,z80,z4,z15,z6])],[(0,[z1,z2,z3,z4,z521,z5,z6]),(0,[z197,z1,z2,z3,z106,z5,z6]),(0,[z1,z2,z3,z480,z4,z5,z6]),(0,[z522,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z80,z4,z28,z6])],[(0,[z1,z2,z3,z4,z5,z6,z523]),(0,[z1,z2,z160,z4,z5,z88,z6]),(0,[z524,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z525,z6]),(0,[z1,z2,z3,z80,z4,z5,z24]),(0,[z1,z2,z3,z4,z526,z5,z6])],[(0,[z1,z2,z3,z527,z4,z5,z6]),(0,[z1,z2,z3,z4,z528,z5,z6]),(1,[z1,z2,z329,z4,z5,z6]),(1,[z135,z1,z3,z4,z5,z23]),(0,[z25,z1,z2,z3,z80,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z529]),(0,[z96,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z142,z5,z16]),(0,[z530,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z194,z5,z24])]],
   [[(0,[z1,z2,z3,z531,z4,z5,z6]),(0,[z1,z2,z3,z4,z532,z5,z6]),(0,[z1,z2,z3,z533,z4,z5,z6]),(0,[z1,z2,z3,z81,z4,z5,z24])],[(0,[z33,z1,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z81,z4,z5,z10]),(0,[z1,z2,z3,z534,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z226]),(0,[z1,z2,z3,z535,z4,z5,z6]),(0,[z1,z2,z536,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z24]),(0,[z1,z2,z3,z537,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z273,z6]),(0,[z123,z1,z2,z3,z4,z5,z6]),(0,[z123,z1,z2,z413,z4,z5,z6]),(0,[z150,z1,z2,z38,z4,z5,z6])],[(1,[z1,z117,z3,z4,z5,z6]),(0,[z538,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z539,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z540,z5,z6]),(0,[z1,z2,z3,z4,z218,z5,z6]),(0,[z76,z1,z2,z3,z4,z5,z24]),(0,[z43,z1,z2,z3,z4,z5,z24]),(0,[z541,z1,z2,z3,z4,z5,z6])],[(0,[z1,z54,z3,z4,z36,z5,z6]),(0,[z1,z2,z3,z4,z542,z5,z6])],[(0,[z1,z2,z160,z34,z4,z5,z6]),(0,[z543,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z124,z88,z6]),(1,[z1,z2,z3,z544,z5,z6])],[(0,[z1,z2,z3,z4,z5,z24,z545])]],
   [[(0,[z141,z1,z2,z3,z4,z5,z299]),(1,[z1,z2,z3,z4,z5,z188]),(0,[z1,z2,z3,z546,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z6]),(1,[z1,z2,z3,z4,z5,z24])],[(0,[z17,z1,z2,z3,z4,z330,z6]),(0,[z547,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z548,z4,z5,z6]),(0,[z1,z2,z549,z3,z4,z5,z6]),(0,[z1,z2,z3,z550,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z371,z16])],[(1,[z18,z121,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z252]),(0,[z1,z2,z3,z4,z5,z551,z6]),(0,[z1,z2,z38,z3,z4,z194,z6]),(0,[z1,z2,z3,z80,z4,z5,z16])],[(0,[z1,z2,z3,z4,z552,z5,z6]),(0,[z1,z2,z3,z72,z4,z5,z6]),(0,[z1,z3,z4,z142,z5,z124,z6]),(0,[z1,z553,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z554,z5,z6])],[(0,[z555,z1,z2,z3,z4,z5,z6]),(0,[z556,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z37,z5,z6]),(0,[z557,z1,z2,z3,z4,z5,z6]),(0,[z558,z1,z2,z3,z4,z5,z6]),(0,[z1,z179,z2,z3,z4,z5,z24]),(0,[z1,z2,z68,z3,z4,z5,z24])],[(0,[z1,z2,z3,z272,z4,z5,z6]),(0,[z141,z1,z2,z3,z63,z5,z6]),(0,[z1,z2,z3,z559,z4,z5,z6]),(0,[z1,z2,z3,z560,z4,z5,z6]),(0,[z1,z2,z3,z106,z4,z5,z561]),(0,[z562,z1,z2,z3,z4,z5,z6]),(0,[z563,z1,z2,z3,z4,z5,z6]),(0,[z1,z564,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z425,z24]),(0,[z1,z2,z3,z81,z4,z5,z16])],[(0,[z1,z2,z3,z4,z5,z185,z6]),(0,[z1,z2,z3,z565,z4,z5,z6]),(0,[z1,z3,z29,z4,z5,z124,z6]),(0,[z566,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z427,z5,z24]),(0,[z1,z2,z3,z4,z4,z5,z16])],[(0,[z567,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z27,z10]),(0,[z123,z1,z2,z3,z4,z142,z6]),(0,[z1,z2,z3,z4,z44,z5,z6]),(0,[z1,z2,z3,z4,z5,z434,z24])]],
   [[(0,[z568,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z88,z24]),(0,[z437,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z569,z3,z4,z5,z6]),(0,[z1,z570,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z571,z6])],[(0,[z121,z2,z54,z3,z4,z5,z6]),(0,[z76,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z81,z4,z5,z35]),(0,[z1,z2,z3,z572,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z573,z4,z5,z6])],[(0,[z1,z2,z3,z574,z4,z5,z6]),(0,[z575,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z576,z6]),(0,[z1,z2,z3,z4,z5,z24,z50]),(0,[z1,z2,z577,z3,z4,z5,z6]),(0,[z578,z1,z2,z3,z4,z5,z6])],[(0,[z1,z20,z2,z3,z4,z5,z24]),(1,[z1,z2,z3,z4,z5,z223]),(0,[z579,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z176,z4,z5,z6]),(0,[z1,z409,z2,z3,z4,z5,z16])],[(0,[z1,z2,z3,z106,z218,z5,z6]),(0,[z1,z2,z3,z4,z580,z5,z6]),(0,[z135,z1,z2,z3,z4,z171,z5]),(0,[z1,z2,z3,z581,z4,z5,z6])],[(0,[z1,z2,z3,z480,z4,z5,z124]),(0,[z1,z2,z38,z3,z4,z5,z24]),(1,[z1,z2,z3,z4,z5,z16])],[(0,[z1,z2,z3,z4,z5,z582,z6]),(0,[z1,z2,z49,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z583,z5,z6]),(0,[z1,z2,z3,z4,z5,z561,z6]),(0,[z1,z2,z3,z4,z5,z23,z6]),(0,[z1,z2,z3,z4,z584,z5,z6]),(1,[z1,z2,z3,z81,z4,z172])],[(0,[z1,z2,z585,z3,z4,z5,z6]),(0,[z1,z2,z3,z14,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z586,z6])]],
   [[(0,[z1,z2,z3,z4,z194,z77,z6]),(0,[z587,z1,z2,z3,z4,z5,z6])],[(0,[z17,z1,z2,z490,z4,z5,z6]),(0,[z141,z25,z1,z2,z3,z5,z6]),(0,[z1,z2,z588,z3,z4,z5,z6]),(0,[z1,z2,z3,z81,z4,z77,z6]),(0,[z1,z2,z3,z589,z4,z5,z6]),(0,[z1,z2,z3,z590,z4,z5,z6]),(0,[z1,z179,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z26,z4,z5,z6]),(0,[z1,z2,z68,z3,z4,z5,z16]),(1,[z1,z2,z3,z80,z28,z6]),(0,[z591,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z592,z4,z5,z6]),(1,[z141,z1,z2,z3,z5,z24]),(0,[z135,z1,z2,z3,z4,z5,z23]),(0,[z1,z2,z3,z4,z5,z187,z6]),(0,[z1,z593,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z594,z4,z5,z6])],[(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z596,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z597]),(0,[z1,z2,z3,z176,z4,z5,z88]),(0,[z1,z2,z3,z4,z5,z598,z6])],[(0,[z1,z2,z93,z29,z4,z5,z6]),(0,[z1,z2,z599,z3,z4,z5,z6]),(0,[z600,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z601,z5,z6])],[(1,[z1,z2,z3,z4,z428,z6]),(1,[z1,z2,z3,z4,z5,z255]),(0,[z1,z2,z3,z4,z5,z602,z6]),(1,[z1,z2,z3,z4,z5,z204]),(0,[z603,z1,z2,z3,z4,z5,z6]),(0,[z76,z1,z2,z3,z4,z77,z6]),(0,[z1,z2,z3,z4,z604,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z605]),(0,[z1,z2,z3,z4,z5,z88,z16]),(0,[z1,z2,z3,z4,z5,z6,z139])],[(0,[z92,z2,z93,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z6]),(0,[z1,z31,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z156]),(0,[z1,z2,z3,z4,z606,z5,z6]),(0,[z1,z2,z3,z4,z607,z5,z6]),(0,[z65,z277,z2,z3,z4,z5,z6]),(0,[z1,z608,z2,z3,z4,z5,z6]),(0,[z609,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z544,z81,z5,z6])]],
   [[(0,[z141,z1,z2,z3,z4,z374,z6]),(0,[z610,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z611,z6]),(0,[z1,z20,z2,z3,z4,z5,z16]),(1,[z1,z2,z3,z4,z5,z126]),(0,[z1,z2,z3,z4,z612,z5,z6])],[(0,[z1,z2,z3,z4,z5,z77,z24]),(0,[z135,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z38,z4,z194,z5,z6]),(0,[z1,z2,z3,z613,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z614,z6]),(0,[z1,z2,z3,z4,z5,z615,z6]),(0,[z1,z616,z2,z3,z4,z5,z6]),(0,[z1,z2,z38,z3,z4,z5,z16]),(0,[z1,z2,z3,z617,z4,z5,z6]),(0,[z1,z2,z3,z618,z4,z5,z6])],[(0,[z141,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z619,z6]),(0,[z1,z2,z160,z3,z4,z5,z24]),(0,[z120,z1,z2,z3,z4,z5,z6]),(0,[z1,z31,z3,z4,z5,z6,z50]),(0,[z150,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z620,z3,z4,z5,z6])],[(0,[z621,z1,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z63,z5,z6]),(0,[z622,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z623,z6])],[(0,[z1,z2,z3,z4,z624,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z27])],[(0,[z141,z1,z2,z3,z218,z5,z6]),(0,[z1,z2,z3,z4,z37,z82,z6])],[(0,[z1,z2,z3,z4,z625,z5,z6]),(0,[z25,z1,z2,z3,z4,z5,z24])]],
   [[(1,[z1,z148,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z290]),(0,[z1,z2,z3,z4,z626,z5,z6])],[(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z627,z6]),(0,[z1,z2,z3,z4,z5,z628,z6]),(0,[z1,z2,z3,z4,z5,z461,z16])],[(0,[z1,z2,z3,z629,z4,z5,z6]),(0,[z1,z2,z3,z264,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z293]),(0,[z1,z630,z2,z3,z4,z5,z6]),(0,[z99,z1,z2,z3,z4,z5,z6])],[(0,[z33,z1,z2,z3,z4,z189,z6]),(0,[z1,z631,z2,z3,z4,z5,z6]),(0,[z632,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z633,z4,z5,z6]),(0,[z150,z1,z2,z3,z4,z88,z6])],[(0,[z1,z2,z634,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z635,z5,z6])],[(0,[z1,z636,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z330,z6]),(0,[z1,z2,z637,z3,z4,z5,z6]),(0,[z638,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z77,z16]),(0,[z1,z639,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z194,z124,z6]),(0,[z135,z1,z2,z3,z4,z5,z16]),(0,[z43,z1,z2,z3,z26,z5,z6]),(0,[z1,z2,z46,z3,z4,z5,z139]),(0,[z1,z112,z2,z3,z4,z5,z6]),(0,[z25,z1,z2,z3,z5,z16,z6])],[(0,[z197,z1,z54,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z640,z6]),(0,[z1,z641,z2,z3,z4,z5,z6])]],
   [[(0,[z141,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z160,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z642,z5,z6]),(0,[z150,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z479,z16])],[(1,[z1,z2,z476,z4,z5,z6]),(0,[z643,z1,z2,z3,z4,z5,z6]),(0,[z25,z1,z2,z3,z36,z5,z6]),(0,[z1,z2,z4,z5,z27,z6,z139]),(0,[z1,z2,z3,z4,z5,z24,z133])],[(0,[z1,z2,z3,z4,z644,z5,z6]),(0,[z645,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z35,z139]),(0,[z1,z2,z3,z29,z4,z5,z24]),(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z102,z5,z6])],[(0,[z1,z2,z3,z4,z5,z647,z6]),(0,[z1,z2,z3,z4,z648,z5,z6]),(0,[z1,z2,z3,z4,z5,z649,z6]),(0,[z1,z20,z160,z3,z4,z5,z6]),(0,[z123,z1,z2,z329,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z266,z6])],[(0,[z1,z54,z3,z29,z4,z5,z6]),(0,[z1,z2,z93,z4,z44,z5,z6]),(0,[z135,z1,z2,z3,z4,z5,z50]),(0,[z1,z650,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z169,z4,z6,z24]),(0,[z25,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z16,z586])],[(0,[z33,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z651,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z364]),(0,[z1,z2,z3,z4,z171,z5,z24])],[(0,[z1,z121,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z171,z5,z10]),(0,[z1,z2,z3,z652,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z653,z6]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z68,z3,z26,z5,z6])],[(0,[z1,z2,z34,z29,z4,z5,z6]),(0,[z1,z2,z655,z3,z4,z5,z6]),(0,[z1,z2,z3,z63,z4,z5,z105]),(0,[z1,z2,z3,z656,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z124,z24])]],
   [[(0,[z1,z657,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z658,z5,z6]),(0,[z659,z1,z2,z3,z4,z5,z6]),(0,[z25,z96,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z660,z5,z6])],[(0,[z1,z2,z3,z4,z5,z661,z6])],[(0,[z96,z1,z2,z3,z4,z5,z24]),(0,[z1,z122,z2,z3,z4,z5,z58]),(0,[z90,z1,z2,z3,z4,z5,z139]),(0,[z1,z2,z3,z4,z244,z6,z24])],[(0,[z1,z2,z3,z4,z28,z77,z6]),(0,[z1,z2,z3,z4,z194,z37,z6]),(0,[z1,z179,z2,z3,z4,z124,z6])],[(0,[z17,z1,z121,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z4,z5,z6]),(0,[z662,z1,z2,z3,z4,z5,z6]),(0,[z1,z179,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z23]),(0,[z1,z2,z3,z44,z5,z6,z24])],[(0,[z96,z1,z2,z3,z218,z5,z6]),(0,[z1,z663,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z273,z6]),(0,[z197,z1,z2,z3,z4,z5,z6]),(0,[z123,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z142,z88,z6]),(0,[z664,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z490,z4,z5,z6]),(0,[z665,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z26,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z666]),(0,[z667,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z668,z6]),(0,[z1,z2,z669,z3,z4,z5,z6]),(0,[z123,z1,z179,z3,z4,z5,z6]),(0,[z1,z179,z3,z4,z142,z5,z6]),(0,[z1,z2,z4,z194,z5,z88,z6]),(0,[z1,z2,z3,z670,z4,z5,z6])],[(0,[z18,z1,z2,z3,z4,z5,z6]),(1,[z17,z54,z3,z4,z5,z6]),(0,[z18,z121,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z671,z5,z6]),(0,[z1,z2,z3,z4,z218,z5,z24]),(0,[z1,z2,z3,z4,z77,z82,z6]),(0,[z1,z2,z3,z29,z4,z5,z16]),(0,[z1,z2,z3,z168,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z672]),(0,[z150,z1,z2,z4,z5,z88,z6])],[(0,[z2,z93,z3,z34,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z231]),(0,[z221,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z673,z6]),(0,[z1,z2,z26,z4,z44,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z24]),(0,[z1,z2,z3,z4,z171,z5,z16])],[(0,[z1,z2,z3,z4,z674,z5,z6]),(0,[z1,z675,z2,z3,z4,z5,z6]),(0,[z676,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z24])],[(0,[z1,z2,z677,z3,z4,z5,z6]),(0,[z1,z2,z678,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z16,z10]),(0,[z1,z2,z3,z4,z5,z6,z545]),(0,[z1,z2,z3,z4,z5,z124,z16]),(0,[z1,z2,z46,z3,z146,z5,z6]),(0,[z1,z2,z3,z544,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z189,z6]),(0,[z141,z1,z2,z3,z4,z5,z293]),(0,[z1,z2,z3,z4,z37,z15,z6]),(0,[z1,z2,z3,z4,z5,z6,z679]),(0,[z1,z2,z3,z4,z5,z680,z6]),(0,[z1,z2,z3,z4,z5,z422,z6]),(0,[z1,z2,z3,z81,z4,z5,z172])],[(0,[z65,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z171,z5,z35]),(0,[z1,z2,z3,z4,z36,z5,z24]),(1,[z25,z1,z2,z3,z5,z16])],[(0,[z681,z1,z2,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z438,z5,z6]),(0,[z1,z20,z3,z4,z5,z124,z6]),(1,[z1,z2,z3,z4,z5,z561]),(0,[z1,z2,z3,z169,z4,z5,z6])]],
   [[(0,[z682,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z683,z6]),(0,[z1,z31,z2,z3,z326,z5,z6])],[(0,[z1,z2,z3,z4,z684,z5,z6]),(0,[z685,z1,z2,z3,z4,z5,z6]),(0,[z686,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z687,z6]),(0,[z1,z2,z3,z688,z4,z5,z6]),(0,[z566,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z689,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z690,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z85,z6]),(0,[z1,z2,z3,z691,z4,z5,z6]),(0,[z123,z1,z2,z3,z4,z5,z16]),(1,[z1,z2,z3,z5,z16,z24]),(1,[z1,z2,z3,z4,z244,z24])],[(0,[z1,z2,z3,z4,z5,z6,z692]),(0,[z1,z2,z3,z4,z5,z693,z6]),(0,[z1,z2,z3,z4,z694,z5,z6]),(0,[z1,z695,z2,z3,z4,z5,z6]),(0,[z1,z696,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z91]),(0,[z1,z2,z3,z4,z5,z697,z6])],[(0,[z141,z1,z2,z476,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z2,z3,z4,z218,z5,z16]),(0,[z698,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z699,z6]),(0,[z1,z2,z3,z106,z5,z6,z24])],[(0,[z700,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z701,z4,z5,z6]),(1,[z1,z2,z3,z36,z5,z24]),(0,[z1,z2,z3,z4,z702,z5,z6]),(0,[z1,z2,z3,z703,z4,z5,z6])],[(0,[z1,z2,z3,z4,z142,z77,z6]),(0,[z1,z2,z3,z4,z5,z704,z6])],[(0,[z1,z2,z3,z4,z47,z5,z6]),(0,[z1,z2,z34,z4,z44,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z65,z1,z2,z3,z4,z438,z6]),(0,[z705,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z706,z6]),(0,[z1,z2,z3,z4,z5,z6,z50]),(0,[z150,z1,z491,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z707,z4,z5,z6]),(0,[z1,z2,z3,z4,z708,z6]),(0,[z1,z2,z476,z4,z5,z24]),(0,[z1,z2,z3,z4,z709,z6]),(0,[z161,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z710]),(0,[z711,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z80,z5,z91])],[(0,[z1,z2,z3,z4,z428,z255]),(0,[z33,z117,z34,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z712]),(0,[z1,z2,z3,z4,z713,z6]),(0,[z1,z2,z3,z714,z5,z6]),(0,[z1,z2,z3,z5,z479,z24])],[(0,[z1,z2,z3,z5,z481,z24]),(0,[z1,z31,z3,z4,z5,z422]),(0,[z1,z2,z247,z44,z5,z6])],[(0,[z1,z2,z3,z4,z428,z156]),(0,[z1,z2,z3,z4,z5,z715]),(0,[z1,z491,z3,z4,z5,z24]),(0,[z1,z2,z3,z146,z5,z371])],[(0,[z1,z2,z3,z4,z5,z716]),(0,[z1,z148,z3,z4,z5,z16]),(0,[z1,z2,z3,z4,z717,z5]),(0,[z141,z49,z3,z218,z5,z6]),(0,[z1,z177,z3,z106,z5,z6]),(0,[z1,z2,z46,z4,z5,z139]),(1,[z1,z2,z3,z718,z6]),(0,[z1,z2,z3,z168,z5,z719])],[(0,[z1,z2,z3,z4,z5,z720]),(0,[z1,z2,z721,z4,z5,z6]),(0,[z277,z2,z3,z4,z5,z722]),(0,[z347,z1,z29,z4,z5,z6]),(0,[z1,z2,z3,z14,z718,z6]),(0,[z1,z2,z3,z169,z4,z360])],[(0,[z1,z2,z490,z272,z5,z6]),(0,[z1,z2,z3,z4,z5,z723]),(0,[z1,z2,z724,z4,z5,z6]),(0,[z1,z725,z3,z4,z5,z6]),(0,[z141,z96,z2,z3,z5,z24]),(0,[z1,z2,z3,z339,z5,z16]),(0,[z1,z2,z3,z14,z15,z24])],[(0,[z17,z54,z3,z272,z5,z6]),(0,[z1,z2,z3,z4,z726,z6]),(0,[z1,z2,z3,z4,z727,z6]),(0,[z1,z2,z3,z728,z5,z6]),(0,[z96,z2,z3,z5,z53,z24]),(0,[z1,z2,z3,z729,z5,z6]),(0,[z1,z3,z36,z5,z434,z24]),(0,[z1,z2,z3,z4,z5,z730]),(0,[z1,z2,z26,z44,z5,z24]),(0,[z150,z1,z2,z4,z88,z6]),(0,[z40,z1,z2,z3,z5,z24])]],
   [[(0,[z1,z2,z3,z4,z5,z731]),(0,[z1,z2,z3,z272,z5,z732]),(0,[z646,z54,z3,z4,z5,z6]),(0,[z1,z733,z3,z4,z5,z6]),(1,[z1,z2,z72,z5,z24]),(0,[z1,z2,z3,z5,z23,z192]),(0,[z1,z2,z3,z4,z5,z734]),(0,[z1,z2,z3,z5,z126,z24])],[(0,[z141,z2,z72,z218,z5,z6]),(0,[z1,z2,z4,z5,z735,z6]),(0,[z1,z2,z3,z4,z5,z736]),(0,[z1,z2,z3,z4,z5,z737])],[(0,[z1,z2,z3,z4,z5,z738]),(0,[z1,z2,z3,z4,z330,z16]),(0,[z1,z2,z3,z4,z739,z6]),(0,[z1,z2,z3,z264,z5,z16]),(0,[z1,z740,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z741]),(0,[z277,z1,z2,z3,z5,z192]),(0,[z1,z2,z3,z4,z310,z16]),(0,[z19,z1,z742,z4,z5,z6]),(0,[z197,z1,z3,z106,z5,z24]),(0,[z1,z2,z3,z4,z5,z743])],[(0,[z1,z2,z3,z4,z744,z6]),(0,[z1,z2,z3,z5,z500,z24]),(0,[z1,z2,z3,z4,z745,z5]),(0,[z1,z2,z3,z80,z82,z24])],[(0,[z1,z2,z3,z746,z5,z6]),(0,[z1,z2,z3,z4,z5,z747]),(0,[z25,z1,z2,z3,z5,z561]),(0,[z90,z1,z2,z4,z5,z425])],[(0,[z1,z2,z476,z4,z5,z16]),(0,[z646,z1,z2,z3,z5,z24])],[(0,[z1,z2,z3,z4,z5,z748]),(0,[z1,z2,z749,z4,z5,z6]),(0,[z1,z2,z3,z4,z750,z6]),(0,[z65,z2,z3,z4,z5,z53]),(0,[z1,z2,z3,z751,z5,z6]),(0,[z1,z650,z160,z4,z5,z6])],[(0,[z141,z1,z2,z476,z5,z24]),(0,[z1,z2,z3,z752,z5,z6]),(0,[z1,z2,z3,z5,z753,z24])]],
   [[(0,[z1,z54,z3,z200,z5,z6]),(0,[z1,z2,z3,z754,z4,z5]),(0,[z1,z2,z3,z4,z37,z185]),(0,[z9,z65,z2,z3,z5,z10]),(0,[z1,z2,z329,z4,z5,z24]),(0,[z1,z2,z3,z81,z326,z5]),(0,[z1,z491,z3,z4,z5,z16])],[(0,[z380,z2,z93,z4,z5,z6]),(0,[z1,z179,z329,z4,z5,z6]),(0,[z1,z2,z3,z339,z5,z126]),(0,[z90,z1,z2,z3,z169,z4]),(0,[z1,z2,z3,z80,z267,z6])],[(0,[z1,z2,z3,z4,z330,z255]),(0,[z1,z2,z3,z755,z5,z6]),(0,[z1,z2,z3,z264,z5,z204])],[(0,[z1,z2,z3,z14,z15,z16]),(0,[z1,z2,z3,z80,z169,z24]),(0,[z1,z112,z3,z4,z5,z545])],[(0,[z1,z2,z3,z4,z330,z156]),(0,[z1,z2,z3,z4,z5,z756]),(0,[z181,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z4,z5,z757]),(0,[z1,z2,z3,z4,z273,z6]),(0,[z19,z1,z29,z4,z273,z6]),(0,[z197,z1,z3,z758,z5,z6]),(1,[z1,z2,z3,z5,z719])],[(0,[z1,z117,z3,z4,z5,z24]),(0,[z1,z2,z3,z176,z4,z37]),(0,[z1,z2,z3,z759,z4,z273]),(0,[z1,z2,z760,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z761]),(0,[z25,z1,z2,z3,z5,z719])],[(0,[z1,z2,z3,z526,z5,z24])],[(0,[z1,z2,z3,z4,z5,z732]),(0,[z296,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z528,z5,z24]),(0,[z197,z1,z3,z106,z5,z16]),(0,[z1,z2,z3,z4,z762,z6]),(0,[z1,z2,z3,z81,z4,z114]),(0,[z1,z2,z3,z4,z763,z24])]],
   [[(0,[z1,z2,z764,z4,z5,z6]),(0,[z1,z2,z3,z5,z765,z24]),(0,[z1,z2,z3,z106,z5,z24]),(0,[z135,z1,z3,z4,z507,z5]),(0,[z1,z2,z3,z4,z766,z24]),(0,[z1,z2,z3,z544,z5,z24])],[(0,[z1,z2,z3,z4,z767,z6]),(0,[z1,z2,z3,z4,z768,z6]),(0,[z1,z2,z3,z4,z5,z769]),(0,[z123,z1,z3,z480,z4,z124]),(0,[z135,z1,z2,z3,z267,z5]),(0,[z1,z2,z3,z198,z5,z24]),(0,[z1,z2,z3,z26,z5,z753])],[(0,[z1,z2,z490,z4,z5,z16]),(0,[z1,z2,z3,z4,z770,z6]),(0,[z1,z2,z466,z3,z5,z24])],[(0,[z17,z54,z3,z4,z5,z16]),(0,[z33,z2,z34,z4,z5,z204]),(0,[z1,z2,z93,z44,z5,z24]),(0,[z1,z2,z3,z4,z5,z771]),(0,[z1,z2,z4,z194,z772,z6]),(0,[z1,z2,z3,z617,z5,z24]),(0,[z1,z2,z3,z81,z4,z364]),(0,[z1,z2,z3,z80,z626,z6])],[(0,[z1,z2,z3,z773,z5,z6])],[(0,[z1,z148,z3,z264,z5,z6]),(0,[z96,z2,z3,z728,z5,z6]),(0,[z1,z2,z329,z4,z5,z16]),(0,[z1,z2,z3,z4,z5,z774]),(1,[z1,z2,z4,z5,z775])],[(0,[z1,z2,z3,z776,z5,z6]),(0,[z1,z2,z3,z4,z5,z777]),(0,[z1,z2,z3,z4,z5,z226]),(0,[z1,z2,z3,z4,z171,z82])],[(0,[z1,z2,z3,z4,z5,z778]),(0,[z1,z2,z3,z4,z5,z779])]],
   [[],[(0,[z1,z780,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z781,z6]),(0,[z1,z2,z3,z656,z5,z24]),(0,[z1,z2,z3,z4,z5,z782]),(0,[z783,z2,z3,z4,z5,z6]),(0,[z1,z2,z46,z4,z5,z775]),(0,[z1,z2,z3,z5,z16,z24])],[(0,[z1,z2,z490,z4,z428,z6]),(0,[z1,z2,z490,z4,z5,z255]),(0,[z1,z2,z69,z272,z5,z6]),(0,[z1,z2,z3,z4,z5,z784]),(0,[z1,z117,z3,z4,z5,z16]),(0,[z1,z49,z3,z4,z374,z6]),(0,[z1,z631,z3,z4,z5,z50]),(0,[z1,z2,z3,z4,z785,z6]),(0,[z1,z2,z3,z4,z5,z786]),(0,[z1,z2,z3,z758,z5,z6]),(0,[z1,z2,z3,z4,z5,z787]),(0,[z788,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z789,z5,z6])],[(0,[z1,z2,z3,z4,z790,z6]),(0,[z1,z2,z3,z47,z189,z6]),(0,[z1,z2,z3,z5,z551,z24]),(0,[z1,z2,z3,z36,z244,z24]),(0,[z1,z2,z3,z791,z4,z6]),(0,[z110,z1,z2,z3,z5,z24]),(0,[z135,z1,z3,z4,z5,z792]),(0,[z1,z2,z3,z4,z5,z793]),(0,[z221,z1,z2,z3,z4,z75])],[(0,[z1,z2,z490,z4,z5,z156]),(0,[z1,z2,z3,z4,z5,z794]),(0,[z1,z2,z3,z552,z5,z24]),(0,[z1,z2,z3,z4,z5,z795]),(0,[z1,z2,z3,z81,z4,z666]),(0,[z1,z2,z3,z4,z5,z796]),(0,[z1,z2,z3,z4,z5,z797]),(0,[z1,z2,z3,z80,z28,z364])],[(0,[z17,z54,z3,z4,z5,z156]),(0,[z1,z2,z3,z176,z4,z77]),(1,[z1,z2,z3,z798,z5]),(0,[z1,z2,z68,z44,z5,z187]),(0,[z1,z2,z3,z4,z5,z799]),(0,[z1,z2,z3,z544,z5,z16])],[(0,[z33,z2,z34,z4,z5,z290]),(1,[z2,z3,z4,z800,z6]),(0,[z1,z801,z3,z4,z5,z6])],[(0,[z1,z2,z3,z548,z5,z24]),(0,[z1,z2,z72,z4,z374,z6]),(0,[z1,z2,z3,z4,z5,z252]),(0,[z151,z2,z3,z4,z37,z6]),(0,[z1,z2,z3,z4,z171,z401]),(0,[z1,z2,z3,z392,z5,z24]),(0,[z1,z2,z3,z544,z81,z172])]],
   [[(0,[z1,z2,z476,z4,z5,z299]),(0,[z1,z2,z3,z802,z5,z6]),(0,[z1,z2,z3,z44,z5,z24])],[(0,[z1,z2,z3,z4,z5,z803]),(0,[z1,z122,z3,z36,z5,z58]),(0,[z1,z2,z3,z146,z5,z139]),(0,[z1,z2,z3,z80,z718,z6])],[(0,[z1,z117,z3,z4,z5,z204]),(0,[z1,z3,z106,z36,z5,z24]),(0,[z1,z2,z3,z80,z15,z24])],[(0,[z804,z1,z2,z4,z5,z6]),(0,[z2,z805,z34,z4,z5,z6]),(0,[z232,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z806,z4,z5]),(0,[z96,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z542,z5,z16]),(0,[z1,z2,z3,z163,z5,z24]),(0,[z1,z2,z3,z80,z28,z24]),(0,[z1,z2,z3,z4,z807,z24])],[(0,[z1,z2,z3,z4,z5,z808]),(0,[z1,z2,z3,z4,z5,z809])],[(0,[z1,z2,z810,z4,z5,z6]),(0,[z1,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z1,z2,z3,z41,z5,z24])],[(0,[z1,z2,z3,z4,z5,z812]),(0,[z1,z813,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z814,z6]),(0,[z1,z2,z3,z4,z5,z815])],[(0,[z1,z2,z3,z4,z428,z24]),(0,[z1,z2,z3,z5,z816,z6]),(0,[z1,z2,z3,z4,z5,z58]),(0,[z1,z2,z3,z4,z5,z817]),(0,[z1,z2,z3,z36,z5,z223]),(0,[z1,z2,z3,z5,z561,z24]),(0,[z1,z3,z329,z4,z124,z6]),(0,[z1,z2,z127,z4,z5,z84])]],
   [[(0,[z1,z2,z818,z3,z5,z6]),(0,[z1,z2,z819,z4,z5,z6]),(0,[z65,z2,z3,z4,z5,z10]),(0,[z1,z2,z68,z44,z5,z6]),(0,[z150,z1,z39,z4,z88,z6]),(0,[z1,z2,z3,z5,z586,z24])],[(0,[z1,z2,z69,z4,z5,z6]),(0,[z1,z2,z69,z200,z5,z6]),(0,[z1,z292,z2,z3,z5,z24]),(0,[z1,z2,z3,z4,z5,z820]),(0,[z1,z821,z3,z4,z5,z6]),(0,[z1,z2,z3,z81,z4,z91])],[(0,[z1,z49,z3,z4,z5,z16]),(0,[z1,z20,z160,z4,z5,z6]),(0,[z1,z2,z3,z822,z4,z5]),(0,[z1,z20,z193,z4,z5,z6]),(0,[z1,z2,z3,z4,z823,z5]),(0,[z1,z2,z3,z368,z5,z24]),(0,[z1,z2,z3,z267,z5,z6]),(0,[z334,z2,z3,z4,z5,z461])],[(0,[z1,z2,z490,z4,z330,z6]),(0,[z1,z2,z824,z4,z5,z6]),(0,[z1,z825,z3,z4,z5,z6]),(0,[z1,z2,z826,z4,z5,z6]),(0,[z1,z2,z3,z4,z827,z5]),(0,[z1,z2,z3,z80,z244,z24])],[(0,[z1,z2,z3,z4,z828,z6]),(0,[z1,z2,z3,z829,z5,z6]),(0,[z1,z2,z3,z4,z5,z830]),(0,[z76,z2,z3,z4,z77,z6]),(0,[z1,z2,z3,z4,z831,z5]),(0,[z1,z2,z3,z5,z832,z24]),(0,[z1,z2,z3,z5,z598,z24])],[(0,[z1,z2,z3,z833,z5,z6]),(0,[z1,z834,z3,z4,z5,z6]),(0,[z141,z2,z3,z218,z210,z6]),(0,[z1,z2,z3,z4,z5,z835]),(0,[z1,z2,z3,z601,z5,z24]),(0,[z1,z2,z3,z472,z5,z24]),(0,[z1,z2,z3,z4,z5,z836]),(0,[z1,z2,z3,z4,z5,z266])],[(0,[z1,z2,z3,z4,z5,z837]),(0,[z1,z2,z3,z4,z5,z838]),(0,[z1,z839,z3,z4,z5,z6]),(0,[z1,z2,z3,z604,z5,z24])],[(0,[z1,z2,z72,z4,z5,z16]),(0,[z662,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z840,z5,z6]),(0,[z1,z2,z3,z4,z5,z841]),(0,[z150,z1,z2,z4,z772,z6]),(0,[z1,z2,z3,z81,z146,z5])]],
   [[(0,[z1,z2,z3,z842,z5,z6]),(0,[z1,z2,z3,z843,z5,z6]),(0,[z33,z2,z805,z4,z5,z6]),(0,[z141,z2,z3,z218,z5,z6]),(0,[z141,z1,z260,z3,z5,z24]),(0,[z1,z2,z3,z4,z5,z844]),(0,[z90,z1,z2,z4,z389,z5]),(0,[z1,z2,z3,z533,z5,z24]),(0,[z1,z2,z3,z80,z28,z16]),(0,[z1,z2,z3,z4,z845,z6])],[(0,[z1,z2,z3,z4,z5,z846]),(0,[z65,z2,z3,z4,z438,z10]),(0,[z1,z2,z3,z326,z5,z479]),(0,[z1,z2,z3,z612,z5,z24]),(0,[z1,z2,z3,z5,z24,z75])],[(0,[z1,z148,z3,z4,z5,z24]),(0,[z1,z2,z3,z41,z5,z16]),(0,[z1,z2,z3,z847,z4,z5])],[(0,[z1,z2,z3,z4,z5,z848]),(0,[z217,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z4,z709,z24])],[(0,[z1,z152,z3,z36,z5,z6]),(0,[z1,z2,z3,z4,z5,z849]),(0,[z213,z2,z3,z4,z5,z35]),(0,[z1,z20,z3,z4,z273,z6])],[],[(0,[z1,z2,z3,z850,z5,z6]),(1,[z1,z3,z758,z5,z6])],[(0,[z1,z2,z3,z264,z85,z6]),(0,[z1,z260,z3,z4,z210,z6]),(0,[z1,z2,z3,z4,z5,z105]),(0,[z1,z2,z329,z4,z124,z6]),(0,[z1,z2,z3,z4,z851,z6]),(0,[z1,z852,z3,z4,z5,z6]),(0,[z90,z1,z2,z3,z267,z5]),(0,[z1,z2,z3,z14,z15,z231])]],
   [[(0,[z1,z2,z3,z4,z330,z24]),(0,[z853,z1,z2,z3,z5,z6]),(0,[z64,z2,z3,z4,z37,z185]),(0,[z1,z2,z3,z625,z5,z24])],[(0,[z1,z2,z3,z854,z5,z6]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z1,z31,z2,z3,z169,z4]),(0,[z1,z2,z284,z3,z5,z24])],[(0,[z1,z260,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z856]),(0,[z1,z2,z3,z72,z5,z24]),(0,[z108,z2,z3,z4,z77,z6]),(0,[z1,z39,z38,z4,z5,z6]),(0,[z1,z2,z3,z5,z628,z24]),(0,[z1,z2,z3,z81,z4,z857])],[],[(0,[z1,z858,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z757]),(0,[z65,z2,z3,z5,z10,z192]),(0,[z1,z2,z3,z26,z5,z24]),(0,[z1,z2,z4,z772,z88,z6])],[(0,[z859,z2,z3,z4,z5,z6]),(0,[z1,z31,z3,z4,z5,z50]),(0,[z1,z2,z3,z5,z16,z56])],[(0,[z1,z2,z4,z5,z860,z6]),(0,[z1,z2,z3,z4,z861,z6]),(0,[z25,z1,z49,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z100]),(0,[z1,z2,z3,z4,z5,z862]),(0,[z1,z2,z863,z44,z5,z6])],[(0,[z567,z1,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z864]),(0,[z1,z2,z3,z4,z5,z865])]],
   [[(0,[z33,z2,z34,z4,z85,z6]),(0,[z1,z2,z3,z866,z5,z6])],[(0,[z1,z2,z3,z4,z5,z867]),(0,[z1,z2,z3,z4,z868,z6]),(0,[z2,z3,z728,z218,z5,z6]),(0,[z1,z2,z3,z869,z5,z6]),(0,[z1,z2,z3,z4,z870,z6]),(0,[z197,z1,z3,z106,z5,z561]),(0,[z1,z2,z3,z5,z16,z369])],[(0,[z1,z2,z3,z4,z871,z6]),(0,[z1,z2,z3,z872,z5,z6]),(0,[z1,z873,z3,z4,z5,z6]),(0,[z150,z1,z491,z4,z88,z6]),(0,[z1,z2,z291,z4,z5,z27])],[(0,[z1,z2,z34,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z874]),(0,[z1,z2,z3,z4,z5,z875]),(0,[z64,z2,z3,z4,z37,z6]),(0,[z1,z2,z3,z4,z5,z876]),(0,[z1,z2,z3,z5,z159,z24])],[(0,[z1,z2,z3,z5,z266,z24])],[(0,[z1,z2,z3,z4,z877,z6]),(0,[z878,z54,z3,z4,z5,z6]),(0,[z18,z878,z3,z4,z5,z6]),(0,[z1,z49,z3,z4,z5,z299]),(0,[z96,z1,z2,z3,z169,z24]),(0,[z1,z2,z3,z879,z4,z105]),(0,[z334,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z572,z5,z24])],[(0,[z1,z49,z476,z4,z5,z6]),(0,[z1,z2,z3,z513,z5,z24])],[(0,[z1,z148,z3,z4,z5,z204]),(0,[z1,z2,z3,z4,z273,z24])]],
   [[(0,[z1,z2,z490,z4,z5,z24]),(0,[z1,z2,z3,z81,z5,z192]),(0,[z1,z2,z3,z146,z5,z6]),(0,[z1,z2,z760,z4,z5,z24])],[(0,[z17,z54,z3,z4,z5,z24]),(0,[z141,z1,z2,z3,z5,z105]),(0,[z1,z2,z3,z169,z4,z6]),(0,[z1,z2,z3,z718,z5,z6])],[(0,[z1,z2,z3,z272,z5,z6]),(0,[z1,z49,z3,z63,z5,z6]),(0,[z1,z2,z72,z4,z5,z299]),(0,[z287,z1,z3,z4,z124,z6]),(0,[z1,z2,z3,z4,z5,z880]),(0,[z1,z2,z3,z4,z881,z6]),(0,[z1,z2,z882,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z883]),(0,[z1,z2,z3,z863,z5,z6]),(0,[z1,z2,z3,z5,z661,z24]),(0,[z1,z2,z3,z4,z171,z244])],[(0,[z1,z2,z3,z560,z5,z16]),(0,[z1,z2,z3,z4,z884,z6])],[(0,[z1,z2,z3,z4,z5,z885]),(0,[z33,z2,z34,z47,z5,z6]),(0,[z256,z1,z2,z3,z5,z24]),(0,[z64,z2,z3,z4,z37,z252]),(0,[z1,z2,z3,z5,z192,z139]),(0,[z1,z2,z3,z4,z5,z886]),(0,[z1,z2,z887,z4,z5,z6]),(0,[z1,z2,z3,z176,z4,z5])],[(0,[z1,z2,z3,z888,z5,z6]),(0,[z1,z2,z3,z5,z757,z6]),(0,[z1,z409,z3,z4,z5,z479])],[(0,[z1,z2,z3,z200,z5,z889]),(0,[z1,z2,z3,z4,z5,z889]),(0,[z575,z54,z3,z4,z5,z6]),(0,[z99,z96,z2,z3,z5,z24]),(0,[z1,z2,z3,z4,z5,z185]),(0,[z1,z2,z3,z4,z5,z186]),(0,[z1,z2,z3,z4,z5,z890]),(0,[z1,z2,z891,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z187]),(0,[z1,z892,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z893]),(0,[z1,z2,z3,z4,z189,z6]),(0,[z1,z117,z3,z4,z85,z6]),(0,[z1,z2,z72,z63,z5,z6]),(0,[z1,z894,z3,z4,z5,z6]),(0,[z895,z2,z3,z4,z5,z6]),(0,[z1,z742,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z896]),(0,[z1,z669,z3,z36,z5,z6]),(0,[z1,z2,z46,z4,z5,z586]),(0,[z1,z2,z3,z169,z16,z24])]],
   [[(0,[z1,z2,z3,z4,z5,z897]),(0,[z1,z112,z3,z36,z5,z6]),(0,[z123,z1,z3,z4,z124,z6]),(0,[z123,z1,z413,z4,z124,z6]),(0,[z1,z898,z3,z4,z5,z6]),(0,[z1,z39,z3,z4,z194,z6]),(0,[z1,z2,z3,z169,z4,z91])],[(0,[z1,z2,z3,z899,z5,z6]),(0,[z1,z2,z3,z243,z5,z24]),(0,[z1,z2,z3,z4,z171,z327]),(0,[z1,z900,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z901])],[(0,[z1,z148,z3,z4,z5,z290]),(0,[z1,z2,z3,z902,z5,z6]),(0,[z1,z2,z903,z4,z5,z6]),(0,[z1,z2,z904,z4,z5,z6]),(0,[z1,z2,z3,z574,z5,z24]),(0,[z1,z2,z3,z106,z244,z24]),(0,[z1,z2,z3,z81,z267,z172])],[(1,[z878,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z905,z6]),(0,[z587,z2,z34,z4,z5,z6]),(0,[z1,z122,z3,z36,z5,z6]),(0,[z1,z2,z3,z4,z906,z6]),(1,[z1,z329,z4,z124,z6]),(0,[z1,z907,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z85,z24]),(0,[z1,z2,z3,z674,z5,z24]),(0,[z141,z260,z3,z218,z5,z6]),(0,[z1,z2,z3,z4,z273,z16]),(0,[z1,z2,z3,z13,z5,z24]),(0,[z1,z2,z3,z480,z798,z5]),(0,[z1,z3,z4,z5,z792,z6]),(0,[z150,z1,z2,z4,z102,z88])],[(0,[z1,z112,z2,z3,z169,z4])],[(0,[z1,z2,z3,z4,z210,z6]),(0,[z1,z2,z3,z37,z15,z24]),(0,[z1,z2,z3,z791,z4,z24]),(0,[z1,z2,z3,z5,z422,z24])],[(0,[z1,z2,z3,z4,z908,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z909]),(0,[z1,z2,z3,z264,z5,z290]),(0,[z316,z1,z2,z4,z88,z6]),(0,[z1,z2,z3,z4,z182,z60]),(0,[z1,z2,z3,z81,z4,z170])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z200,z5,z6]),(0,[z19,z1,z29,z4,z5,z6]),(0,[z1,z2,z413,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z910]),(0,[z1,z2,z3,z4,z5,z911]),(0,[z1,z112,z3,z4,z5,z50]),(0,[z1,z2,z46,z339,z5,z139]),(0,[z1,z2,z3,z4,z912,z6]),(0,[z1,z801,z3,z4,z5,z24])],[(0,[z141,z1,z49,z3,z5,z24]),(0,[z1,z2,z913,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z24])],[(0,[z1,z914,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z915]),(0,[z1,z2,z3,z5,z24,z376])],[(0,[z1,z2,z3,z4,z5,z916]),(0,[z1,z2,z3,z694,z5,z24]),(0,[z1,z2,z3,z4,z5,z832]),(0,[z1,z2,z127,z44,z5,z6]),(0,[z1,z2,z3,z4,z5,z917]),(0,[z1,z2,z3,z5,z697,z24]),(0,[z306,z1,z2,z4,z5,z586])],[(0,[z1,z2,z476,z4,z5,z293]),(0,[z1,z2,z3,z5,z210,z24]),(0,[z579,z2,z3,z4,z77,z6]),(0,[z123,z1,z3,z4,z918,z6])],[(0,[z1,z121,z490,z4,z5,z6]),(0,[z17,z54,z3,z4,z428,z6]),(0,[z17,z54,z3,z4,z5,z255]),(0,[z1,z2,z3,z4,z919,z6]),(0,[z1,z2,z3,z106,z5,z223]),(0,[z25,z1,z2,z3,z5,z266]),(0,[z1,z2,z3,z5,z719,z6])],[(0,[z1,z2,z3,z200,z5,z920]),(0,[z1,z2,z3,z4,z5,z920]),(0,[z17,z878,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z921]),(0,[z393,z1,z2,z4,z88,z6]),(0,[z1,z2,z3,z4,z5,z922]),(0,[z1,z2,z3,z4,z171,z355]),(0,[z90,z1,z2,z4,z5,z775]),(0,[z1,z2,z3,z16,z244,z24])]],
   [[(0,[z1,z2,z3,z923,z5,z6]),(0,[z1,z2,z3,z47,z5,z24]),(0,[z1,z924,z3,z4,z5,z6]),(0,[z1,z49,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z925]),(0,[z926,z1,z2,z3,z5,z185]),(0,[z1,z2,z3,z927,z5,z6]),(0,[z1,z2,z149,z4,z194,z6]),(0,[z1,z928,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z929]),(0,[z1,z2,z3,z4,z85,z16]),(0,[z1,z3,z4,z918,z124,z6]),(0,[z1,z2,z3,z5,z16,z719])],[(0,[z1,z2,z3,z4,z438,z6]),(0,[z1,z2,z3,z44,z244,z24])],[(0,[z1,z214,z2,z3,z5,z24]),(0,[z1,z2,z3,z4,z930,z6]),(0,[z1,z2,z3,z4,z5,z931]),(0,[z1,z2,z3,z4,z932,z6]),(0,[z1,z49,z3,z218,z5,z6]),(0,[z1,z2,z3,z565,z28,z6]),(0,[z1,z39,z3,z4,z5,z6]),(0,[z1,z2,z3,z933,z5,z6]),(0,[z1,z3,z106,z758,z5,z6]),(0,[z1,z2,z68,z44,z5,z24]),(0,[z1,z2,z3,z169,z4,z53])],[(0,[z1,z2,z69,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z934]),(0,[z1,z2,z3,z4,z5,z935]),(0,[z1,z2,z3,z41,z5,z561]),(0,[z1,z2,z3,z4,z82,z364])],[(0,[z1,z2,z72,z4,z5,z24]),(0,[z1,z936,z3,z4,z5,z6]),(0,[z2,z3,z63,z728,z5,z6]),(0,[z96,z1,z2,z3,z244,z24]),(0,[z1,z2,z3,z4,z937,z105]),(0,[z1,z2,z3,z146,z5,z27]),(0,[z1,z2,z3,z5,z15,z91])],[(0,[z1,z938,z3,z4,z5,z6]),(0,[z1,z2,z3,z267,z5,z10]),(0,[z1,z2,z939,z4,z5,z6]),(0,[z388,z1,z3,z4,z124,z6]),(0,[z1,z2,z3,z4,z6,z857])],[(0,[z1,z2,z3,z940,z5,z6]),(0,[z1,z2,z3,z879,z4,z6]),(0,[z76,z2,z3,z4,z77,z24]),(0,[z1,z2,z3,z4,z800,z6]),(0,[z1,z2,z3,z4,z11,z16]),(0,[z1,z31,z3,z326,z5,z50])]],
   [[(0,[z1,z2,z72,z218,z5,z6]),(0,[z141,z2,z3,z218,z374,z6]),(0,[z1,z2,z3,z941,z5,z6]),(0,[z1,z2,z3,z4,z942,z5]),(0,[z1,z2,z46,z689,z4,z5])],[(0,[z1,z2,z3,z4,z85,z204]),(0,[z1,z2,z3,z4,z5,z943]),(0,[z1,z2,z3,z4,z944,z5]),(0,[z1,z2,z3,z5,z60,z24])],[(0,[z1,z2,z805,z4,z5,z6]),(0,[z1,z3,z4,z5,z945,z6]),(0,[z1,z2,z3,z4,z5,z946]),(0,[z2,z3,z4,z5,z10,z722])],[(0,[z1,z2,z3,z947,z5,z6]),(0,[z926,z1,z2,z3,z5,z6]),(0,[z1,z237,z29,z4,z5,z6]),(0,[z150,z1,z2,z176,z4,z88])],[(0,[z1,z2,z3,z4,z5,z948]),(0,[z59,z2,z3,z4,z37,z6]),(0,[z99,z2,z3,z4,z5,z133]),(0,[z1,z2,z3,z4,z857,z172])],[(0,[z1,z121,z3,z36,z5,z24]),(0,[z1,z2,z3,z47,z5,z16]),(0,[z1,z2,z3,z264,z5,z756]),(0,[z1,z949,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z950,z6]),(0,[z361,z1,z2,z4,z5,z27]),(0,[z1,z2,z3,z4,z5,z951]),(0,[z1,z2,z3,z952,z4,z6]),(0,[z1,z2,z3,z537,z5,z24])],[(0,[z1,z2,z3,z4,z953,z6]),(0,[z1,z2,z3,z954,z4,z5]),(0,[z1,z2,z3,z5,z955,z6]),(0,[z1,z2,z3,z78,z5,z24]),(0,[z1,z2,z3,z4,z956,z5])],[(0,[z17,z54,z3,z4,z330,z6]),(0,[z1,z2,z3,z4,z5,z957]),(0,[z1,z2,z3,z958,z4,z6]),(0,[z1,z2,z3,z77,z15,z24]),(0,[z1,z2,z3,z5,z83,z24]),(0,[z1,z2,z39,z4,z88,z6]),(0,[z1,z2,z3,z297,z5,z24]),(0,[z1,z2,z3,z4,z959,z5]),(0,[z566,z1,z3,z4,z5,z434])]],
   [[(0,[z1,z117,z3,z4,z5,z290]),(0,[z1,z2,z68,z44,z5,z16]),(0,[z1,z2,z127,z3,z169,z4])],[(0,[z1,z2,z69,z4,z5,z16]),(0,[z1,z2,z3,z169,z106,z24]),(0,[z1,z2,z3,z81,z4,z73]),(0,[z960,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z961,z6]),(0,[z1,z2,z3,z15,z244,z24]),(0,[z1,z2,z3,z5,z89,z24])],[(0,[z1,z2,z962,z4,z5,z6]),(0,[z963,z1,z2,z3,z4,z6]),(0,[z1,z260,z3,z4,z374,z6]),(0,[z1,z2,z3,z210,z6,z24]),(0,[z1,z964,z3,z4,z5,z6]),(0,[z96,z2,z3,z63,z5,z105]),(0,[z288,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z965,z6]),(0,[z1,z2,z3,z267,z5,z16])],[(0,[z1,z2,z3,z966,z5,z6]),(0,[z1,z2,z3,z967,z5,z6]),(0,[z1,z2,z3,z4,z968,z6]),(0,[z587,z2,z3,z218,z5,z6]),(0,[z1,z2,z3,z5,z192,z6]),(0,[z645,z1,z2,z4,z88,z6]),(0,[z1,z2,z3,z169,z4,z133])],[(0,[z1,z148,z3,z4,z85,z6]),(0,[z1,z2,z3,z4,z85,z290]),(0,[z76,z2,z3,z4,z77,z16]),(0,[z65,z2,z3,z4,z5,z722])],[(0,[z1,z2,z3,z969,z5,z6]),(0,[z1,z260,z3,z4,z5,z24])],[(0,[z1,z2,z3,z970,z5,z6]),(0,[z1,z2,z3,z4,z5,z971]),(0,[z1,z2,z3,z47,z5,z972]),(0,[z33,z2,z34,z4,z189,z6]),(0,[z161,z2,z3,z4,z37,z6]),(0,[z1,z3,z29,z4,z273,z6]),(0,[z388,z1,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z973]),(0,[z1,z2,z3,z146,z171,z5]),(0,[z1,z2,z3,z81,z4,z75])],[(0,[z1,z2,z3,z4,z974,z6]),(0,[z1,z2,z3,z4,z648,z82]),(0,[z1,z2,z3,z4,z5,z975])]],
   [[(0,[z1,z2,z3,z4,z5,z976]),(1,[z1,z49,z3,z5,z24]),(0,[z1,z2,z3,z480,z4,z37]),(0,[z1,z2,z3,z4,z845,z16])],[(0,[z1,z54,z490,z4,z5,z6]),(0,[z1,z2,z69,z4,z428,z6]),(0,[z1,z2,z69,z4,z5,z255]),(0,[z96,z2,z3,z63,z5,z100]),(0,[z1,z2,z3,z4,z977,z5]),(0,[z197,z1,z3,z106,z5,z186]),(0,[z1,z2,z978,z4,z5,z6])],[(0,[z1,z2,z979,z4,z5,z6]),(0,[z1,z2,z3,z4,z82,z91])],[(0,[z1,z2,z69,z4,z5,z156]),(0,[z1,z2,z3,z113,z5,z24])],[(0,[z1,z2,z3,z4,z980,z6]),(0,[z309,z1,z3,z106,z5,z6]),(0,[z1,z2,z3,z36,z5,z105]),(0,[z1,z2,z742,z4,z5,z6]),(0,[z981,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z118,z5,z24])],[(0,[z1,z2,z3,z4,z982,z6]),(0,[z1,z2,z3,z983,z5,z6]),(0,[z1,z31,z3,z116,z4,z5]),(0,[z568,z1,z2,z3,z5,z24]),(0,[z150,z1,z2,z4,z88,z24])],[(0,[z64,z2,z3,z4,z37,z24]),(0,[z1,z2,z3,z26,z244,z24])],[(0,[z17,z54,z490,z4,z5,z6]),(0,[z1,z2,z3,z4,z984,z5]),(0,[z1,z985,z3,z4,z5,z6]),(0,[z1,z2,z3,z370,z5,z24]),(0,[z135,z1,z3,z4,z5,z434]),(0,[z1,z2,z3,z5,z16,z473]),(0,[z1,z2,z4,z5,z735,z24])]],
   [[(0,[z33,z2,z34,z4,z5,z6]),(0,[z1,z148,z3,z47,z5,z6]),(0,[z2,z3,z4,z37,z800,z6]),(0,[z1,z2,z3,z14,z15,z6])],[(0,[z1,z2,z3,z4,z986,z6]),(0,[z1,z2,z34,z44,z5,z24]),(0,[z1,z2,z3,z4,z5,z987])],[(0,[z1,z2,z3,z4,z5,z988]),(0,[z1,z117,z93,z4,z5,z6]),(0,[z1,z49,z3,z4,z5,z293]),(0,[z1,z260,z3,z4,z5,z16]),(0,[z1,z2,z3,z989,z5,z6]),(0,[z123,z1,z3,z4,z67,z124]),(0,[z1,z2,z3,z143,z5,z24]),(0,[z990,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z718,z15,z6])],[(0,[z25,z1,z2,z72,z5,z6]),(0,[z1,z2,z3,z145,z5,z24]),(0,[z1,z3,z758,z4,z5,z6]),(0,[z1,z2,z3,z326,z5,z6]),(0,[z1,z2,z3,z146,z5,z24])],[(0,[z991,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z169,z4,z24]),(0,[z1,z2,z3,z4,z182,z82])],[(0,[z1,z2,z3,z4,z992,z6]),(0,[z1,z117,z3,z4,z189,z6]),(0,[z1,z2,z3,z169,z4,z10]),(0,[z1,z2,z3,z154,z5,z24]),(0,[z437,z1,z2,z4,z5,z425])],[(0,[z1,z2,z3,z4,z993,z6]),(0,[z1,z2,z994,z4,z5,z6]),(0,[z2,z3,z4,z5,z722,z35]),(0,[z1,z2,z29,z4,z273,z6]),(0,[z90,z1,z2,z4,z5,z27])],[(0,[z1,z2,z72,z4,z5,z293]),(0,[z25,z1,z2,z3,z210,z6]),(0,[z1,z2,z3,z4,z937,z6])]],
   [[(0,[z1,z2,z3,z480,z4,z77])],[(0,[z65,z2,z3,z4,z310,z10]),(0,[z181,z2,z3,z4,z5,z173])],[(0,[z1,z2,z69,z4,z330,z6]),(0,[z1,z2,z995,z4,z5,z6]),(0,[z1,z2,z3,z4,z189,z24]),(0,[z1,z2,z3,z996,z480,z5]),(0,[z150,z1,z2,z4,z88,z16]),(0,[z437,z1,z2,z3,z169,z4])],[(0,[z64,z2,z3,z4,z37,z16]),(0,[z1,z112,z3,z36,z5,z24]),(0,[z123,z1,z3,z4,z124,z24]),(1,[z1,z39,z4,z88,z6]),(0,[z1,z898,z3,z4,z5,z24]),(0,[z1,z2,z3,z444,z5,z16]),(0,[z1,z2,z3,z4,z82,z857])],[(0,[z1,z2,z997,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z998]),(0,[z1,z2,z512,z44,z5,z6]),(0,[z110,z2,z3,z63,z5,z6])],[(0,[z999,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z1000]),(0,[z1,z2,z3,z1001,z4,z5]),(0,[z1,z2,z68,z863,z5,z6]),(0,[z1,z2,z3,z4,z5,z364])],[(0,[z315,z121,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1002]),(0,[z99,z2,z3,z4,z5,z35]),(0,[z1,z122,z3,z36,z5,z24]),(0,[z1,z2,z3,z4,z1003,z6]),(0,[z1,z2,z3,z4,z5,z1004]),(0,[z1,z2,z3,z60,z244,z24])],[(0,[z2,z3,z4,z728,z5,z6]),(1,[z1,z2,z3,z4,z857])]],
   [[(0,[z1,z2,z3,z4,z5,z1005]),(0,[z1,z409,z3,z4,z5,z23]),(0,[z1,z2,z3,z146,z5,z16])],[(0,[z1,z2,z3,z4,z374,z6]),(0,[z1,z2,z3,z4,z210,z24]),(0,[z1006,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z169,z4,z16])],[(0,[z1,z2,z3,z272,z5,z16]),(0,[z1,z2,z3,z4,z1007,z6]),(1,[z1,z2,z4,z772,z6]),(0,[z1,z2,z3,z4,z5,z775])],[(0,[z141,z2,z3,z218,z5,z299]),(0,[z1,z2,z3,z4,z5,z1008]),(0,[z1,z2,z3,z196,z5,z24]),(0,[z1,z2,z3,z1009,z5,z6]),(0,[z1,z2,z3,z4,z1010,z6]),(0,[z1,z2,z3,z4,z5,z1011]),(0,[z1,z2,z3,z4,z5,z1012])],[(0,[z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z200,z5,z24]),(0,[z96,z2,z3,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z1013]),(0,[z19,z1,z29,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z1014]),(0,[z1,z2,z3,z169,z15,z6])],[(0,[z1,z2,z3,z169,z4,z35]),(0,[z1,z2,z291,z4,z5,z371])],[(0,[z18,z121,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1015]),(0,[z378,z1,z29,z4,z5,z6]),(0,[z1,z2,z3,z759,z4,z5]),(0,[z1,z2,z3,z207,z5,z24]),(0,[z1,z2,z3,z169,z26,z24]),(0,[z1,z2,z3,z267,z5,z60])],[(0,[z1,z2,z3,z4,z189,z16]),(0,[z1,z2,z3,z4,z5,z1016]),(0,[z1,z260,z3,z4,z5,z293]),(0,[z1,z2,z3,z5,z185,z757]),(0,[z1,z2,z3,z81,z4,z351]),(0,[z1,z2,z3,z1017,z5,z6]),(0,[z1,z2,z127,z44,z5,z24])]],
   [[(0,[z1,z1018,z3,z4,z5,z6]),(0,[z141,z2,z3,z728,z5,z6]),(1,[z2,z3,z4,z5,z722]),(0,[z1,z2,z3,z4,z1019,z6]),(1,[z1,z742,z4,z5,z6]),(0,[z123,z1,z3,z4,z124,z16])],[(0,[z249,z1,z29,z4,z5,z6]),(0,[z393,z1,z3,z4,z124,z6]),(0,[z1,z2,z1020,z4,z5,z6]),(0,[z1,z2,z3,z5,z216,z24]),(0,[z1,z2,z3,z176,z1021,z5]),(0,[z1,z2,z3,z1021,z5,z6]),(0,[z1,z2,z3,z5,z15,z24])],[(0,[z1,z2,z3,z272,z428,z6]),(0,[z1,z2,z3,z272,z5,z255]),(0,[z1,z2,z1022,z4,z5,z6]),(0,[z1,z2,z3,z1023,z5,z6]),(0,[z1,z2,z1024,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z765]),(0,[z1,z3,z4,z5,z1025,z6]),(0,[z1,z2,z3,z1026,z4,z5]),(0,[z108,z1,z2,z3,z5,z24])],[(0,[z17,z54,z69,z4,z5,z6]),(0,[z1,z2,z3,z4,z1027,z5]),(0,[z1,z2,z3,z1028,z5,z6]),(0,[z1,z122,z3,z36,z5,z16]),(0,[z1,z2,z1029,z3,z176,z5]),(0,[z1,z2,z3,z4,z244,z6]),(0,[z1,z2,z3,z4,z16,z244])],[(0,[z1,z2,z3,z272,z5,z156]),(0,[z1,z878,z3,z4,z5,z6]),(0,[z121,z878,z3,z4,z5,z6]),(0,[z1,z2,z3,z26,z5,z105]),(0,[z1,z2,z3,z4,z5,z1030])],[(0,[z1,z2,z1031,z4,z5,z6]),(0,[z1,z20,z690,z4,z5,z6]),(0,[z1,z260,z3,z4,z5,z299]),(0,[z1,z2,z3,z4,z1032,z6]),(0,[z1,z2,z3,z4,z5,z1033]),(0,[z1,z2,z3,z4,z1021,z5])],[(0,[z1,z117,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z1034]),(0,[z1,z2,z3,z4,z5,z1035]),(0,[z1,z260,z476,z4,z5,z6]),(0,[z1,z2,z3,z4,z210,z16]),(0,[z1,z2,z3,z4,z438,z10]),(0,[z1,z39,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z1036])],[(0,[z1,z2,z3,z4,z189,z204]),(0,[z1,z2,z3,z4,z5,z1037]),(0,[z1,z2,z49,z3,z5,z24]),(0,[z1,z2,z1038,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1039]),(0,[z1,z2,z3,z4,z5,z1040]),(0,[z1,z2,z3,z459,z5,z24])]],
   [[(0,[z1041,z1,z2,z3,z4,z5]),(0,[z1,z405,z3,z36,z5,z6]),(0,[z654,z2,z3,z4,z37,z6]),(0,[z1,z2,z3,z4,z5,z1042])],[(0,[z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z3,z200,z5,z16]),(0,[z1,z2,z1043,z4,z5,z6]),(0,[z19,z1,z29,z4,z5,z16]),(0,[z1,z2,z3,z4,z1044,z5]),(0,[z1,z2,z3,z4,z5,z1045]),(0,[z1,z2,z3,z1021,z5,z88])],[(0,[z1,z2,z3,z47,z85,z6]),(0,[z1,z2,z3,z4,z77,z185]),(1,[z1,z29,z4,z273,z6]),(0,[z316,z1,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z1046,z6]),(0,[z1,z3,z4,z5,z792,z50]),(0,[z1,z2,z3,z44,z5,z226]),(0,[z1,z2,z3,z81,z4,z172])],[(0,[z141,z1,z2,z3,z210,z24]),(0,[z158,z1,z2,z4,z88,z6]),(0,[z1,z2,z3,z4,z5,z1047]),(0,[z1,z2,z3,z248,z5,z24]),(0,[z1,z2,z38,z4,z194,z6]),(0,[z1,z2,z3,z4,z5,z91]),(0,[z1,z2,z3,z4,z1048,z6])],[(0,[z1049,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z814,z24])],[(0,[z1,z2,z3,z4,z1050,z6]),(0,[z1,z1051,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z1052]),(0,[z1,z2,z3,z798,z5,z124]),(0,[z1,z2,z3,z1053,z5,z6])],[(0,[z141,z1,z2,z3,z5,z24]),(0,[z1,z2,z1054,z4,z5,z6]),(0,[z1,z2,z3,z4,z1055,z6]),(0,[z277,z2,z3,z4,z5,z173]),(0,[z1,z2,z3,z420,z5,z24]),(0,[z1,z2,z44,z5,z425,z24]),(0,[z1,z39,z3,z4,z88,z6]),(0,[z1,z2,z3,z5,z262,z24])],[(0,[z1,z2,z3,z1056,z5,z6]),(0,[z9,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z565,z5,z24]),(0,[z1,z2,z3,z1057,z5,z6]),(0,[z1,z2,z1058,z4,z5,z6]),(0,[z1,z3,z4,z5,z23,z792]),(0,[z1,z2,z3,z1059,z5,z6])]],
   [[(0,[z1,z20,z160,z4,z5,z24]),(0,[z1,z2,z3,z267,z5,z24]),(0,[z1,z2,z3,z952,z4,z24])],[(0,[z1,z2,z3,z4,z428,z6]),(0,[z1,z2,z3,z4,z5,z255]),(0,[z1,z2,z3,z200,z428,z6]),(0,[z1,z2,z3,z200,z5,z255]),(0,[z1,z2,z3,z4,z1060,z6]),(0,[z1,z2,z3,z4,z5,z1061]),(0,[z1,z2,z127,z4,z5,z139]),(0,[z1,z2,z3,z544,z5,z266])],[(0,[z1,z148,z3,z4,z189,z6]),(0,[z1,z2,z3,z4,z5,z972]),(0,[z1,z2,z3,z4,z438,z16]),(0,[z1,z2,z3,z4,z5,z1062]),(0,[z1,z31,z2,z3,z267,z5]),(0,[z1,z2,z3,z1063,z5,z6]),(0,[z1,z2,z3,z4,z1064,z6]),(0,[z1,z2,z3,z958,z4,z24])],[(0,[z1,z2,z3,z4,z5,z156]),(0,[z1,z2,z3,z200,z5,z156]),(0,[z1,z2,z3,z272,z330,z6]),(0,[z1,z2,z3,z81,z4,z222]),(0,[z1,z2,z3,z996,z5,z6]),(0,[z1,z39,z3,z4,z5,z16]),(0,[z1,z2,z3,z81,z4,z244])],[(0,[z1,z2,z3,z1065,z5,z6]),(0,[z141,z1,z2,z3,z5,z765]),(0,[z1,z2,z366,z4,z194,z6]),(0,[z1,z2,z3,z1066,z5,z6]),(0,[z1,z2,z1067,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1068]),(0,[z1,z2,z3,z4,z5,z126]),(0,[z1,z2,z3,z4,z5,z753]),(0,[z1,z2,z3,z487,z5,z24]),(0,[z1,z2,z3,z4,z961,z24])],[(0,[z1,z2,z3,z4,z977,z273]),(0,[z1,z2,z3,z101,z5,z24]),(0,[z1,z964,z3,z4,z5,z24])],[(0,[z141,z2,z3,z218,z5,z24]),(0,[z1,z2,z3,z5,z192,z24]),(0,[z1,z2,z3,z4,z5,z1069]),(0,[z1,z312,z2,z3,z5,z16])],[(0,[z1,z1070,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z1071,z6]),(0,[z92,z2,z93,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1072]),(0,[z1,z3,z742,z4,z5,z6]),(0,[z1,z2,z3,z4,z427,z244])]],
   [[(0,[z66,z121,z3,z4,z5,z6]),(0,[z1,z2,z3,z264,z189,z6]),(0,[z1,z2,z3,z4,z1073,z6]),(0,[z1,z2,z3,z4,z5,z1074])],[(0,[z2,z3,z805,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1075]),(0,[z1,z2,z3,z1076,z5,z6]),(0,[z1,z2,z3,z589,z5,z24]),(0,[z1,z2,z3,z326,z171,z5]),(0,[z1,z1077,z3,z4,z5,z6])],[(0,[z1,z2,z863,z4,z5,z6]),(0,[z1,z2,z3,z5,z295,z24])],[(0,[z1,z49,z72,z4,z5,z6]),(0,[z1,z2,z3,z4,z210,z293]),(0,[z1,z2,z3,z559,z5,z24]),(0,[z1,z2,z3,z106,z5,z105]),(0,[z1,z2,z3,z80,z81,z24])],[(0,[z1,z148,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z299,z24]),(0,[z1,z31,z3,z4,z5,z792]),(0,[z1,z2,z3,z168,z5,z24]),(0,[z120,z1,z3,z4,z5,z422]),(0,[z1,z2,z3,z4,z5,z857])],[(0,[z1,z2,z3,z4,z5,z1078]),(0,[z64,z1,z2,z3,z5,z757]),(0,[z280,z2,z3,z4,z5,z35]),(0,[z1,z2,z160,z4,z273,z6]),(0,[z1,z20,z160,z4,z5,z16])],[(0,[z1,z2,z466,z44,z5,z6]),(0,[z1,z2,z3,z4,z5,z293]),(1,[z2,z3,z728,z5,z6]),(0,[z1,z2,z3,z339,z5,z6]),(0,[z1,z2,z3,z80,z56,z6]),(0,[z1,z2,z3,z169,z267,z6])],[(0,[z1,z2,z3,z4,z5,z1079]),(0,[z1,z2,z3,z4,z5,z1080]),(0,[z1,z2,z3,z1081,z4,z6]),(0,[z1,z2,z3,z480,z4,z5]),(0,[z1,z2,z3,z326,z5,z23])]],
   [[(0,[z1,z2,z3,z47,z5,z204]),(0,[z1,z2,z3,z1082,z5,z6])],[(0,[z1,z2,z3,z4,z210,z299]),(0,[z1,z2,z3,z267,z5,z35]),(0,[z1,z2,z1083,z4,z5,z6]),(0,[z1,z2,z3,z5,z311,z24])],[(0,[z1,z2,z3,z4,z330,z6]),(0,[z1,z2,z3,z200,z330,z6]),(0,[z1,z2,z1084,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1085]),(0,[z1,z2,z1086,z4,z5,z6]),(0,[z1,z2,z3,z264,z5,z6]),(0,[z1,z2,z476,z4,z210,z6]),(0,[z1,z2,z1087,z4,z5,z6]),(0,[z1,z2,z3,z4,z310,z6]),(0,[z1,z2,z3,z4,z5,z1088])],[(0,[z1,z2,z3,z1089,z4,z6]),(0,[z33,z2,z34,z4,z5,z24]),(0,[z141,z2,z3,z218,z5,z16]),(0,[z1,z2,z3,z4,z5,z1090]),(0,[z1,z2,z3,z1091,z5,z6]),(0,[z1,z39,z4,z5,z88,z6])],[(0,[z1,z2,z3,z4,z5,z1092]),(0,[z1,z2,z3,z4,z5,z299]),(0,[z1,z2,z1093,z4,z5,z6]),(0,[z65,z1,z2,z3,z5,z192]),(0,[z1,z2,z3,z80,z28,z266])],[(0,[z1,z2,z476,z4,z5,z6]),(0,[z575,z2,z34,z4,z5,z6]),(0,[z1,z2,z3,z1094,z5,z6]),(0,[z1,z2,z3,z5,z27,z192]),(0,[z334,z1,z2,z3,z5,z24])],[(0,[z1,z1095,z3,z4,z5,z6]),(0,[z1,z2,z3,z326,z5,z24]),(0,[z1,z2,z3,z26,z5,z226]),(0,[z1096,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1097])]],
   [[(0,[z1,z2,z3,z1098,z4,z5]),(0,[z1,z491,z3,z4,z5,z6])],[(1,[z1,z2,z3,z210,z24]),(0,[z1,z2,z136,z3,z5,z24]),(0,[z1,z2,z3,z267,z77,z6]),(0,[z277,z2,z3,z4,z5,z35]),(0,[z1,z2,z3,z5,z192,z50]),(0,[z1,z2,z3,z4,z1099,z5]),(0,[z1,z2,z3,z169,z168,z24])],[(0,[z1,z2,z3,z1100,z5,z6]),(0,[z1,z1101,z3,z4,z5,z6]),(0,[z1,z2,z3,z267,z5,z82])],[(0,[z1,z2,z3,z5,z1102,z6]),(0,[z1,z2,z3,z47,z5,z290]),(0,[z1,z2,z3,z44,z5,z105]),(0,[z2,z3,z4,z5,z800,z6]),(0,[z1,z2,z46,z3,z169,z4])],[(0,[z1,z2,z3,z1103,z5,z6]),(0,[z144,z1,z2,z3,z5,z24]),(0,[z96,z2,z3,z5,z53,z6]),(0,[z1,z2,z3,z4,z1104,z6]),(0,[z123,z1,z329,z4,z124,z6])],[(0,[z1,z1105,z3,z4,z5,z6])],[(0,[z96,z1,z2,z3,z5,z105]),(0,[z1,z1106,z3,z4,z5,z6]),(0,[z1,z2,z3,z1107,z5,z6])],[(0,[z9,z1,z2,z3,z5,z299]),(0,[z1,z2,z3,z5,z346,z24]),(0,[z197,z1,z3,z106,z5,z6])]],
   [[(0,[z1,z2,z3,z272,z5,z24]),(0,[z1,z2,z1108,z4,z5,z6]),(0,[z33,z2,z34,z4,z5,z16]),(0,[z1,z260,z72,z4,z5,z6]),(0,[z141,z1,z2,z3,z169,z24]),(0,[z141,z641,z2,z3,z5,z6]),(0,[z1,z2,z3,z253,z5,z24]),(0,[z1,z3,z758,z36,z5,z6]),(0,[z1,z1109,z3,z4,z5,z6]),(0,[z1,z2,z3,z1110,z5,z6])],[(0,[z219,z2,z93,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1111]),(0,[z1,z2,z3,z4,z5,z1112]),(0,[z1,z2,z3,z534,z5,z24]),(0,[z1,z2,z3,z169,z4,z172])],[(0,[z1,z2,z490,z4,z5,z6]),(0,[z1,z2,z490,z200,z5,z6]),(0,[z1,z2,z3,z4,z5,z1113]),(0,[z8,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z352,z5,z24]),(0,[z1,z2,z3,z4,z5,z1114]),(0,[z1,z2,z3,z14,z15,z91])],[(0,[z17,z54,z3,z4,z5,z6]),(0,[z17,z54,z3,z200,z5,z6]),(0,[z1,z54,z3,z36,z5,z24]),(0,[z1,z657,z2,z3,z5,z24]),(0,[z1,z2,z3,z1115,z5,z6]),(0,[z1,z2,z3,z326,z5,z16])],[(0,[z1,z2,z1116,z4,z5,z6]),(0,[z1,z2,z3,z4,z374,z24]),(0,[z1,z2,z3,z4,z5,z1117]),(0,[z1,z2,z3,z4,z5,z1118]),(0,[z1,z2,z3,z4,z772,z6]),(0,[z1,z2,z3,z4,z718,z6]),(0,[z1,z2,z3,z80,z5,z975]),(0,[z1,z1119,z2,z3,z4,z5])],[(0,[z92,z2,z805,z4,z5,z6]),(0,[z1,z2,z329,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1120]),(0,[z135,z1,z3,z4,z5,z23]),(1,[z1,z2,z3,z1021,z5]),(0,[z1,z2,z3,z4,z5,z231]),(0,[z1,z2,z3,z4,z1007,z24])],[(0,[z1,z2,z3,z4,z1121,z6]),(0,[z524,z2,z3,z4,z5,z35]),(0,[z1,z2,z3,z169,z36,z24]),(0,[z1,z31,z3,z41,z5,z50]),(0,[z1,z2,z3,z4,z1010,z24])],[(0,[z1,z498,z160,z4,z5,z6]),(0,[z96,z2,z3,z63,z5,z24]),(0,[z1,z122,z3,z758,z5,z6]),(0,[z1,z2,z3,z798,z5,z6]),(0,[z1,z2,z3,z169,z15,z24]),(0,[z1,z2,z3,z4,z244,z364])]],
   [[(0,[z141,z2,z3,z218,z5,z293]),(0,[z1,z2,z3,z4,z918,z6]),(0,[z1,z2,z3,z80,z169,z6]),(0,[z1,z2,z903,z4,z5,z24])],[(0,[z18,z121,z3,z4,z5,z24]),(0,[z1,z1122,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1123,z6]),(0,[z1,z2,z3,z4,z5,z1124]),(0,[z1,z2,z3,z326,z5,z50]),(0,[z1,z2,z3,z514,z5,z24]),(0,[z1,z2,z3,z4,z5,z1125])],[(0,[z1,z117,z3,z4,z5,z6]),(0,[z646,z2,z3,z218,z5,z6]),(0,[z1,z2,z3,z5,z371,z24]),(0,[z25,z1,z2,z3,z5,z16]),(0,[z1,z2,z3,z169,z4,z244])],[(0,[z1,z2,z3,z4,z1126,z6]),(0,[z1,z2,z3,z4,z5,z1127]),(0,[z1128,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z561]),(0,[z1,z2,z3,z4,z5,z1129]),(0,[z566,z1,z2,z3,z169,z4])],[(0,[z1,z2,z3,z4,z5,z1130]),(0,[z667,z1,z3,z4,z5,z23]),(0,[z1,z2,z3,z4,z763,z6])],[(0,[z1,z2,z93,z47,z5,z6]),(0,[z1,z1131,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1132]),(0,[z1,z2,z3,z4,z766,z6]),(0,[z1,z3,z4,z5,z918,z6]),(0,[z1,z2,z3,z544,z5,z6]),(0,[z1,z3,z4,z5,z1025,z24])],[(0,[z197,z1,z3,z548,z5,z6]),(0,[z1,z2,z3,z4,z85,z6]),(0,[z2,z93,z805,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1133]),(0,[z1,z2,z1134,z4,z5,z6]),(0,[z1,z2,z3,z4,z244,z24])],[(0,[z1,z2,z3,z1135,z5,z6]),(0,[z141,z2,z476,z218,z5,z6]),(0,[z1,z160,z742,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1136]),(0,[z1,z2,z3,z138,z5,z24]),(0,[z1,z2,z413,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z188]),(0,[z1,z2,z4,z5,z775,z6])]],
   [[(0,[z1,z2,z3,z106,z5,z832])],[(0,[z1,z2,z3,z4,z374,z16]),(0,[z600,z1,z2,z3,z5,z24]),(0,[z1137,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z36,z5,z24]),(0,[z1,z2,z3,z1138,z5,z6]),(0,[z1,z2,z3,z4,z171,z857])],[(0,[z64,z2,z3,z4,z800,z6]),(0,[z1,z2,z329,z4,z142,z6]),(0,[z1,z2,z3,z4,z1139,z5]),(0,[z1,z2,z3,z4,z5,z1140])],[(0,[z1,z2,z3,z1141,z5,z6]),(0,[z33,z148,z34,z4,z5,z6]),(0,[z1,z2,z3,z342,z5,z24]),(0,[z1,z2,z3,z4,z5,z792]),(0,[z1142,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z372,z5,z24])],[(0,[z1,z292,z3,z36,z5,z6]),(0,[z1,z2,z585,z44,z5,z6]),(0,[z96,z2,z3,z63,z5,z16]),(0,[z1,z2,z3,z4,z11,z6]),(0,[z19,z1,z29,z4,z11,z6]),(0,[z1,z122,z3,z36,z5,z223]),(0,[z1,z2,z3,z5,z719,z24]),(0,[z1,z2,z3,z4,z5,z719])],[(0,[z1,z2,z3,z4,z5,z1143]),(0,[z1,z2,z3,z4,z1144,z6]),(0,[z382,z2,z3,z4,z77,z6]),(0,[z1,z2,z38,z4,z190,z6]),(0,[z1,z2,z3,z4,z5,z1145]),(0,[z25,z1,z2,z3,z5,z126]),(0,[z1,z2,z3,z4,z5,z1146])],[(0,[z18,z121,z3,z4,z5,z16]),(1,[z2,z805,z4,z5,z6]),(0,[z1,z49,z3,z5,z6,z24]),(0,[z141,z1,z2,z3,z374,z24]),(0,[z1,z2,z3,z4,z5,z1147]),(0,[z1,z2,z3,z4,z1148,z6]),(0,[z1,z2,z3,z412,z5,z24]),(0,[z1,z2,z3,z1149,z5,z6]),(0,[z1,z2,z38,z4,z194,z24])],[(0,[z1,z2,z3,z1150,z5,z6]),(0,[z1,z49,z3,z4,z210,z6]),(0,[z2,z3,z4,z800,z77,z6]),(0,[z1,z2,z3,z439,z5,z24]),(0,[z1,z2,z3,z5,z975,z24])]],
   [[(0,[z1,z2,z3,z4,z1151,z5]),(0,[z1,z2,z3,z336,z15,z6]),(0,[z1,z2,z3,z5,z1152,z6]),(0,[z1,z2,z3,z4,z438,z24]),(0,[z1,z2,z3,z4,z5,z1153]),(0,[z1,z1154,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1155,z5,z6]),(0,[z1,z2,z3,z4,z5,z1156]),(0,[z33,z2,z34,z264,z5,z6]),(0,[z1,z2,z3,z4,z5,z722]),(0,[z1,z2,z3,z4,z1157,z6]),(0,[z1,z2,z4,z5,z772,z6]),(0,[z1,z2,z3,z4,z1055,z24]),(0,[z1,z2,z3,z169,z4,z82])],[(0,[z1,z49,z3,z4,z5,z6]),(0,[z141,z1,z2,z72,z5,z24]),(0,[z1,z2,z3,z336,z5,z24]),(0,[z9,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z4,z5,z1158]),(0,[z1,z2,z3,z4,z5,z223])],[(0,[z1,z2,z3,z1159,z5,z6]),(0,[z1,z2,z72,z5,z6,z24]),(0,[z98,z2,z3,z4,z77,z6]),(0,[z135,z1,z2,z3,z169,z4])],[(0,[z1,z2,z3,z1160,z5,z6]),(0,[z1,z2,z72,z4,z210,z6]),(0,[z1,z2,z3,z4,z1161,z6]),(0,[z1,z2,z3,z267,z37,z6]),(0,[z1,z2,z3,z171,z5,z192]),(0,[z1,z2,z413,z4,z5,z16])],[(0,[z1,z2,z3,z4,z5,z1162]),(0,[z181,z1,z2,z3,z5,z192]),(0,[z1,z2,z3,z4,z67,z5]),(0,[z1,z2,z68,z44,z5,z226]),(0,[z1,z2,z257,z3,z5,z16]),(0,[z1,z2,z3,z14,z267,z6])],[(0,[z1,z2,z3,z4,z5,z1163]),(0,[z1,z2,z3,z5,z1164,z6]),(0,[z1,z1165,z3,z4,z5,z6]),(0,[z76,z2,z3,z4,z800,z6]),(0,[z43,z1,z2,z26,z5,z24]),(0,[z1,z2,z38,z4,z772,z6])],[(0,[z1,z2,z3,z4,z1166,z6]),(0,[z1,z2,z72,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1167]),(0,[z1,z20,z742,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z1168,z4,z5]),(0,[z141,z1,z2,z3,z244,z24]),(0,[z1,z2,z3,z4,z807,z6]),(0,[z1,z2,z3,z300,z5,z24]),(0,[z1,z2,z4,z5,z27,z775]),(0,[z1,z2,z3,z80,z28,z6])],[(0,[z587,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z80,z5,z24])],[(0,[z1,z2,z1169,z4,z5,z6]),(0,[z1,z2,z3,z4,z1170,z6]),(0,[z92,z2,z93,z4,z5,z24]),(0,[z1,z2,z3,z41,z5,z6])],[(0,[z1,z2,z1171,z4,z5,z6]),(0,[z1,z2,z3,z5,z445,z24]),(0,[z1,z2,z38,z4,z194,z16]),(0,[z1,z2,z46,z146,z5,z139]),(0,[z1,z2,z3,z4,z1048,z16])],[(0,[z1,z2,z3,z4,z5,z204]),(0,[z1,z1172,z3,z4,z5,z6]),(0,[z1,z2,z509,z4,z5,z139]),(0,[z1,z2,z3,z169,z44,z24])],[(0,[z1,z121,z3,z200,z5,z6]),(0,[z1,z2,z3,z272,z5,z716]),(0,[z1,z2,z3,z4,z189,z290]),(0,[z25,z1,z2,z3,z5,z299]),(0,[z1,z2,z3,z4,z5,z1173]),(0,[z1,z2,z3,z4,z5,z1174]),(0,[z1,z2,z3,z4,z798,z5]),(0,[z1,z2,z3,z28,z718,z6]),(0,[z1,z2,z3,z267,z5,z172])],[(0,[z1,z2,z3,z1175,z5,z6]),(0,[z1,z2,z3,z4,z374,z293]),(0,[z568,z2,z3,z63,z5,z6])],[(0,[z9,z1,z2,z3,z5,z16]),(0,[z1,z29,z4,z5,z273,z6]),(0,[z1,z2,z3,z4,z1176,z6])]],
   [[(0,[z1,z117,z34,z4,z5,z6]),(0,[z1,z117,z3,z264,z5,z6]),(0,[z1,z1177,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1178,z6]),(0,[z1,z2,z1029,z3,z5,z6])],[(0,[z1,z2,z3,z4,z428,z16]),(0,[z178,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z4,z438,z35]),(0,[z1,z2,z3,z339,z5,z24]),(0,[z1,z2,z46,z3,z267,z5]),(0,[z1,z2,z3,z4,z5,z1179]),(0,[z1,z2,z1180,z3,z4,z5]),(0,[z1,z2,z3,z169,z267,z24])],[(0,[z1,z2,z3,z5,z16,z192]),(0,[z1,z2,z3,z1181,z5,z6]),(0,[z1,z2,z3,z463,z5,z24]),(0,[z1,z2,z3,z4,z102,z5])],[(0,[z2,z878,z3,z4,z5,z6]),(0,[z1,z29,z4,z124,z88,z6]),(0,[z1,z329,z4,z5,z124,z6]),(0,[z1,z2,z4,z5,z775,z139])],[(0,[z1,z1182,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z374,z299]),(0,[z1,z2,z3,z4,z5,z1183]),(0,[z1,z1184,z3,z4,z5,z6]),(0,[z1,z2,z3,z1185,z5,z6]),(0,[z241,z1,z3,z4,z124,z6]),(0,[z1186,z2,z3,z4,z5,z6]),(0,[z1,z2,z1083,z4,z5,z24])],[(0,[z1,z2,z3,z47,z5,z820]),(0,[z1,z2,z3,z264,z5,z24]),(0,[z1,z2,z476,z4,z374,z6]),(0,[z1,z2,z3,z4,z310,z24]),(0,[z1,z2,z3,z4,z5,z1187])],[(0,[z1,z2,z3,z503,z5,z24]),(0,[z1,z2,z3,z519,z5,z24]),(0,[z1,z1188,z3,z4,z5,z6]),(0,[z1,z2,z3,z168,z244,z24]),(0,[z164,z2,z3,z4,z5,z53])],[(0,[z1,z2,z3,z4,z5,z290]),(0,[z1,z2,z3,z264,z5,z1015]),(0,[z92,z2,z93,z4,z5,z16]),(0,[z2,z3,z4,z5,z722,z6]),(0,[z1189,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1190,z4,z5]),(1,[z1,z3,z4,z5,z792])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 514) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 514).take 517) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1031).take 205) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1236)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [514, 517, 205] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 87).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 87).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 170).take 85).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 255).take 1).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [87, 83, 85, 1] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_39087

theorem PEqualNP.Outside.L_meta_39087 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276791464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39087.solve