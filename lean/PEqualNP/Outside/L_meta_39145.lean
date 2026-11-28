import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39145

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
  Nat.testBit (4277071594 * 2 ^ 32 + 4205502464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00000861502aae1c#64 ++ 0x2000010c2a0555c3#64 ++ 0xf82458e3f07ffe3f#64 ++ 0xdf048b1c7e0fffc7#64 : BitVec 256),
   (0x10498b2ccc6666c1#64 ++ 0x42093165998cccd8#64 ++ 0xf0dbaf3ccc6667c7#64 ++ 0xbe1b75e7998cccf8#64 : BitVec 256),
   (0x0b1c303705878369#64 ++ 0x81638606e0b0f06d#64 ++ 0x9f1c303f0f8787ff#64 ++ 0x73e38607e1f0f0ff#64 : BitVec 256),
   (0x25e03dc00af805b6#64 ++ 0x04bc07b8015f00b6#64 ++ 0xafe03fc00ff807fe#64 ++ 0xf5fc07f801ff00ff#64 : BitVec 256),
   (0x06fec0000f555000#64 ++ 0x00dfd80001eaaa00#64 ++ 0xcfffc0000ffff805#64 ++ 0xf9fff80001ffff00#64 : BitVec 256),
   (0x07b7769aa0000000#64 ++ 0x00f6eed354000000#64 ++ 0xf7fffffff0000003#64 ++ 0xfefffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0xf02458e3f0000003 0xde048b1c7e000000

def z1 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xf82458e3f07ffe3f 0xdf048b1c7e0fffc7

def z2 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xffffd8e3fffff807 0xfffffb1c7fffff00

def z3 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xf7fffffff0000003 0xfefffffffe000000

def z4 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x9f1c303f0f8787ff 0x73e38607e1f0f0ff

def z5 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0dbaf3ccc6667c7 0xbe1b75e7998cccf8

def z6 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xafe03fc00ff807fe 0xf5fc07f801ff00ff

def z7 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xcfffc0000ffff805 0xf9fff80001ffff00

def z8 : W := mkw 0x1009820c84044041 0x4201304190808808 0x001b801c00000000 0x0003700380000000

def z9 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x00dba71c0c0001c0 0x201b74e381800038

def z10 : W := mkw 0x0101369aa0000000 0x002026d354000000 0x30003ffff0000002 0x060007fffe000000

def z11 : W := mkw 0x07fff69aaf555000 0x00fffed355eaaa00 0xfffffffffffff807 0xffffffffffffff00

def z12 : W := mkw 0x06b74688a0000000 0x00d6e8d114000000 0xe7ffcfc0f0000001 0xfcfff9f81e000000

def z13 : W := mkw 0x104889655c6eeedd 0x6209112cab8ddddb 0xf82458e3fc7fffff 0xdf048b1c7f8fffff

def z14 : W := mkw 0x29003df700aa87ff 0x852007bee01550ff 0x30003fff000007fa 0x060007ffe00000ff

def z15 : W := mkw 0x0101369aa0000000 0x002026d354000000 0xf0247ffff0000003 0xde048ffffe000000

def z16 : W := mkw 0x05a0348000000000 0x00b4069000000000 0xa7e03fc000000002 0xf4fc07f800000000

def z17 : W := mkw 0x0800003700028249 0x81000006e0005049 0x1000003f00000000 0x02000007e0000000

def z18 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x700458e3f007fe3b 0x0e008b1c7e00ffc7

def z19 : W := mkw 0x0001020880000000 0x0000204110000000 0x501b803cc0000001 0x0a03700798000000

def z20 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x2fe01fc003f80038 0xc5fc03f8007f0007

def z21 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x0fc027000ff807fc 0x21f804e001ff00ff

def z22 : W := mkw 0x0b1c387755afaf7d 0xa163870eeab5f5ef 0xff3c78ffffffffff 0xffe78f1fffffffff

def z23 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z24 : W := mkw 0x07f7f69aaa505000 0x00fefed3554a0a00 0xf7fffffff0787803 0xfefffffffe0f0f00

def z25 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xf00018e3f066663f 0x9e00031c7e0cccc7

def z26 : W := mkw 0x0314301200000000 0x0062860240000000 0x971c303f00000003 0x72e38607e0000000

def z27 : W := mkw 0x04a34688a0000000 0x009468d114000000 0x60e3cfc0f0000000 0x8c1c79f81e000000

def z28 : W := mkw 0x0000084000280414 0x0000010800050082 0xa82018c00078063e 0xd5040318000f00c7

def z29 : W := mkw 0x25e035800ad001a2 0x04bc06b0015a0034 0x07c027000f8001c0 0x20f804e001f00038

def z30 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x702448e3f07ff801 0x8e04891c7e0fff00

def z31 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x1f1c103f03878039 0x43e38207e070f007

def z32 : W := mkw 0x0b1c3077158f8b7d 0xa163860ee2b1f16f 0x9f3c70ff3f9f9fff 0x73e78e1fe7f3f3ff

def z33 : W := mkw 0x06fec0000c444000 0x00dfd80001888800 0xc7ffc0000c666005 0xf8fff800018ccc00

def z34 : W := mkw 0x04e880000e544000 0x009d100001ca8800 0xcffb80000ffe6005 0xf9ff700001ffcc00

def z35 : W := mkw 0x0008082444262641 0x000101048884c4c8 0xf018283ccc6667c7 0xbe030507998cccf8

def z36 : W := mkw 0x204009400af805b6 0x04080128015f00b6 0x080000000ff807fc 0x0100000001ff00ff

def z37 : W := mkw 0x25e03de15afaafbe 0x24bc07bc2b5f55f7 0xffe47fe3ffffffff 0xfffc8ffc7fffffff

def z38 : W := mkw 0x0fbf76bfa5878369 0x81f7eed7f4b0f06d 0xffffffffff8787ff 0xfffffffffff0f0ff

def z39 : W := mkw 0x27f77fdaaaf805b6 0x04feeffb555f00b6 0xfffffffffff807ff 0xffffffffffff00ff

def z40 : W := mkw 0x0008002404060241 0x000100048080c048 0x9018203c0c0607c7 0x320304078180c0f8

def z41 : W := mkw 0x07b6749220000000 0x00f6ce9244000000 0x072450c330000000 0x40e48a1866000000

def z42 : W := mkw 0x0b14387351abaf3c 0xa162870e6a3575e7 0xff2458e3f3fffe3f 0xdfe48b1c7e7fffc7

def z43 : W := mkw 0x004880000f555000 0x0009100001eaaa00 0x080000000ffff804 0x0100000001ffff00

def z44 : W := mkw 0x0040010008400080 0x0008002001080010 0x00c027000c0001c0 0x201804e001800038

def z45 : W := mkw 0x3149bfecccee67f7 0x462937fd999dccfe 0xf0dbbffccc6667ff 0xbe1b77ff998cccff

def z46 : W := mkw 0x0a1c003705078249 0x81438006e0a0f049 0x101c003f00078001 0x02038007e000f000

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0xc8244000007ff805 0xd9048800000fff00

def z48 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xdf3c703f0fffffff 0xfbe78e07e1ffffff

def z49 : W := mkw 0x06b6400000000000 0x00d6c80000000000 0x07db800000000000 0x20fb700000000000

def z50 : W := mkw 0x0000002100028208 0x0000000420005041 0x980410230007863f 0x530082046000f0c7

def z51 : W := mkw 0x0000082040222600 0x00000104080444c0 0xf0000820c0666607 0x9e000104180cccc0

def z52 : W := mkw 0x10418b48d8686c94 0x620831691b0d0d92 0x60e3cfc0f0787800 0x8c1c79f81e0f0f00

def z53 : W := mkw 0x0a1c002505878369 0x81438004a0b0f06d 0x8f1c00000f8787fd 0x71e3800001f0f0ff

def z54 : W := mkw 0x04a2448020000000 0x0094489004000000 0x002040c030000000 0x0004081806000000

def z55 : W := mkw 0x025ec0000f555000 0x004bd80001eaaa00 0x481fc0000ffff805 0x0903f80001ffff00

def z56 : W := mkw 0x0fb7769ba1818128 0x81f6eed374303025 0xfffffffff381803b 0xfffffffffe703007

def z57 : W := mkw 0x031c301205050000 0x0063860240a0a000 0x9f1c303f0f878007 0x73e38607e1f0f000

def z58 : W := mkw 0x0100301200000000 0x0020060240000000 0x1000303f00000002 0x02000607e0000000

def z59 : W := mkw 0x0040000008400000 0x0008000001080000 0x80c000000c600004 0xb0180000018c0000

def z60 : W := mkw 0x10098a6dd42eee5d 0x6201314dba85ddcb 0xf83fd8fff07ffe3f 0xdf07fb1ffe0fffc7

def z61 : W := mkw 0x27fefdc00ffd55b6 0x04ffdfb801ffaab6 0xaffbbfc00ff807fe 0xf5ff77f801ff00ff

def z62 : W := mkw 0x35e9bfcc8efc45f7 0x46bd37f991df88be 0xaffbbfdc0ff807fe 0xf5ff77fb81ff00ff

def z63 : W := mkw 0x04e009000a700480 0x009c0120014e0090 0xafe02f000ff807c6 0xf5fc05e001ff00f8

def z64 : W := mkw 0x0009022c84060241 0x000120459080c048 0xf0dbaf3ccc0607c7 0xbe1b75e79980c0f8

def z65 : W := mkw 0x004809240c6606c1 0x00090124818cc0d8 0xb0d82f3c0c6607c7 0xb61b05e7818cc0f8

def z66 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x300018e3f000063a 0x0600031c7e0000c7

def z67 : W := mkw 0x21003dc000a805b6 0x042007b8001500b6 0x20003fc0000007fa 0x040007f8000000ff

def z68 : W := mkw 0x27fefdc00ffd55b6 0x04ffdfb801ffaab6 0xefffffc00fffffff 0xfdfffff801ffffff

def z69 : W := mkw 0x021ec00005055000 0x0043d80000a0aa00 0x401fc0000007f801 0x0803f8000000ff00

def z70 : W := mkw 0x0b1ef0370587d369 0x8163de06e0b0fa6d 0xdf1ff03f0f87ffff 0x7be3fe07e1f0ffff

def z71 : W := mkw 0x04e000000a500000 0x009c0000014a0000 0x8fe000000ff80004 0xf1fc000001ff0000

def z72 : W := mkw 0x0900303700828369 0x81200606e010506d 0x1000303f000007fa 0x02000607e00000ff

def z73 : W := mkw 0x0908302505878369 0x81210604a0b0f06d 0x8f0030000f8787fe 0x71e0060001f0f0ff

def z74 : W := mkw 0x304889644efe67f7 0x4609112c89dfccfe 0x080000000ffe67fc 0x0100000001ffccff

def z75 : W := mkw 0x35e9bfeddefeefff 0x66bd37fdbbdfddff 0xffffffffffffffff 0xffffffffffffffff

def z76 : W := mkw 0x000000215002aa08 0x200000042a005541 0x50044023f007f801 0x0a0088047e00ff00

def z77 : W := mkw 0x01013efbf02aae1c 0x202027df7e0555c3 0xf8247ffff07ffe3f 0xdf048ffffe0fffc7

def z78 : W := mkw 0x1b5cb9374de7e7e9 0xc36b9726e9bcfcfd 0x9f1c303f0fe7e7ff 0x73e38607e1fcfcff

def z79 : W := mkw 0x00400961586aae9c 0x2008012c2b0d55d3 0xf8e47fe3fc7fffff 0xff1c8ffc7f8fffff

def z80 : W := mkw 0x35e9bfeccefe67f7 0x46bd37fd99dfccfe 0xfffbbffccffe67ff 0xffff77ff99ffccff

def z81 : W := mkw 0x07fff69aaf555000 0x00fffed355eaaa00 0xcfffe71c0ffff805 0xf9fffce381ffff00

def z82 : W := mkw 0x10498b2dcc66e6c9 0x42093165b98cdcd9 0xf8dfbf3fcc67e7ff 0xff1bf7e7f98cfcff

def z83 : W := mkw 0x0fbe703705878369 0x81f7ce06e0b0f06d 0xdffff03f0f8787ff 0xfbfffe07e1f0f0ff

def z84 : W := mkw 0x0fbe74b725878369 0x81f7ce96e4b0f06d 0x9f3c70ff3f8787ff 0x73e78e1fe7f0f0ff

def z85 : W := mkw 0x0100300000800120 0x0020060000100024 0x8f0030000f8007fe 0x71e0060001f000ff

def z86 : W := mkw 0x06fec8400f7d5414 0x00dfd90801efaa82 0xefffd8c00ffffe3f 0xfdfffb1801ffffc7

def z87 : W := mkw 0x21003dc000a805b6 0x042007b8001500b6 0xaf003fc00f8007fe 0x75e007f801f000ff

def z88 : W := mkw 0x0b1f723fa5878369 0x8163ee47f4b0f06d 0xdf1ff03fff8787ff 0x7be3fe07fff0f0ff

def z89 : W := mkw 0x2ffc3df70fff87ff 0x85ff87bee1fff0ff 0xbffc3fff0fff87ff 0xf7ff87ffe1fff0ff

def z90 : W := mkw 0x06fec8615f7ffe1c 0x20dfd90c2befffc3 0xffffd8e3fffffe3f 0xfffffb1c7fffffc7

def z91 : W := mkw 0x000000411008881c 0x2000000822011103 0x000010c330000038 0x0000021866000007

def z92 : W := mkw 0x1001030c800000c1 0x4200206190000018 0x0000271c000001c0 0x000004e380000038

def z93 : W := mkw 0x0216400000000000 0x0042c80000000000 0x401fc00000000001 0x0803f80000000000

def z94 : W := mkw 0x0002c00000005000 0x0000580000000a00 0x4003c00000007800 0x0800780000000f00

def z95 : W := mkw 0x05a0348000800120 0x00b4069000100024 0xafe03fc00f8007fe 0xf5fc07f801f000ff

def z96 : W := mkw 0x04e880000f555000 0x009d100001eaaa00 0x8fe000000ffff804 0xf1fc000001ffff00

def z97 : W := mkw 0x0140390008e005a0 0x00280720011c00b4 0xafc03f000fe007fe 0xf5f807e001fc00ff

def z98 : W := mkw 0x1b5dbb3fcde7e7e9 0xc36bb767f9bcfcfd 0xffdfbf3fcfe7e7ff 0xfffbf7e7f9fcfcff

def z99 : W := mkw 0x021ec00005055000 0x0043d80000a0aa00 0xcf1fc0000f87f805 0x79e3f80001f0ff00

def z100 : W := mkw 0x000000215002aa08 0x200000042a005541 0x10000023f0000000 0x020000047e000000

def z101 : W := mkw 0x0ffef0370fd7d369 0x81ffde06e1fafa6d 0xdffff03f0fffffff 0xfbfffe07e1ffffff

def z102 : W := mkw 0x0908303705878369 0x81210606e0b0f06d 0x1800303f0f8787fe 0x03000607e1f0f0ff

def z103 : W := mkw 0x07bf769aa5050000 0x00f7eed354a0a000 0xffffffffff878007 0xfffffffffff0f000

def z104 : W := mkw 0x25a034c002980136 0x04b4069800530026 0x0f2010c003980038 0x41e4021800730007

def z105 : W := mkw 0x104889244c6666c1 0x42091124898cccd8 0x000000000c6667c4 0x00000000018cccf8

def z106 : W := mkw 0x0000084050282c14 0x200001080a050582 0x602048c0f0787800 0x8c0409181e0f0f00

def z107 : W := mkw 0x0001020880000000 0x0000204110000000 0xf0dbaf3cc0000003 0xbe1b75e798000000

def z108 : W := mkw 0x0b14301301818128 0x8162860260303025 0x0f04100303818038 0x41e0820060703007

def z109 : W := mkw 0x104889244c6666c1 0x42091124898cccd8 0xf0000820cc6667c7 0x9e000104198cccf8

def z110 : W := mkw 0x1041830888404080 0x4208306111080810 0x00c3870000000000 0x001870e000000000

def z111 : W := mkw 0x06b6400000000000 0x00d6c80000000000 0xc7ffc00000000001 0xf8fff80000000000

def z112 : W := mkw 0x10010b2cc02226c1 0x42002165980444d8 0xf0dbaf3cc00007c3 0xbe1b75e7980000f8

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0x8804000000078005 0x510080000000f000

def z114 : W := mkw 0x1049832ccc4662c1 0x420930659988cc58 0x50dba73ccc0661c1 0x2a1b74e79980cc38

def z115 : W := mkw 0x06b6400003111000 0x00d6c80000622200 0x0f24400003999800 0x41e4880000733300

def z116 : W := mkw 0x16ffcb2ccf7776c1 0x42dff96599eeeed8 0xffffef3ccfffffc7 0xfffffde799fffff8

def z117 : W := mkw 0x07bff69aa5055000 0x00f7fed354a0aa00 0xf7fffffff007f803 0xfefffffffe00ff00

def z118 : W := mkw 0x27fef4c00fdd5136 0x04ffde9801fbaa26 0xcfffd0c00ffff83d 0xf9fffa1801ffff07

def z119 : W := mkw 0x10010b2cc02226c1 0x42002165980444d8 0x30002f3cc00007c2 0x060005e7980000f8

def z120 : W := mkw 0x25e8bdc00ffd55b6 0x04bd17b801ffaab6 0xafe03fc00ffffffe 0xf5fc07f801ffffff

def z121 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x382458e3f0199e3a 0x47048b1c7e0333c7

def z122 : W := mkw 0x04e2c0000a505000 0x009c5800014a0a00 0x40e3c00000787800 0x881c7800000f0f00

def z123 : W := mkw 0x07b6701200000000 0x00f6ce0240000000 0xd7fff03f00000003 0xfafffe07e0000000

def z124 : W := mkw 0x004880000c444000 0x0009100001888800 0xc0db80000c666005 0xb81b7000018ccc00

def z125 : W := mkw 0x0fbe703707979369 0x81f7ce06e0f2f26d 0x9f3c703f0f9f9fff 0x73e78e07e1f3f3ff

def z126 : W := mkw 0x0908303704868369 0x81210606e090d06d 0x9018303f0c0607ff 0x32030607e180c0ff

def z127 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xb82018e3f078063e 0xd704031c7e0f00c7

def z128 : W := mkw 0x0000084000280414 0x0000010800050082 0x080000000078063c 0x01000000000f00c7

def z129 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x8ffb80000ff80004 0xf1ff700001ff0000

def z130 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x07fff7df30000000 0x60fffefbe6000000

def z131 : W := mkw 0x10498b2ccf7776c1 0x4209316599eeeed8 0xf8dbaf3ccfffffc7 0xbf1b75e799fffff8

def z132 : W := mkw 0x06bec00007155000 0x00d7d80000e2aa00 0x4f3fc000039ff801 0x49e7f8000073ff00

def z133 : W := mkw 0x000000215002aa08 0x200000042a005541 0xf02458e3f007f803 0xde048b1c7e00ff00

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0x400440000007f801 0x080088000000ff00

def z135 : W := mkw 0x0100300000800120 0x0020060000100024 0x070020000f8001c0 0x20e0040001f00038

def z136 : W := mkw 0x0008000404040041 0x0001000080808008 0x0018201c0c0001c0 0x2003040381800038

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000000666005 0x98000000000ccc00

def z138 : W := mkw 0x0b1c301605850161 0x81638602c0b0a02c 0x971c303f0f8001c3 0x72e38607e1f00038

def z139 : W := mkw 0x0ffef0160fd55161 0x81ffde02c1faaa2c 0xcfffe01c0ffff9c5 0xf9fffc0381ffff38

def z140 : W := mkw 0x004880000c444000 0x0009100001888800 0xc8ffc0000c7ff805 0xf91ff800018fff00

def z141 : W := mkw 0x35e1bfc8caf865b6 0x46bc37f9195f0cb6 0xefe3bfc0cff867fe 0xfdfc77f819ff0cff

def z142 : W := mkw 0x0217421aa0000000 0x0042e84354000000 0x001b801c00000000 0x0003700380000000

def z143 : W := mkw 0x0001020880000000 0x0000204110000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z144 : W := mkw 0x0008800005055000 0x0001100000a0aa00 0x000000000007f800 0x000000000000ff00

def z145 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x702058e3f0787e3a 0x8e040b1c7e0f0fc7

def z146 : W := mkw 0x021c000005050000 0x0043800000a0a000 0x001c000000078001 0x000380000000f000

def z147 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x0f18201c0f8787fc 0x21e3040381f0f0ff

def z148 : W := mkw 0x07b77efbf02aae1c 0x20f6efdf7e0555c3 0xfffffffff07ffe3f 0xfffffffffe0fffc7

def z149 : W := mkw 0x25e03dc05af82db6 0x24bc07b80b5f05b6 0xefe07fc0fff87ffe 0xfdfc0ff81fff0fff

def z150 : W := mkw 0x0b1c301605850161 0x81638602c0b0a02c 0x8f1c201c0f8781c5 0x71e3840381f0f038

def z151 : W := mkw 0x04e2c0000a505000 0x009c5800014a0a00 0x00c3800000000000 0x0018700000000000

def z152 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x07dba71c00000000 0x20fb74e380000000

def z153 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x8fdf80000f878005 0x71fbf00001f0f000

def z154 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x0fffc0000f999800 0x61fff80001f33300

def z155 : W := mkw 0x000000411008881c 0x2000000822011103 0x082450c330199838 0x41048a1866033307

def z156 : W := mkw 0x0b1c301605850161 0x81638602c0b0a02c 0x8f18301c0f8007fe 0x71e3060381f000ff

def z157 : W := mkw 0x17ffffbeec6666c1 0x42fffff7dd8cccd8 0xf7fffffffc6667c7 0xfeffffffff8cccf8

def z158 : W := mkw 0x06b7469aa0000000 0x00d6e8d354000000 0x70ffcffff0000001 0x8e1ff9fffe000000

def z159 : W := mkw 0x1009822cc4066241 0x420130459880cc48 0x501b803cc0066001 0x0a0370079800cc00

def z160 : W := mkw 0x021c000005050000 0x0043800000a0a000 0x8f1c00000f878005 0x71e3800001f0f000

def z161 : W := mkw 0x0100386150aaaf3c 0x2020070c2a1555e7 0xff2478e3ffffffff 0xffe48f1c7fffffff

def z162 : W := mkw 0x24e00de15a7aae9e 0x249c01bc2b4f55d3 0xf8e45fe3f07ffe3f 0xdf1c8bfc7e0fffc7

def z163 : W := mkw 0x1040890048606480 0x42081120090c0c90 0x0000000000606000 0x00000000000c0c00

def z164 : W := mkw 0x31013fecc0aa27f7 0x462027fd981544fe 0x30003ffcc00007fa 0x060007ff980000ff

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z166 : W := mkw 0x1008802444066241 0x420110048880cc48 0x0000000000066000 0x000000000000cc00

def z167 : W := mkw 0x25e2fdc00af855b6 0x04bc5fb8015f0ab6 0xefe3ffc00ff87ffe 0xfdfc7ff801ff0fff

def z168 : W := mkw 0x02174a7bf02aae1c 0x2042e94f7e0555c3 0xf83fd8fff07ffe3f 0xdf07fb1ffe0fffc7

def z169 : W := mkw 0x004888204c666600 0x00091104098cccc0 0xf0db8820cc666607 0xbe1b7104198cccc0

def z170 : W := mkw 0x10498b6ccc6e66d5 0x4209316d998dccda 0xf8fbbffccc7e67ff 0xff1f77ff998fccff

def z171 : W := mkw 0x0fbf7efff5afaf7d 0xa1f7efdffeb5f5ef 0xffffffffffffffff 0xffffffffffffffff

def z172 : W := mkw 0x0b1c301605850161 0x81638602c0b0a02c 0x0718201c0f8001c0 0x20e3040381f00038

def z173 : W := mkw 0x27fef5800fd551a2 0x04ffdeb001faaa34 0xcfffe7000ffff9c5 0xf9fffce001ffff38

def z174 : W := mkw 0x35e8bde44efe67f7 0x46bd17bc89dfccfe 0xafe03fc00ffe67fe 0xf5fc07f801ffccff

def z175 : W := mkw 0x04e2c8615a7afe1c 0x209c590c2b4f5fc3 0xf8e7d8e3f07ffe3f 0xdf1cfb1c7e0fffc7

def z176 : W := mkw 0x0808002505878369 0x81010004a0b0f06d 0x9818203c0f8787ff 0x3303040781f0f0ff

def z177 : W := mkw 0x10498b6cdc6e6ed5 0x6209316d9b8dcdda 0xf0fbeffcfc7e7fc7 0xbe1f7dff9f8fcff8

def z178 : W := mkw 0x25e03de15afaafbe 0x24bc07bc2b5f55f7 0xafe03fc00ffffffe 0xf5fc07f801ffffff

def z179 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xff3c78ffff8787ff 0xffe78f1ffff0f0ff

def z180 : W := mkw 0x16ffc30c8f5550c1 0x42dff86191eaaa18 0xcfffe71c0ffff9c5 0xf9fffce381ffff38

def z181 : W := mkw 0x0217421aa0000000 0x0042e84354000000 0x501fc03ff0000001 0x0a03f807fe000000

def z182 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x1718303f0f8007fa 0x22e30607e1f000ff

def z183 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x07db80000f800000 0x20fb700001f00000

def z184 : W := mkw 0x0b1c303605870361 0x81638606c0b0e06c 0x9718203c0f8607c7 0x32e3040781f0c0f8

def z185 : W := mkw 0x10000924402226c1 0x42000124880444d8 0x00000000000007c0 0x00000000000000f8

def z186 : W := mkw 0x00010688a0000000 0x000020d114000000 0x20000fc0f0000000 0x040001f81e000000

def z187 : W := mkw 0x25a034c002980136 0x04b4069800530026 0xafe03fc00398003a 0xf5fc07f800730007

def z188 : W := mkw 0x06fec9000f755480 0x00dfd92001eeaa90 0xefffef000fffffc7 0xfdfffde001fffff8

def z189 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x27c03fc00f8007fa 0x24f807f801f000ff

def z190 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xffe47fe3fff807ff 0xfffc8ffc7fff00ff

def z191 : W := mkw 0x24e00dc00a780496 0x049c01b8014f0092 0x20e00fc000780000 0x841c01f8000f0000

def z192 : W := mkw 0x10418b08c8606480 0x42083161190c0c90 0x60c38f00c0606000 0x8c1871e0180c0c00

def z193 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xf7dbaf3cc0000003 0xbefb75e798000000

def z194 : W := mkw 0x21403dc008e805b6 0x042807b8011d00b6 0xa0c03fc00c6007fe 0xb41807f8018c00ff

def z195 : W := mkw 0x1a1d823fc507e249 0xc343b047f8a0fc49 0x501f803fc007e001 0x0a03f007f800fc00

def z196 : W := mkw 0x0a1c003705078249 0x81438006e0a0f049 0x901c203f0c0787c7 0x32038407e180f0f8

def z197 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xfffffffff07ff807 0xfffffffffe0fff00

def z198 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x08000000007ffe3c 0x01000000000fffc7

def z199 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf8dbaf3ccc7fffff 0xbf1b75e7998fffff

def z200 : W := mkw 0x031c303604060241 0x00638606c080c048 0x971c303f0c0607c7 0x72e38607e180c0f8

def z201 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf0dbbffffc6667ff 0xbe1b77ffff8cccff

def z202 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0xc0dba71c0c6661c5 0xb81b74e3818ccc38

def z203 : W := mkw 0x25e8bdc00efc45b6 0x04bd17b801df88b6 0xeffbbfc00ffe67ff 0xfdff77f801ffccff

def z204 : W := mkw 0x210034c000880136 0x0420069800110026 0x000010c000000038 0x0000021800000007

def z205 : W := mkw 0x0214001200000000 0x0042800240000000 0x101c003f00000001 0x02038007e0000000

def z206 : W := mkw 0x07fef4922f555000 0x00ffde9245eaaa00 0xcfffd0c33ffff805 0xf9fffa1867ffff00

def z207 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x0fdb80000ffff804 0x21fb700001ffff00

def z208 : W := mkw 0x06b6400003111000 0x00d6c80000622200 0xcfffc00003999801 0xf9fff80000733300

def z209 : W := mkw 0x24e34fc8aa780496 0x049c69f9154f0092 0x60e3cfc0f0780000 0x8c1c79f81e0f0000

def z210 : W := mkw 0x06bec00005055000 0x00d7d80000a0aa00 0xc7ffc0000007f801 0xf8fff8000000ff00

def z211 : W := mkw 0x07f77f9aa8600480 0x00feeff3550c0090 0xf7fffffffc6007c7 0xfeffffffff8c00f8

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0x0824400000199800 0x4104880000033300

def z213 : W := mkw 0x07b776bba0028208 0x00f6eed774005041 0xfffffffff007863f 0xfffffffffe00f0c7

def z214 : W := mkw 0x0000000000000000 0x0000000000000000 0x8820000000780004 0xd1040000000f0000

def z215 : W := mkw 0x25e03dc11af88dbe 0x24bc07b8235f11b7 0xafe47fc33ff99ffe 0xf5fc8ff867ff33ff

def z216 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x171c203f0f8781c1 0x22e38407e1f0f038

def z217 : W := mkw 0x10010b08c0202480 0x4200216118040490 0x20000f00c0000000 0x040001e018000000

def z218 : W := mkw 0x04e3c688aa505000 0x009c78d1154a0a00 0x60e3cfc0f0787800 0x8c1c79f81e0f0f00

def z219 : W := mkw 0x04a2400002101000 0x0094480000420200 0x0020400000181800 0x0004080000030300

def z220 : W := mkw 0x06be400007151000 0x00d7c80000e2a200 0x8f3c40000f9f9805 0x71e7880001f3f300

def z221 : W := mkw 0x05a1369aa0000000 0x00b426d354000000 0xb7e03ffff0000002 0xf6fc07fffe000000

def z222 : W := mkw 0x0000000000000000 0x0000000000000000 0x800020000c0007c6 0x30000400018000f8

def z223 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x37dbbffff0000002 0x26fb77fffe000000

def z224 : W := mkw 0x0a1c001605050041 0x81438002c0a0a008 0x0018001c00000000 0x0003000380000000

def z225 : W := mkw 0x104881040c4440c1 0x4209102081888818 0x000000000c0001c0 0x0000000001800038

def z226 : W := mkw 0x1b5db33f8dc7c3e9 0xc36bb667f1b8f87d 0x9fdfb73f0f8787ff 0x73fbf6e7e1f0f0ff

def z227 : W := mkw 0x06b6400000000000 0x00d6c80000000000 0x0724400000000000 0x40e4880000000000

def z228 : W := mkw 0x004982088c444000 0x0009304111888800 0xf0dbaf3ccc666007 0xbe1b75e7998ccc00

def z229 : W := mkw 0x0b14303701838369 0x81628606e030706d 0x1f04303f038187fa 0x43e08607e07030ff

def z230 : W := mkw 0x0000080040202400 0x0000010008040480 0x60000800c0606000 0x8c000100180c0c00

def z231 : W := mkw 0x1949bb3fcce6e7e9 0xc3293767f99cdcfd 0xf0dbbf3fcc6667ff 0xbe1b77e7f98cccff

def z232 : W := mkw 0x125fcb3eec6666c1 0x424bf967dd8cccd8 0xf0dfef3ffc6667c7 0xbe1bfde7ff8cccf8

def z233 : W := mkw 0x204009400a780496 0x04080128014f0092 0x0000000000780000 0x00000000000f0000

def z234 : W := mkw 0x184889254de7e7e9 0xc3091124a9bcfcfd 0x080000000fe7e7fc 0x0100000001fcfcff

def z235 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0fffffffc6667c7 0xfe1fffffff8cccf8

def z236 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xf02458e3f000063b 0xde048b1c7e0000c7

def z237 : W := mkw 0x0000000000000000 0x0000000000000000 0x9018203c00000003 0x3203040780000000

def z238 : W := mkw 0x0100349220000000 0x0020069244000000 0x000010c330000000 0x0000021866000000

def z239 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x573fd0fff0000001 0x4ae7fa1ffe000000

def z240 : W := mkw 0x204009400af805b6 0x04080128015f00b6 0xa82018c00ff807fe 0xd504031801ff00ff

def z241 : W := mkw 0x04e2c0000a505000 0x009c5800014a0a00 0xc8e7c000007ff805 0xd91cf800000fff00

def z242 : W := mkw 0x10498b2ddc66eec9 0x62093165bb8cddd9 0xf0dfef3ffc67ffc7 0xbe1bfde7ff8cfff8

def z243 : W := mkw 0x0fbf769ea5850161 0x81f7eed3d4b0a02c 0xf7ffffffff8001c3 0xfefffffffff00038

def z244 : W := mkw 0x07b6749223111000 0x00f6ce9244622200 0x0f2450c333999800 0x41e48a1866733300

def z245 : W := mkw 0x0a1f423fa5078249 0x8143e847f4a0f049 0x501fc03ff0078001 0x0a03f807fe00f000

def z246 : W := mkw 0x00080865542eae5d 0x2001010caa85d5cb 0xf83c78fffc7fffff 0xff078f1fff8fffff

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0x602048c0f0000000 0x8c0409181e000000

def z248 : W := mkw 0x004880000c444000 0x0009100001888800 0x00db80000c000000 0x201b700001800000

def z249 : W := mkw 0x0b14303700828369 0x81628606e010506d 0x971c303f000007fb 0x72e38607e00000ff

def z250 : W := mkw 0x07b7769aa3111000 0x00f6eed354622200 0xfffffffff3999803 0xfffffffffe733300

def z251 : W := mkw 0x25e035800ad001a2 0x04bc06b0015a0034 0xa7e03fc00f8001c2 0xf4fc07f801f00038

def z252 : W := mkw 0x16fec9244f7776c1 0x42dfd92489eeeed8 0xcfffc0000fffffc5 0xf9fff80001fffff8

def z253 : W := mkw 0x27b674d222980136 0x04f6ce9a44530026 0x0f2450c333980038 0x41e48a1866730007

def z254 : W := mkw 0x16ffcb6ddf7ffedd 0x62dff96dbbefffdb 0xffffffffffffffff 0xffffffffffffffff

def z255 : W := mkw 0x0b1c30375587ab69 0xa1638606eab0f56d 0xdf1c703fff87ffff 0x7be38e07fff0ffff

def z256 : W := mkw 0x0315321a80000000 0x0062a64350000000 0xf7dfbf3fc0000003 0xfefbf7e7f8000000

def z257 : W := mkw 0x06b6400000000000 0x00d6c80000000000 0xf7ffd8e3f0000003 0xfefffb1c7e000000

def z258 : W := mkw 0x0800002500828369 0x81000004a010506d 0x00000000000007f8 0x00000000000000ff

def z259 : W := mkw 0x0001021aa0000000 0x0000204354000000 0x1000003ff0000000 0x02000007fe000000

def z260 : W := mkw 0x2ffc35960fd501e3 0x85ff86b2c1faa03c 0x07d8271c0f8001c0 0x20fb04e381f00038

def z261 : W := mkw 0x25a03ce152baaf3e 0x24b4079c2a5755e7 0xff2458e3f3fffe3f 0xdfe48b1c7e7fffc7

def z262 : W := mkw 0x17fff79eac4440c1 0x42fffef3d5888818 0x07dba71c0c0001c0 0x20fb74e381800038

def z263 : W := mkw 0x0100300000800120 0x0020060000100024 0x0f00100003800038 0x41e0020000700007

def z264 : W := mkw 0x26fecdc00f7d5496 0x04dfd9b801efaa92 0xefffcfc00ffff805 0xfdfff9f801ffff00

def z265 : W := mkw 0x0ffef0160fd55161 0x81ffde02c1faaa2c 0x07dba01c0f8001c0 0x20fb740381f00038

def z266 : W := mkw 0x2ffefdf70fffd7ff 0x85ffdfbee1fffaff 0xffffffff0fffffff 0xffffffffe1ffffff

def z267 : W := mkw 0x0b1c301305858128 0x8163860260b0b025 0x8f1c10030f87803d 0x71e3820061f0f007

def z268 : W := mkw 0x1b1db23fc587e369 0xc363b647f8b0fc6d 0xdf1fb03fcf87e7ff 0x7be3f607f9f0fcff

def z269 : W := mkw 0x21003de150aaafbe 0x242007bc2a1555f7 0x30003fe3f00007fa 0x060007fc7e0000ff

def z270 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x27e02fc00ff801c0 0xa4fc05f801ff0038

def z271 : W := mkw 0x07fff69aac444000 0x00fffed355888800 0xf7fffffffc666007 0xfeffffffff8ccc00

def z272 : W := mkw 0x204009615afaafbe 0x2408012c2b5f55f7 0xf82458e3ffffffff 0xdf048b1c7fffffff

def z273 : W := mkw 0x284809650fff87ff 0x8509012ca1fff0ff 0x080000000fff87fc 0x0100000001fff0ff

def z274 : W := mkw 0x0b1430531189893c 0xa162860a62313127 0x0f2450c333999838 0x41e48a1866733307

def z275 : W := mkw 0x14e3cf88e8606480 0x429c79f11d0c0c90 0x60e3cfc0f0606000 0x8c1c79f81e0c0c00

def z276 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf8ffef3ccc7fffc7 0xff1ffde7998ffff8

def z277 : W := mkw 0x2fb434d30399813e 0x85f6869a60733027 0x0f2410c303998038 0x41e4821860733007

def z278 : W := mkw 0x07b6748000000000 0x00f6ce9000000000 0xe7ffffc000000003 0xfcfffff800000000

def z279 : W := mkw 0x104889655c6eeedd 0x6209112cab8ddddb 0x080000000c7ffffc 0x01000000018fffff

def z280 : W := mkw 0x07b776bbf002aa08 0x20f6eed77e005541 0xf7fffffff007f803 0xfefffffffe00ff00

def z281 : W := mkw 0x0000000003111000 0x0000000000622200 0x0800000003999800 0x0100000000733300

def z282 : W := mkw 0x21003dc000a805b6 0x042007b8001500b6 0xa8203fc0007807fe 0xd50407f8000f00ff

def z283 : W := mkw 0x0000002040022200 0x0000000408004440 0x50000020c0066001 0x0a0000041800cc00

def z284 : W := mkw 0x0808002505878369 0x81010004a0b0f06d 0x080000000f8787fc 0x0100000001f0f0ff

def z285 : W := mkw 0x2000094000a805b6 0x04000128001500b6 0x00000000000007f8 0x00000000000000ff

def z286 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x682048c0f07ffe3c 0x8d0409181e0fffc7

def z287 : W := mkw 0x10098b2cc42666c1 0x420131659884ccd8 0x701baf3cc00667c3 0x0e0375e79800ccf8

def z288 : W := mkw 0x2ffc3dd60ffd05f7 0x85ff87bac1ffa0be 0xaff83fdc0ff807fe 0xf5ff07fb81ff00ff

def z289 : W := mkw 0x06b64861502aae1c 0x20d6c90c2a0555c3 0xffffd8e3f07ffe3f 0xfffffb1c7e0fffc7

def z290 : W := mkw 0x1fffffbfede7e7e9 0xc3fffff7fdbcfcfd 0xffffffffffe7e7ff 0xfffffffffffcfcff

def z291 : W := mkw 0x06ffc2088f555000 0x00dff84111eaaa00 0xffffef3ccffff807 0xfffffde799ffff00

def z292 : W := mkw 0x0a1c003705878369 0x81438006e0b0f06d 0x181c003f0f8787fd 0x03038007e1f0f0ff

def z293 : W := mkw 0x0214000000000000 0x0042800000000000 0x871c000000000001 0x70e3800000000000

def z294 : W := mkw 0x04a34688a0000000 0x009468d114000000 0xf0fbeffcf0000003 0xbe1f7dff9e000000

def z295 : W := mkw 0x2ff43dd30bf985be 0x85fe87ba617f30b7 0xafe43fc30ff987fe 0xf5fc87f861ff30ff

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0x8f0000000f800004 0x71e0000001f00000

def z297 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x00dba71c0c6667c4 0x201b74e3818cccf8

def z298 : W := mkw 0x05e030000ad00120 0x00bc0600015a0024 0x8fe030000ff807fe 0xf1fc060001ff00ff

def z299 : W := mkw 0x204889400ffd55b6 0x0409112801ffaab6 0x080000000ffffffc 0x0100000001ffffff

def z300 : W := mkw 0x0000084050282c14 0x200001080a050582 0xf02458e3f0787803 0xde048b1c7e0f0f00

def z301 : W := mkw 0x0100302100828328 0x0020060420105065 0x9f0430230f8787ff 0x73e0860461f0f0ff

def z302 : W := mkw 0x0008800004044000 0x0001100000808800 0x401b800000066001 0x080370000000cc00

def z303 : W := mkw 0x0216401220000000 0x0042c80244000000 0x0004400330000000 0x0000880066000000

def z304 : W := mkw 0x00000860402a2614 0x0000010c080544c2 0xf82018e0c07e663f 0xdf04031c180fccc7

def z305 : W := mkw 0x04e000000a500000 0x009c0000014a0000 0x07c000000f800000 0x20f8000001f00000

def z306 : W := mkw 0x27f67dc00af805b6 0x04fecfb8015f00b6 0xefffffc00ff807ff 0xfdfffff801ff00ff

def z307 : W := mkw 0x25a03dc002b805b6 0x04b407b8005700b6 0x2f203fc0039807fa 0x45e407f8007300ff

def z308 : W := mkw 0x24e2cdc00a785496 0x049c59b8014f0a92 0x60e3cfc000787800 0x8c1c79f8000f0f00

def z309 : W := mkw 0x0a14001301018008 0x8142800260203001 0x0004000300018000 0x0000800060003000

def z310 : W := mkw 0x0040090008600480 0x00080120010c0090 0xa0c02f000c6007c6 0xb41805e0018c00f8

def z311 : W := mkw 0x21003de150aaafbe 0x242007bc2a1555f7 0xf8247fe3f07fffff 0xdf048ffc7e0fffff

def z312 : W := mkw 0x06b7421aa0000000 0x00d6e84354000000 0xd7ffc03ff0000001 0xfafff807fe000000

def z313 : W := mkw 0x10498b0ccc6464c1 0x42093161998c8c98 0x60dbaf1ccc6061c0 0xac1b75e3998c0c38

def z314 : W := mkw 0x0ffff6bfafd7d369 0x81fffed7f5fafa6d 0xffffffffffffffff 0xffffffffffffffff

def z315 : W := mkw 0x0b14303301838328 0x8162860660307065 0x9f0410230387863f 0x53e082046070f0c7

def z316 : W := mkw 0x0000090000200480 0x0000012000040090 0x20002f00000007c2 0x040005e0000000f8

def z317 : W := mkw 0x06f6c0000a505000 0x00ded800014a0a00 0xc7ffc00000787801 0xf8fff800000f0f00

def z318 : W := mkw 0x0000084000280414 0x0000010800050082 0x202008c000780000 0x84040118000f0000

def z319 : W := mkw 0x34e98fecce7e66d7 0x469d31fd99cfccda 0xf0fbaffccc7e67c7 0xbe1f75ff998fccf8

def z320 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xefe47fc00fffffff 0xfdfc8ff801ffffff

def z321 : W := mkw 0x10498b0c8c6444c1 0x42093161918c8898 0xa0dbaf1c0c6007c6 0xb41b75e3818c00f8

def z322 : W := mkw 0x07fffefbff7ffe1c 0x20ffffdf7fefffc3 0xfffffffffffffe3f 0xffffffffffffffc7

def z323 : W := mkw 0x14e3cb08ca707480 0x429c7961194e0e90 0x60e3cf00c0787800 0x8c1c79e0180f0f00

def z324 : W := mkw 0x0217421aa0000000 0x0042e84354000000 0xf03fd8fff0000003 0xde07fb1ffe000000

def z325 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x70db8f3cc0666001 0x8e1b71e7980ccc00

def z326 : W := mkw 0x04a34ec8f0282c14 0x209469d91e050582 0x60e3cfc0f0787800 0x8c1c79f81e0f0f00

def z327 : W := mkw 0x10010b6dd02aaedd 0x6200216dba0555db 0x30003ffff00007fa 0x060007fffe0000ff

def z328 : W := mkw 0x24e00dc05a782c96 0x249c01b80b4f0592 0x60e04fc0f0787800 0x8c1c09f81e0f0f00

def z329 : W := mkw 0x10090b2cc42626c1 0x420121659884c4d8 0xb0182f3ccc0607c7 0x360305e79980c0f8

def z330 : W := mkw 0x0900301600800161 0x81200602c010002c 0x0000201c000001c0 0x0000040380000038

def z331 : W := mkw 0x05a03cc000280414 0x00b4079800050082 0xafe03fc00078063e 0xf5fc07f8000f00c7

def z332 : W := mkw 0x17ffffbeec6666c1 0x42fffff7dd8cccd8 0xf7dbaf3ccc6667c7 0xbefb75e7998cccf8

def z333 : W := mkw 0x24e00dc00a780496 0x049c01b8014f0092 0xa0e02fc00c7807c6 0xb41c05f8018f00f8

def z334 : W := mkw 0x0317721aa0000000 0x0062ee4354000000 0xd71ff03ff0000003 0x7ae3fe07fe000000

def z335 : W := mkw 0x025ec0000d455000 0x004bd80001a8aa00 0xc0dfc0000c67f805 0xb81bf800018cff00

def z336 : W := mkw 0x24e005800a500082 0x049c00b0014a0010 0x00c0070000000000 0x001800e000000000

def z337 : W := mkw 0x1ffffb3fcff7f7e9 0xc3ffff67f9fefefd 0xffffff3fcfffffff 0xffffffe7f9ffffff

def z338 : W := mkw 0x0100300000800120 0x0020060000100024 0x00003000000007fa 0x00000600000000ff

def z339 : W := mkw 0x031c300005850120 0x0063860000b0a024 0x8f1c30000f8787ff 0x71e3860001f0f0ff

def z340 : W := mkw 0x15e9bfaccc6666c1 0x42bd37f5998cccd8 0xf7fbbffccc6667c7 0xfeff77ff998cccf8

def z341 : W := mkw 0x004888615c6eee1c 0x2009110c2b8dddc3 0xf8ffd8e3fc7ffe3f 0xff1ffb1c7f8fffc7

def z342 : W := mkw 0x06b6400000000000 0x00d6c80000000000 0xcfffc000007ff805 0xf9fff800000fff00

def z343 : W := mkw 0x25e03de04afa27b6 0x04bc07bc095f44f6 0xffe03fe0cffe67ff 0xfffc07fc19ffccff

def z344 : W := mkw 0x0000004000080014 0x0000000800010002 0x082010c000180038 0x4104021800030007

def z345 : W := mkw 0x125d8b2ccd6766c1 0x424bb16599acecd8 0xffdfaf3ccfe7e7c7 0xfffbf5e799fcfcf8

def z346 : W := mkw 0x0214000001010000 0x0042800000202000 0x0f04000003818000 0x41e0800000703000

def z347 : W := mkw 0x24a004c002180016 0x0494009800430002 0x002000c000180000 0x0004001800030000

def z348 : W := mkw 0x10418b08c8606480 0x42083161190c0c90 0xe0c3af00cc6067c6 0xbc1875e0198c0cf8

def z349 : W := mkw 0x06b6400003111000 0x00d6c80000622200 0x0700000003800000 0x00e0000000700000

def z350 : W := mkw 0x06b6400003111000 0x00d6c80000622200 0xcf24400003fff805 0xd9e48800007fff00

def z351 : W := mkw 0x004880240c464241 0x000910048188c848 0xd0dba03c0c6667c7 0xba1b7407818cccf8

def z352 : W := mkw 0x25e034c00ad80136 0x04bc0698015b0026 0x8fe010c00ff8003c 0xf1fc021801ff0007

def z353 : W := mkw 0x05a0348000000000 0x00b4069000000000 0x072010c000000000 0x40e4021800000000

def z354 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xc8244000007ffe3d 0xd9048800000fffc7

def z355 : W := mkw 0x0000084000280414 0x0000010800050082 0xe82458c0007ffe3f 0xdd048b18000fffc7

def z356 : W := mkw 0x2de83de50fff87ff 0x85bd07bca1fff0ff 0xafe03fc00fff87fe 0xf5fc07f801fff0ff

def z357 : W := mkw 0x104889244c6666c1 0x42091124898cccd8 0xa0c02f000c6667c6 0xb41805e0018cccf8

def z358 : W := mkw 0x10018208c0006000 0x4200304118000c00 0x40038000c0006000 0x0800700018000c00

def z359 : W := mkw 0x0000082040222600 0x00000104080444c0 0xf8244820c07ffe07 0xdf048904180fffc0

def z360 : W := mkw 0x11013fbee02226c1 0x422027f7dc0444d8 0x30003ffff00007c2 0x060007fffe0000f8

def z361 : W := mkw 0x0b1c301705858169 0x81638602e0b0b02d 0x0f1c301f0f8181f8 0x61e38603e1f0303f

def z362 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x37247ffff0000002 0x46e48ffffe000000

def z363 : W := mkw 0x07b6749220000000 0x00f6ce9244000000 0x973c70ff30000003 0x72e78e1fe6000000

def z364 : W := mkw 0x0b1c387755afaf7d 0xa163870eeab5f5ef 0xbf1c38ffff8787ff 0x77e3871ffff0f0ff

def z365 : W := mkw 0x0900303700828369 0x81200606e010506d 0x9f00303f0f8007fe 0x73e00607e1f000ff

def z366 : W := mkw 0x25e37fc8aaf805b6 0x04bc6ff9155f00b6 0xefe3ffc0fff807fe 0xfdfc7ff81fff00ff

def z367 : W := mkw 0x021ec00005055000 0x0043d80000a0aa00 0x001b800000000000 0x0003700000000000

def z368 : W := mkw 0x24e00dc00af805b6 0x049c01b8015f00b6 0x28e00fc00ff807fc 0x851c01f801ff00ff

def z369 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0c02f0000000002 0xb41805e000000000

def z370 : W := mkw 0x000000411008881c 0x2000000822011103 0xf82458e3f019983b 0xdf048b1c7e033307

def z371 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x40ffc000007ff801 0x881ff800000fff00

def z372 : W := mkw 0x0000080000200400 0x0000010000040080 0xa000080000600606 0x94000100000c00c0

def z373 : W := mkw 0x25a0348002900122 0x04b4069000520024 0x0700000003800000 0x00e0000000700000

def z374 : W := mkw 0x06b64861533bbe1c 0x20d6c90c2a6777c3 0xff2458e3f3fffe3f 0xdfe48b1c7e7fffc7

def z375 : W := mkw 0x0fb6749321818128 0x81f6ce9264303025 0x0f2450c333818038 0x41e48a1866703007

def z376 : W := mkw 0x06f6c0000b515000 0x00ded800016a2a00 0x4fe7c00003f9f800 0xc9fcf800007f3f00

def z377 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x101c303f000787fb 0x02038607e000f0ff

def z378 : W := mkw 0x0317769aa0000000 0x0062eed354000000 0x701ffffff0000003 0x0e03fffffe000000

def z379 : W := mkw 0x0efec0370f57d249 0x81dfd806e1eafa49 0xdfffc03f0ffff805 0xfbfff807e1ffff00

def z380 : W := mkw 0x34e18fc8ca786496 0x469c31f9194f0c92 0x60e38fc0c0786000 0x8c1c71f8180f0c00

def z381 : W := mkw 0x1049832c8c4642c1 0x420930659188c858 0x90dba73c0c0607c7 0x321b74e78180c0f8

def z382 : W := mkw 0x0008002504068249 0x00010004a080d049 0x981c303f0c0787ff 0x73038607e180f0ff

def z383 : W := mkw 0x0008000004040000 0x0001000000808000 0x801800000c060005 0x300300000180c000

def z384 : W := mkw 0x125fcb2ccd6776c1 0x424bf96599aceed8 0xf0dfef3ccc67ffc7 0xbe1bfde7998cfff8

def z385 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x0f2440000ffff804 0x41e4880001ffff00

def z386 : W := mkw 0x07b7769aa0800120 0x00f6eed354100024 0xffffffffff8007ff 0xfffffffffff000ff

def z387 : W := mkw 0x021ec861552ffe1c 0x2043d90c2aa5ffc3 0xf83fd8e3f07ffe3f 0xdf07fb1c7e0fffc7

def z388 : W := mkw 0x121fc22cc5077241 0x4243f84598a0ee48 0x501fc03cc007f801 0x0a03f8079800ff00

def z389 : W := mkw 0x2000004002980136 0x0400000800530026 0x0800000003980038 0x0100000000730007

def z390 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x20e03fc0007807fa 0x841c07f8000f00ff

def z391 : W := mkw 0x1b5db31e8dc541e1 0xc36bb663d1b8a83c 0x07dba71c0f8001c0 0x20fb74e381f00038

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x880010000000063e 0x51000200000000c7

def z393 : W := mkw 0x35e9b78c8ed441e3 0x46bd36f191da883c 0x07dba71c0f8001c0 0x20fb74e381f00038

def z394 : W := mkw 0x27b674c003991136 0x04f6ce9800732226 0x0f2450c003999838 0x41e48a1800733307

def z395 : W := mkw 0x26fec9400ffd55b6 0x04dfd92801ffaab6 0xcfffc0000ffffffd 0xf9fff80001ffffff

def z396 : W := mkw 0x004880000f555000 0x0009100001eaaa00 0x000000000f800000 0x0000000001f00000

def z397 : W := mkw 0x0314301200000000 0x0062860240000000 0x0718201c00000000 0x20e3040380000000

def z398 : W := mkw 0x0000000000000000 0x0000000000000000 0x002450c330000000 0x40048a1866000000

def z399 : W := mkw 0x00010a28c0222600 0x00002145180444c0 0xf0dbaf3cc0666607 0xbe1b75e7980cccc0

def z400 : W := mkw 0x000000215002aa08 0x200000042a005541 0x000000000007f800 0x000000000000ff00

def z401 : W := mkw 0x0040094008680494 0x00080128010d0092 0xa8e03fc00c7807fe 0xf51c07f8018f00ff

def z402 : W := mkw 0x25a03cc002b80536 0x04b40798005700a6 0xaf2018c003f8063e 0xd5e40318007f00c7

def z403 : W := mkw 0x0ffef0370fd7d369 0x81ffde06e1fafa6d 0x9fdfb03f0f8787ff 0x73fbf607e1f0f0ff

def z404 : W := mkw 0x04a0000002100000 0x0094000000420000 0x0f20000003980000 0x41e4000000730000

def z405 : W := mkw 0x0008002404060241 0x000100048080c048 0x1018003c00060001 0x020300078000c000

def z406 : W := mkw 0x000008214022a608 0x00000104280454c1 0xf8041823c067e63f 0xdf008304780cfcc7

def z407 : W := mkw 0x27ffffdaaffd55b6 0x04fffffb55ffaab6 0xffffffffffffffff 0xffffffffffffffff

def z408 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x60c38f00cc6667c4 0x8c1871e0198cccf8

def z409 : W := mkw 0x07bf76bea4060241 0x00f7eed7d480c048 0xf7fffffffc0607c7 0xfeffffffff80c0f8

def z410 : W := mkw 0x27f77fdaaa780496 0x04feeffb554f0092 0xf7fffffff0780003 0xfefffffffe0f0000

def z411 : W := mkw 0x0b14301301818128 0x8162860260303025 0x8f0430030f8187fe 0x71e0860061f030ff

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0x4020400000787800 0x88040800000f0f00

def z413 : W := mkw 0x0000002000020200 0x0000000400004040 0x9000002000060607 0x120000040000c0c0

def z414 : W := mkw 0x25e03d800af005a2 0x04bc07b0015e00b4 0xa7c02f000fe007c6 0xb4f805e001fc00f8

def z415 : W := mkw 0x27f67dc00bf915b6 0x04fecfb8017f22b6 0xafe47fc00ff99ffe 0xf5fc8ff801ff33ff

def z416 : W := mkw 0x0fbf769ea5850161 0x81f7eed3d4b0a02c 0x07dba71c0f8001c0 0x20fb74e381f00038

def z417 : W := mkw 0x03143873502aae1c 0x2062870e6a0555c3 0xff3c78fff07ffe3f 0xffe78f1ffe0fffc7

def z418 : W := mkw 0x3ffdbfffcfffe7ff 0xc7ffb7fff9fffcff 0xffffbfffcfffe7ff 0xfffff7fff9fffcff

def z419 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x30dbaf3ccc0007c2 0x261b75e7998000f8

def z420 : W := mkw 0x24e009400af805b6 0x049c0128015f00b6 0x8fe000000ff807fc 0xf1fc000001ff00ff

def z421 : W := mkw 0x0000084050282c14 0x200001080a050582 0xe82448c0f07ff805 0xdd0489181e0fff00

def z422 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xa82018c0007ffe3e 0xd5040318000fffc7

def z423 : W := mkw 0x07b77ebae0222600 0x00f6efd75c0444c0 0xf7fffffff0666607 0xfefffffffe0cccc0

def z424 : W := mkw 0x0000002100028208 0x0000000420005041 0xf82458e3f007863f 0xdf048b1c7e00f0c7

def z425 : W := mkw 0x0900301300808128 0x8120060260101025 0x0000100300000038 0x0000020060000007

def z426 : W := mkw 0x0000000000800120 0x0000000000100024 0x080000000f8007fc 0x0100000001f000ff

def z427 : W := mkw 0x0b1c383745a7a769 0x81638706e8b4f4ed 0xff1c383fcfe7e7ff 0xffe38707f9fcfcff

def z428 : W := mkw 0x0008000005050000 0x0001000000a0a000 0x080000000f878004 0x0100000001f0f000

def z429 : W := mkw 0x004888615f7ffe1c 0x2009110c2befffc3 0x080000000ffffe3c 0x0100000001ffffc7

def z430 : W := mkw 0x090136bfa0828369 0x812026d7f410506d 0x30003ffff00007fa 0x060007fffe0000ff

def z431 : W := mkw 0x07b776dbb008881c 0x20f6eedb76011103 0xfffffffff019983b 0xfffffffffe033307

def z432 : W := mkw 0x0b1c387705af877d 0x8163870ee0b5f0ef 0xbf3c38ff0fff87ff 0xf7e7871fe1fff0ff

def z433 : W := mkw 0x021ec00005055000 0x0043d80000a0aa00 0xc83fc000007ff805 0xd907f800000fff00

def z434 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x082450c3307ffe3c 0x41048a18660fffc7

def z435 : W := mkw 0x004080000a505000 0x00081000014a0a00 0x0000000000787800 0x00000000000f0f00

def z436 : W := mkw 0x025c80000f555000 0x004b900001eaaa00 0x8f1c00000ffff805 0x71e3800001ffff00

def z437 : W := mkw 0x10418b08c8606480 0x42083161190c0c90 0xf0dbaf3cc0606003 0xbe1b75e7980c0c00

def z438 : W := mkw 0x1009822cc4066241 0x420130459880cc48 0xf0dbaf3cc0066003 0xbe1b75e79800cc00

def z439 : W := mkw 0x06f640000b511000 0x00dec800016a2200 0x8fe440000ff99804 0xf1fc880001ff3300

def z440 : W := mkw 0x0a1c00375507aa49 0xa1438006eaa0f549 0x501c403ff007f801 0x0a038807fe00ff00

def z441 : W := mkw 0x27fc3dc00ffd05b6 0x04ff87b801ffa0b6 0xaffc3fc00fff87ff 0xf5ff87f801fff0ff

def z442 : W := mkw 0x00410b0888600480 0x00082161110c0090 0xf0dbaf3ccc6007c7 0xbe1b75e7998c00f8

def z443 : W := mkw 0x27b776daa2980136 0x04f6eedb54530026 0xfffffffff398003b 0xfffffffffe730007

def z444 : W := mkw 0x04a34688a0000000 0x009468d114000000 0xf0e7dfe3f0000003 0xde1cfbfc7e000000

def z445 : W := mkw 0x0808086555afaf7d 0xa101010caab5f5ef 0xf82458e3ffffffff 0xdf048b1c7fffffff

def z446 : W := mkw 0x0000000100008008 0x0000000020001001 0x0804100300018038 0x4100820060003007

def z447 : W := mkw 0x07fef0120f555000 0x00ffde0241eaaa00 0xdffff03f0ffff807 0xfbfffe07e1ffff00

def z448 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x67e7dfc3f0000000 0xccfcfbf87e000000

def z449 : W := mkw 0x0040090008600480 0x00080120010c0090 0x20c00f0000600000 0x841801e0000c0000

def z450 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xc7ffc0000f800001 0xf8fff80001f00000

def z451 : W := mkw 0x07b6749220000000 0x00f6ce9244000000 0xc7ffd0c330000001 0xf8fffa1866000000

def z452 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x57dfe73ff0000001 0x2afbfce7fe000000

def z453 : W := mkw 0x37fffffeeefe67f7 0x46ffffffdddfccfe 0xfffffffffffe67ff 0xffffffffffffccff

def z454 : W := mkw 0x0fbc34b705878369 0x81f78696e0b0f06d 0xbffc3fff0f8787ff 0xf7ff87ffe1f0f0ff

def z455 : W := mkw 0x04a34688a0000000 0x009468d114000000 0x00c3870000000000 0x001870e000000000

def z456 : W := mkw 0x2de03df70afa87ff 0x85bc07bee15f50ff 0xbfe03fff0ff807fe 0xf7fc07ffe1ff00ff

def z457 : W := mkw 0x0b1d323f85878369 0x8163a647f0b0f06d 0xffdfbf3fcf8787ff 0xfffbf7e7f9f0f0ff

def z458 : W := mkw 0x27f77ffbfafaafbe 0x24feefff7f5f55f7 0xffffffffffffffff 0xffffffffffffffff

def z459 : W := mkw 0x1b5dbb3ecde767e1 0xc36bb767d9bcecfc 0xf7dbaf3ccfe667c7 0xbefb75e799fcccf8

def z460 : W := mkw 0x104889244c6666c1 0x42091124898cccd8 0x9018203c0c6667c7 0x32030407818cccf8

def z461 : W := mkw 0x06ffc21aaf555000 0x00dff84355eaaa00 0xdfffc03ffffff805 0xfbfff807ffffff00

def z462 : W := mkw 0x0b5c39370de787e9 0x816b8726e1bcf0fd 0xbfdc3f3f0fe787ff 0xf7fb87e7e1fcf0ff

def z463 : W := mkw 0x0100384000a80534 0x00200708001500a6 0xaf2038c00ff807fe 0xf5e4071801ff00ff

def z464 : W := mkw 0x1009822dd406ea49 0x62013045ba80dd49 0x501fc03ff007f801 0x0a03f807fe00ff00

def z465 : W := mkw 0x0001020880000000 0x0000204110000000 0x00dba71c00000000 0x201b74e380000000

def z466 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0db800000000001 0xb81b700000000000

def z467 : W := mkw 0x07b6749220000000 0x00f6ce9244000000 0x0700000000000000 0x00e0000000000000

def z468 : W := mkw 0x0800000101818128 0x8100000020303025 0x0800000003818038 0x0100000000703007

def z469 : W := mkw 0x0000002100028208 0x0000000420005041 0x1004002300078001 0x020080046000f000

def z470 : W := mkw 0x35e9bfaccef667e3 0x46bd37f599deccfc 0xf7dbaf3ccfe667c7 0xbefb75e799fcccf8

def z471 : W := mkw 0x16ffc30c8f5550c1 0x42dff86191eaaa18 0x07dba71c0f8001c0 0x20fb74e381f00038

def z472 : W := mkw 0x04a34ee9f02aae1c 0x209469dd3e0555c3 0xf8e7dfe3f07ffe3f 0xdf1cfbfc7e0fffc7

def z473 : W := mkw 0x0000000050002800 0x200000000a000500 0x40004000f0007800 0x080008001e000f00

def z474 : W := mkw 0x0b14301201810120 0x8162860240302024 0x0700000003800000 0x00e0000000700000

def z475 : W := mkw 0x04a2400000000000 0x0094480000000000 0x40e3c00000000000 0x881c780000000000

def z476 : W := mkw 0x06be400005050000 0x00d7c80000a0a000 0xcfffc0000f878005 0xf9fff80001f0f000

def z477 : W := mkw 0x07b4349200000000 0x00f6869240000000 0xb7fc3fff00000003 0xf6ff87ffe0000000

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0xf82458e3f07ff807 0xdf048b1c7e0fff00

def z479 : W := mkw 0x0808086555afaf7d 0xa101010caab5f5ef 0x080000000ffffffc 0x0100000001ffffff

def z480 : W := mkw 0x27f7779aaad001a2 0x04feeef3555a0034 0xf7ffffffff8001c3 0xfefffffffff00038

def z481 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x0000000000000638 0x00000000000000c7

def z482 : W := mkw 0x0000084000280414 0x0000010800050082 0x200018c00000063a 0x04000318000000c7

def z483 : W := mkw 0x17fff79eac4440c1 0x42fffef3d5888818 0xf7fffffffc0001c3 0xfeffffffff800038

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0xc024400000000001 0xd804880000000000

def z485 : W := mkw 0x0000082040222600 0x00000104080444c0 0x30000820c0000602 0x06000104180000c0

def z486 : W := mkw 0x06fec0411f5dd81c 0x20dfd80823ebbb03 0xcfffd0c33ffff83d 0xf9fffa1867ffff07

def z487 : W := mkw 0x00000861002a861c 0x0000010c200550c3 0xb82418e3007f863f 0xd704831c600ff0c7

def z488 : W := mkw 0x0b1c387755afaf7d 0xa163870eeab5f5ef 0x9f1c303f0fffffff 0x73e38607e1ffffff

def z489 : W := mkw 0x0808002505878369 0x81010004a0b0f06d 0x980410230f8787ff 0x5300820461f0f0ff

def z490 : W := mkw 0x25e035800ad001a2 0x04bc06b0015a0034 0x8fc037000f8007fe 0x71f806e001f000ff

def z491 : W := mkw 0x05e034800a500000 0x00bc0690014a0000 0xafe03fc00ff80006 0xf5fc07f801ff0000

def z492 : W := mkw 0x021fc21aa5055000 0x0043f84354a0aa00 0x501fc03ff007f801 0x0a03f807fe00ff00

def z493 : W := mkw 0x021c000005050000 0x0043800000a0a000 0x071800000f800000 0x20e3000001f00000

def z494 : W := mkw 0x0000084050282c14 0x200001080a050582 0xe82058c0f0787e3e 0xdd040b181e0f0fc7

def z495 : W := mkw 0x0108302404860361 0x002106048090c06c 0x9f18303c0f8607ff 0x73e3060781f0c0ff

def z496 : W := mkw 0x0217421aa0000000 0x0042e84354000000 0xf0dfef3ff0000003 0xbe1bfde7fe000000

def z497 : W := mkw 0x04e008615a7aae1c 0x209c010c2b4f55c3 0xffe458e3fffffe3f 0xfffc8b1c7fffffc7

def z498 : W := mkw 0x1049822ccc466241 0x420930459988cc48 0xd0db803ccc666005 0xba1b7007998ccc00

def z499 : W := mkw 0x06b640411319981c 0x20d6c80822633303 0x0f2450c333999838 0x41e48a1866733307

def z500 : W := mkw 0x27f67dd22af805b6 0x04fecfba455f00b6 0xafe47fc33ff807fe 0xf5fc8ff867ff00ff

def z501 : W := mkw 0x04a0048000000000 0x0094009000000000 0x20e00fc000000000 0x841c01f800000000

def z502 : W := mkw 0x06fec0240f575241 0x00dfd80481eaea48 0xdfffe03c0fffffc7 0xfbfffc0781fffff8

def z503 : W := mkw 0x14e98b2cce7666c1 0x429d316599ceccd8 0xfffbaf3ccffe67c7 0xffff75e799ffccf8

def z504 : W := mkw 0x004880000f555000 0x0009100001eaaa00 0xc8db80000ffff805 0xb91b700001ffff00

def z505 : W := mkw 0x0a1c0877552fae5d 0xa143810eeaa5f5cb 0xf83c58fff07ffe3f 0xdf078b1ffe0fffc7

def z506 : W := mkw 0x27fefde15fffffbe 0x24ffdfbc2bfffff7 0xffffffe3ffffffff 0xfffffffc7fffffff

def z507 : W := mkw 0x021c0861552fae1c 0x2043810c2aa5f5c3 0xff3c58e3fffffe3f 0xffe78b1c7fffffc7

def z508 : W := mkw 0x2fbc34f7079f837f 0x85f7869ee0f3f06f 0x9f3c30ff0f9f87ff 0x73e7861fe1f3f0ff

def z509 : W := mkw 0x16ffc22ccf577241 0x42dff84599eaee48 0xdfffc03ccffff805 0xfbfff80799ffff00

def z510 : W := mkw 0x24e00dc00a780496 0x049c01b8014f0092 0xafe00fc00ff80004 0xf5fc01f801ff0000

def z511 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x501b803ccc6667c5 0x0a037007998cccf8

def z512 : W := mkw 0x004000000a500000 0x00080000014a0000 0x080000000ff80004 0x0100000001ff0000

def z513 : W := mkw 0x0fb6701303919128 0x81f6ce0260723225 0x0f24500303999838 0x41e48a0060733307

def z514 : W := mkw 0x0000002400020241 0x0000000480004048 0x1000203c000007c2 0x02000407800000f8

def z515 : W := mkw 0x01013efbf02aae1c 0x202027df7e0555c3 0x30003ffff000063a 0x060007fffe0000c7

def z516 : W := mkw 0x17fffffffc6eeedd 0x62ffffffff8ddddb 0xfffffffffc7fffff 0xffffffffff8fffff

def z517 : W := mkw 0x25e03de15afaafbe 0x24bc07bc2b5f55f7 0xbfe03fe3fff807fe 0xf7fc07fc7fff00ff

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0xf0000820c0000003 0x9e00010418000000

def z519 : W := mkw 0x0100348000000000 0x0020069000000000 0x20003fc000000002 0x040007f800000000

def z520 : W := mkw 0x0008002404060241 0x000100048080c048 0x000000000c0607c4 0x000000000180c0f8

def z521 : W := mkw 0x0000082040222600 0x00000104080444c0 0xf02458e3f0666607 0xde048b1c7e0cccc0

def z522 : W := mkw 0x37ffffeccfff77f7 0x46fffffd99ffeefe 0xfffffffccfffffff 0xffffffff99ffffff

def z523 : W := mkw 0x0900387750aaaf7d 0xa120070eea1555ef 0x300038fff00007fa 0x0600071ffe0000ff

def z524 : W := mkw 0x0315369aa0000000 0x0062a6d354000000 0xb71c3ffff0000003 0x76e387fffe000000

def z525 : W := mkw 0x0ffc30370fd78369 0x81ff8606e1faf06d 0x9ffc303f0fff87ff 0xf3ff8607e1fff0ff

def z526 : W := mkw 0x0217423bf002aa08 0x2042e8477e005541 0x501fc03ff007f801 0x0a03f807fe00ff00

def z527 : W := mkw 0x104889244f7776c1 0x4209112489eeeed8 0x080000000fffffc4 0x0100000001fffff8

def z528 : W := mkw 0x0314303300028208 0x0062860660005041 0x9f1c303f0007863f 0x73e38607e000f0c7

def z529 : W := mkw 0x0ffef0130fd5d128 0x81ffde0261faba25 0xcfffd0030ffff83d 0xf9fffa0061ffff07

def z530 : W := mkw 0x0000084050282c14 0x200001080a050582 0x0000000000787800 0x00000000000f0f00

def z531 : W := mkw 0x25e03dc00a780496 0x04bc07b8014f0092 0xa7e03fc000780002 0xf4fc07f8000f0000

def z532 : W := mkw 0x0000002100028208 0x0000000420005041 0x100010230000063a 0x02000204600000c7

def z533 : W := mkw 0x16ffcb2ccf7776c1 0x42dff96599eeeed8 0xf7dbaf3ccfe667c7 0xbefb75e799fcccf8

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x50044023f0000001 0x0a0088047e000000

def z535 : W := mkw 0x0001020880000000 0x0000204110000000 0x30002f3cc0000002 0x060005e798000000

def z536 : W := mkw 0x204009400af805b6 0x04080128015f00b6 0xa8c02f000ff807fe 0xb51805e001ff00ff

def z537 : W := mkw 0x0314301200000000 0x0062860240000000 0x0704100300000000 0x40e0820060000000

def z538 : W := mkw 0x27f43dd20af805b6 0x04fe87ba415f00b6 0xbffc3fff0ff807ff 0xf7ff87ffe1ff00ff

def z539 : W := mkw 0x1149bb2ccce667e1 0x42293765999cccfc 0xffdbbf3ccfe667ff 0xfffb77e799fcccff

def z540 : W := mkw 0x17bff6bee4066241 0x42f7fed7dc80cc48 0xf7fffffff0066003 0xfefffffffe00cc00

def z541 : W := mkw 0x0fbf76bfa5878369 0x81f7eed7f4b0f06d 0x9fdfb73f0f8787ff 0x73fbf6e7e1f0f0ff

def z542 : W := mkw 0x04e000000a500000 0x009c0000014a0000 0xcfe440000ffff805 0xf9fc880001ffff00

def z543 : W := mkw 0x27b77fdaa0a805b6 0x04f6effb541500b6 0xf7fffffff00007fb 0xfefffffffe0000ff

def z544 : W := mkw 0x0000084050282c14 0x200001080a050582 0x200008c0f0000000 0x040001181e000000

def z545 : W := mkw 0x35e13feccafa27f7 0x46bc27fd995f44fe 0xbfe03ffccff807fe 0xf7fc07ff99ff00ff

def z546 : W := mkw 0x00010a69d02aae1c 0x2000214d3a0555c3 0xf8fffffff07ffe3f 0xff1ffffffe0fffc7

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0xa02018c000000002 0xd404031800000000

def z548 : W := mkw 0x0314301200000000 0x0062860240000000 0xf73c78fff0000003 0xfee78f1ffe000000

def z549 : W := mkw 0x06fec0215f57fa08 0x20dfd8042beaff41 0xdfffc023fffff805 0xfbfff8047fffff00

def z550 : W := mkw 0x20000dc000280496 0x040001b800050092 0x20000fc000000000 0x040001f800000000

def z551 : W := mkw 0x0314301200800120 0x0062860240100024 0x9f1c303f0f8007ff 0x73e38607e1f000ff

def z552 : W := mkw 0x0000004010080814 0x2000000802010102 0x002040c030181800 0x0004081806030300

def z553 : W := mkw 0x07b6749220000000 0x00f6ce9244000000 0xa7e47fc330000002 0xf4fc8ff866000000

def z554 : W := mkw 0x06fec8615f7ffe1c 0x20dfd90c2befffc3 0xcfffc0000ffffe3d 0xf9fff80001ffffc7

def z555 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0xf0dbaf3ccc0001c3 0xbe1b75e799800038

def z556 : W := mkw 0x1149bfbeec6666c1 0x422937f7dd8cccd8 0xf0dbbffffc6667c7 0xbe1b77ffff8cccf8

def z557 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xa7fbbfdc00000002 0xf4ff77fb80000000

def z558 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xf8000820c07ffe3f 0x9f000104180fffc7

def z559 : W := mkw 0x0000084000280414 0x0000010800050082 0xf82458e3f078063f 0xdf048b1c7e0f00c7

def z560 : W := mkw 0x021c000005050000 0x0043800000a0a000 0xcf3c40000ffff805 0xf9e7880001ffff00

def z561 : W := mkw 0x135dbb3ecc6666c1 0x426bb767d98cccd8 0xf7dfbf3fcc6667c7 0xfefbf7e7f98cccf8

def z562 : W := mkw 0x04eac0000e545000 0x009d580001ca8a00 0xc0fbc0000c7e7805 0xb81f7800018fcf00

def z563 : W := mkw 0x25a034c002980136 0x04b4069800530026 0x8f2030c00f9807fe 0x71e4061801f300ff

def z564 : W := mkw 0x07b77edaa0280414 0x00f6efdb54050082 0xfffffffff078063f 0xfffffffffe0f00c7

def z565 : W := mkw 0x06f640000a500000 0x00dec800014a0000 0xcfffc0000ff80005 0xf9fff80001ff0000

def z566 : W := mkw 0x2b5c39770fff87ff 0x856b872ee1fff0ff 0x9f1c303f0fff87ff 0x73e38607e1fff0ff

def z567 : W := mkw 0x04e2c0000a505000 0x009c5800014a0a00 0xcfe3c0000ff87804 0xf9fc780001ff0f00

def z568 : W := mkw 0x07b6749220000000 0x00f6ce9244000000 0xf72458e3f0000003 0xdee48b1c7e000000

def z569 : W := mkw 0x25e13fc88af805b6 0x04bc27f9115f00b6 0xfffbbffccff807ff 0xffff77ff99ff00ff

def z570 : W := mkw 0x21403dc00af805b6 0x042807b8015f00b6 0x28003fc00ff807fe 0x050007f801ff00ff

def z571 : W := mkw 0x0001020880000000 0x0000204110000000 0x60c38f00c0000000 0x8c1871e018000000

def z572 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x58044023f07ffe3d 0x0b0088047e0fffc7

def z573 : W := mkw 0x0101369aa0000000 0x002026d354000000 0x0000271c00000000 0x000004e380000000

def z574 : W := mkw 0x0000002100028208 0x0000000420005041 0xd8245023007ffe3f 0xdb048a04600fffc7

def z575 : W := mkw 0x0a1c003705078249 0x81438006e0a0f049 0x9f1c003f0f878005 0x73e38007e1f0f000

def z576 : W := mkw 0x0b5cb0370dc7c369 0x816b9606e1b8f86d 0xdfdfb03f0fe7e7ff 0xfbfbf607e1fcfcff

def z577 : W := mkw 0x2b1c3df705af87ff 0x856387bee0b5f0ff 0xbf1c3fff0f8787ff 0x77e387ffe1f0f0ff

def z578 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x97dfb73f00000003 0x72fbf6e7e0000000

def z579 : W := mkw 0x004888615f7ffe1c 0x2009110c2befffc3 0xf82458e3fffffe3f 0xdf048b1c7fffffc7

def z580 : W := mkw 0x1b1d3b3fc5a7a7e9 0xc363a767f8b4f4fd 0xbf1c3f3fcf8787ff 0x77e387e7f9f0f0ff

def z581 : W := mkw 0x25a03dc000a805b6 0x04b407b8001500b6 0xa7e03fc0000007fa 0xf4fc07f8000000ff

def z582 : W := mkw 0x06ffc688af555000 0x00dff8d115eaaa00 0xefffcfc0fffff805 0xfdfff9f81fffff00

def z583 : W := mkw 0x25e035c00ad801b6 0x04bc06b8015b0036 0x0fe037c00f9801f8 0x61fc06f801f3003f

def z584 : W := mkw 0x084880250fd7d369 0x81091004a1fafa6d 0x080000000ffffffc 0x0100000001ffffff

def z585 : W := mkw 0x07b67cf3702aae1c 0x20f6cf9e6e0555c3 0xff2458e3f07ffe3f 0xdfe48b1c7e0fffc7

def z586 : W := mkw 0x06b7420880000000 0x00d6e84110000000 0xf7ffef3cc0000003 0xfefffde798000000

def z587 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x67fbefdcf0000000 0xacff7dfb9e000000

def z588 : W := mkw 0x25e13fdaaaf805b6 0x04bc27fb555f00b6 0xbfe03ffffff807fe 0xf7fc07ffffff00ff

def z589 : W := mkw 0x0101369aa0000000 0x002026d354000000 0xf0dbbffff0000003 0xbe1b77fffe000000

def z590 : W := mkw 0x00000061500aaa1c 0x2000000c2a015543 0x582450e3f01ff839 0x4b048a1c7e03ff07

def z591 : W := mkw 0x0000082040222600 0x00000104080444c0 0x0000000000666604 0x00000000000cccc0

def z592 : W := mkw 0x25e83de40efe07f7 0x04bd07bc81dfc0fe 0xbff83ffc0ffe07ff 0xf7ff07ff81ffc0ff

def z593 : W := mkw 0x25e035800ad001a2 0x04bc06b0015a0034 0x8fe027000ff801c4 0xf1fc04e001ff0038

def z594 : W := mkw 0x204001000ad001a2 0x04080020015a0034 0x000000000f8001c0 0x0000000001f00038

def z595 : W := mkw 0x000000411008881c 0x2000000822011103 0x0800000000199838 0x0100000000033307

def z596 : W := mkw 0x10418b2cc86266c1 0x42083165990c4cd8 0x70c3af3cc06067c2 0x8e1875e7980c0cf8

def z597 : W := mkw 0x25e03de10afa87be 0x04bc07bc215f50f7 0xbfe43fe30fff87ff 0xf7fc87fc61fff0ff

def z598 : W := mkw 0x0900387750aaaf7d 0xa120070eea1555ef 0xf82478fff07fffff 0xdf048f1ffe0fffff

def z599 : W := mkw 0x04e008400a780414 0x009c0108014f0082 0xafe018c00ff8063e 0xf5fc031801ff00c7

def z600 : W := mkw 0x2fff7fffafff87ff 0x85ffeffff5fff0ff 0xffffffffffff87ff 0xfffffffffffff0ff

def z601 : W := mkw 0x0b5cb0370fd7d369 0x816b9606e1fafa6d 0x9f1c303f0fffffff 0x73e38607e1ffffff

def z602 : W := mkw 0x04e000000a500000 0x009c0000014a0000 0x00e0000000780000 0x801c0000000f0000

def z603 : W := mkw 0x06fc00000f550000 0x00df800001eaa000 0x8ffc00000fff8005 0xf1ff800001fff000

def z604 : W := mkw 0x0000000000000000 0x0000000000000000 0x300018e3f0000002 0x0600031c7e000000

def z605 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xc7ffe71c00000001 0xf8fffce380000000

def z606 : W := mkw 0x0040092048622680 0x00080124090c44d0 0xf0c02f20cc6667c7 0xbe1805e4198cccf8

def z607 : W := mkw 0x04eac0000f555000 0x009d580001eaaa00 0x48e3c0000ffff804 0x891c780001ffff00

def z608 : W := mkw 0x07fef0000fd55120 0x00ffde0001faaa24 0xcffff0000fffffff 0xf9fffe0001ffffff

def z609 : W := mkw 0x000008215022ae08 0x200001042a0455c1 0xf0044823f067fe07 0x9e0089047e0cffc0

def z610 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x0f2010c00ff807fc 0x41e4021801ff00ff

def z611 : W := mkw 0x05a37688a0000000 0x00b46ed114000000 0xe7e3ffc0f0000002 0xfcfc7ff81e000000

def z612 : W := mkw 0x1009822cc4066241 0x420130459880cc48 0xd01ba03ccc0667c7 0x3a0374079980ccf8

def z613 : W := mkw 0x0b1d36bfa5878369 0x8163a6d7f4b0f06d 0xbf1c3fffff8787ff 0x77e387fffff0f0ff

def z614 : W := mkw 0x0b14301301818128 0x8162860260303025 0x9f1c303f0381803b 0x73e38607e0703007

def z615 : W := mkw 0x07b77edaf0282c14 0x20f6efdb5e050582 0xf7fffffff0787803 0xfefffffffe0f0f00

def z616 : W := mkw 0x0fb776bfa0828369 0x81f6eed7f410506d 0xf7fffffff00007fb 0xfefffffffe0000ff

def z617 : W := mkw 0x10010b6dd02aaedd 0x6200216dba0555db 0xf8247ffff07fffff 0xdf048ffffe0fffff

def z618 : W := mkw 0x24e00dc00a780496 0x049c01b8014f0092 0xa8e01fc00078063e 0xd51c03f8000f00c7

def z619 : W := mkw 0x214039400af805b6 0x04280728015f00b6 0x8f0030000ff807fe 0x71e0060001ff00ff

def z620 : W := mkw 0x17f7ff9ae8606480 0x42fefff35d0c0c90 0xf7fffffff0606003 0xfefffffffe0c0c00

def z621 : W := mkw 0x021c002105078208 0x0043800420a0f041 0x9f1c10230f87863f 0x73e3820461f0f0c7

def z622 : W := mkw 0x004880000f555000 0x0009100001eaaa00 0xc82440000ffff805 0xd904880001ffff00

def z623 : W := mkw 0x04a0000000000000 0x0094000000000000 0x87e0000000000000 0xf0fc000000000000

def z624 : W := mkw 0x21003580008001a2 0x042006b000100034 0x00002700000001c0 0x000004e000000038

def z625 : W := mkw 0x06fec0210f57d208 0x00dfd80421eafa41 0xdfffd0230ffffe3f 0xfbfffa0461ffffc7

def z626 : W := mkw 0x10098a2cc4266641 0x420131459884ccc8 0xf01b883cc0666607 0x9e037107980cccc0

def z627 : W := mkw 0x0efec0250fd7d369 0x81dfd804a1fafa6d 0xcfffc0000ffffffd 0xf9fff80001ffffff

def z628 : W := mkw 0x10418b69d86aee9c 0x6208316d3b0d5dd3 0xf8e7dfe3f07ffe3f 0xdf1cfbfc7e0fffc7

def z629 : W := mkw 0x07b77efbf02aae1c 0x20f6efdf7e0555c3 0xf7fffffff000063b 0xfefffffffe0000c7

def z630 : W := mkw 0x000000215002aa08 0x200000042a005541 0xd8045023f007fe3f 0x5b008a047e00ffc7

def z631 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x380018e3f07ffe3e 0x0700031c7e0fffc7

def z632 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x30002f3ccc6667c6 0x060005e7998cccf8

def z633 : W := mkw 0x0216400001011000 0x0042c80000202200 0x0004400000019800 0x0000880000003300

def z634 : W := mkw 0x000000411008881c 0x2000000822011103 0xc82450c3307ff83d 0xd9048a18660fff07

def z635 : W := mkw 0x17b77fbee02226c1 0x42f6eff7dc0444d8 0xf7fffffff00007c3 0xfefffffffe0000f8

def z636 : W := mkw 0x10410b2cc86226c1 0x42082165990c44d8 0xb0c02f3ccc6007c6 0xb61805e7998c00f8

def z637 : W := mkw 0x000000215002aa08 0x200000042a005541 0xd8244023f07ff805 0xdb0488047e0fff00

def z638 : W := mkw 0x0808000405850161 0x8101000080b0a02c 0x000000000f8001c0 0x0000000001f00038

def z639 : W := mkw 0x1b5dbb7fddefeffd 0xe36bb76ffbbdfdff 0xffffffffffffffff 0xffffffffffffffff

def z640 : W := mkw 0x1001022cc0022241 0x4200204598004448 0x1000003cc0000000 0x0200000798000000

def z641 : W := mkw 0x0900303700828369 0x81200606e010506d 0x9804303f000787ff 0x53008607e000f0ff

def z642 : W := mkw 0x021c002405070241 0x0043800480a0e048 0x9f1c203c0f8787c7 0x73e3840781f0f0f8

def z643 : W := mkw 0x004889000c644480 0x00091120018c8890 0xe0dbaf000c6667c7 0xbc1b75e0018cccf8

def z644 : W := mkw 0x00034208a0000000 0x0000684114000000 0x4003c000f0000000 0x080078001e000000

def z645 : W := mkw 0x0000000110008808 0x2000000022001101 0x0004400330019800 0x0000880066003300

def z646 : W := mkw 0x14ebcfacec6666c1 0x429d79f59d8cccd8 0xf0fbeffcfc6667c7 0xbe1f7dff9f8cccf8

def z647 : W := mkw 0x0b1c303705078249 0x81638606e0a0f049 0x971c303f00078003 0x72e38607e000f000

def z648 : W := mkw 0x0000002100028208 0x0000000420005041 0x080000000007863c 0x010000000000f0c7

def z649 : W := mkw 0x17ffffbeef7776c1 0x42fffff7ddeeeed8 0xffffffffffffffc7 0xfffffffffffffff8

def z650 : W := mkw 0x07fff69aaf555000 0x00fffed355eaaa00 0xf7ffffffff800003 0xfefffffffff00000

def z651 : W := mkw 0x0100300000000000 0x0020060000000000 0x8700300000000002 0x70e0060000000000

def z652 : W := mkw 0x18498b2dcde7e7e9 0xc3093165b9bcfcfd 0xf8dbaf3ccfe7e7ff 0xbf1b75e799fcfcff

def z653 : W := mkw 0x16ffcb2ccc6666c1 0x42dff965998cccd8 0xf7ffef3ccc6667c7 0xfefffde7998cccf8

def z654 : W := mkw 0x0808002505078249 0x81010004a0a0f049 0x0000000000078000 0x000000000000f000

def z655 : W := mkw 0x25a034c11298893e 0x24b4069822531127 0x0f2450c333999838 0x41e48a1866733307

def z656 : W := mkw 0x05a0348000000000 0x00b4069000000000 0xf7e47fe3f0000003 0xfefc8ffc7e000000

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x9004102300000003 0x5200820460000000

def z658 : W := mkw 0x06fec8204f777600 0x00dfd90409eeeec0 0xffffc820cffffe07 0xfffff90419ffffc0

def z659 : W := mkw 0x27f7779aaad001a2 0x04feeef3555a0034 0x07dba71c0f8001c0 0x20fb74e381f00038

def z660 : W := mkw 0x0000084110288c1c 0x2000010822051183 0xa82458c330799e3e 0xd5048b18660f33c7

def z661 : W := mkw 0x19013b3fc0a2a7e9 0xc3202767f81454fd 0x30003f3fc00007fa 0x060007e7f80000ff

def z662 : W := mkw 0x05a0348000000000 0x00b4069000000000 0x07c0270000000000 0x20f804e000000000

def z663 : W := mkw 0x0040800008404000 0x0008100001080800 0x40c3800000606000 0x88187000000c0c00

def z664 : W := mkw 0x025c80000d454000 0x004b900001a8a800 0xcfdf80000fe7e005 0xf9fbf00001fcfc00

def z665 : W := mkw 0x1a5d8b3fcd67e6c9 0xc34bb167f9acfcd9 0xf0dfaf3fcc67e7c7 0xbe1bf5e7f98cfcf8

def z666 : W := mkw 0x10010b2cc02226c1 0x42002165980444d8 0xf0002f3cc06667c7 0x9e0005e7980cccf8

def z667 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x47fbc0000ff87800 0xa8ff780001ff0f00

def z668 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xc7db80000fe66005 0xb8fb700001fccc00

def z669 : W := mkw 0x00000860502a2e14 0x2000010c0a0545c2 0xf02048e0f07e7e07 0x9e04091c1e0fcfc0

def z670 : W := mkw 0x2ffc3df75fffafff 0xa5ff87beebfff5ff 0xfffc7fffffffffff 0xffff8fffffffffff

def z671 : W := mkw 0x06fec8405f7d7c14 0x20dfd9080befaf82 0xefffc8c0fffff805 0xfdfff9181fffff00

def z672 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x0f0410030f8787fc 0x41e0820061f0f0ff

def z673 : W := mkw 0x21013fdaa0a805b6 0x042027fb541500b6 0x30003ffff00007fa 0x060007fffe0000ff

def z674 : W := mkw 0x0ffef8775fffff7d 0xa1ffdf0eebffffef 0xfffff8ffffffffff 0xffffff1fffffffff

def z675 : W := mkw 0x004880000c444000 0x0009100001888800 0x000000000c666004 0x00000000018ccc00

def z676 : W := mkw 0x10418b28c8626680 0x42083165190c4cd0 0xf0c38f20c0666607 0x9e1871e4180cccc0

def z677 : W := mkw 0x0fbf76bfa5078249 0x81f7eed7f4a0f049 0xf7fffffff0078003 0xfefffffffe00f000

def z678 : W := mkw 0x07b674d33008881c 0x20f6ce9a66011103 0x0f2450c330199838 0x41e48a1866033307

def z679 : W := mkw 0x104889244c6666c1 0x42091124898cccd8 0xc0db80000c6667c5 0xb81b7000018cccf8

def z680 : W := mkw 0x05e03d8008600480 0x00bc07b0010c0090 0xa7e03fc00c6007c6 0xf4fc07f8018c00f8

def z681 : W := mkw 0x04e2c8405a787c14 0x209c59080b4f0f82 0x60e3c8c0f0787800 0x8c1c79181e0f0f00

def z682 : W := mkw 0x204009615afaafbe 0x2408012c2b5f55f7 0x080000000ffffffc 0x0100000001ffffff

def z683 : W := mkw 0x07fff69aaf555000 0x00fffed355eaaa00 0x07dba71c0f800000 0x20fb74e381f00000

def z684 : W := mkw 0x05a03ce1502aae1c 0x20b4079c2a0555c3 0xffe47fe3f07ffe3f 0xfffc8ffc7e0fffc7

def z685 : W := mkw 0x27f77fdaaaf805b6 0x04feeffb555f00b6 0xaffbbfdc0ff807fe 0xf5ff77fb81ff00ff

def z686 : W := mkw 0x14ebcb2cce7676c1 0x429d796599ceced8 0xf0fbef3ccc7e7fc7 0xbe1f7de7998fcff8

def z687 : W := mkw 0x05a1368880000000 0x00b426d110000000 0xf7fbbffcc0000003 0xfeff77ff98000000

def z688 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x47dfc0000f87f801 0x28fbf80001f0ff00

def z689 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x98041023007ffe3f 0x53008204600fffc7

def z690 : W := mkw 0x16ffcb08cf757480 0x42dff96119eeae90 0xefffcf00cffff805 0xfdfff9e019ffff00

def z691 : W := mkw 0x05a3769aa0000000 0x00b46ed354000000 0x70e3fffff0000002 0x8e1c7ffffe000000

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000000007ff804 0x01000000000fff00

def z693 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xb80418e3f007863f 0x5700831c7e00f0c7

def z694 : W := mkw 0x10498b08cc646480 0x42093161198c8c90 0xe0db8f00cc666005 0xbc1b71e0198ccc00

def z695 : W := mkw 0x000008415028ac1c 0x200001082a051583 0x682458c3f079f838 0xcd048b187e0f3f07

def z696 : W := mkw 0x30498b6ccefe67f7 0x4609316d99dfccfe 0xf8dbaf3ccffe67ff 0xbf1b75e799ffccff

def z697 : W := mkw 0x0a1c003705078249 0x81438006e0a0f049 0x981c103f0007863f 0x53038207e000f0c7

def z698 : W := mkw 0x121fc23ee4066241 0x4243f847dc80cc48 0x501fc03ff0066001 0x0a03f807fe00cc00

def z699 : W := mkw 0x07fef4800f555000 0x00ffde9001eaaa00 0xefffffc00ffff807 0xfdfffff801ffff00

def z700 : W := mkw 0x00000061100a8a1c 0x2000000c22015143 0x982450e3301f9e3f 0x53048a1c6603f3c7

def z701 : W := mkw 0x27fef5800fd551a2 0x04ffdeb001faaa34 0x07dba7000f8001c0 0x20fb74e001f00038

def z702 : W := mkw 0x021ec0215507fa08 0x2043d8042aa0ff41 0x501fc023f007f801 0x0a03f8047e00ff00

def z703 : W := mkw 0x07f7769aaa500000 0x00feeed3554a0000 0xfffffffffff80007 0xffffffffffff0000

def z704 : W := mkw 0x0040090008600480 0x00080120010c0090 0x000000000c6007c4 0x00000000018c00f8

def z705 : W := mkw 0x2ffc35b70fd783eb 0x85ff86b6e1faf07d 0x9fdc373f0f8787ff 0x73fb86e7e1f0f0ff

def z706 : W := mkw 0x0a1ec0370507d249 0x8143d806e0a0fa49 0x501fc03f0007f801 0x0a03f807e000ff00

def z707 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0xf0fffffffc0001c3 0xfe1fffffff800038

def z708 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x77dffffff0000003 0x2efbfffffe000000

def z709 : W := mkw 0x1049832ccc4662c1 0x420930659988cc58 0xf0dbaf3ccc0661c3 0xbe1b75e79980cc38

def z710 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xdfdfb03f0f8787ff 0xfbfbf607e1f0f0ff

def z711 : W := mkw 0x1049832c8c4642c1 0x420930659188c858 0x00dba71c0c0607c4 0x201b74e38180c0f8

def z712 : W := mkw 0x1b1cb0374587e369 0xc3639606e8b0fc6d 0x9f1c303f0f87e7ff 0x73e38607e1f0fcff

def z713 : W := mkw 0x0b1c385655ad2d75 0xa163870acab5a5ae 0x673868dcfff879c0 0xace70d1b9fff0f38

def z714 : W := mkw 0x0de2f0370ad2d369 0x81bc5e06e15a5a6d 0x50e3f03f00787ffa 0x8a1c7e07e00f0fff

def z715 : W := mkw 0x000008415028ac1c 0x200001082a051583 0xe82458c3f07ff83d 0xdd048b187e0fff07

def z716 : W := mkw 0x0001020880000000 0x0000204110000000 0xf0dbaf3ccc0007c7 0xbe1b75e7998000f8

def z717 : W := mkw 0x07b7769aa3111000 0x00f6eed354622200 0xf7fffffff3800003 0xfefffffffe700000

def z718 : W := mkw 0x000000411008881c 0x2000000822011103 0xf82458e3f07ff83f 0xdf048b1c7e0fff07

def z719 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x1f1c303f0f8187fa 0x63e38607e1f030ff

def z720 : W := mkw 0x22574b5aaaf805b6 0x044ae96b555f00b6 0x581fc03ffff807fd 0x0b03f807ffff00ff

def z721 : W := mkw 0x06fec1000f555080 0x00dfd82001eaaa10 0xcfffe7000ffff9c5 0xf9fffce001ffff38

def z722 : W := mkw 0x06b7469aa0000000 0x00d6e8d354000000 0xf7ffcffff0000001 0xfefff9fffe000000

def z723 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0ffef3ccc6667c7 0xfe1ffde7998cccf8

def z724 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xa0dbaf1c0c6667c6 0xb41b75e3818cccf8

def z725 : W := mkw 0x0140394008e805b4 0x00280728011d00b6 0xafe03fc00ff807fe 0xf5fc07f801ff00ff

def z726 : W := mkw 0x05a1368880000000 0x00b426d110000000 0xf7fffffff0000003 0xfefffffffe000000

def z727 : W := mkw 0x25e27dc02af805b6 0x04bc4fb8055f00b6 0xafe07fc03ff807fe 0xf5fc0ff807ff00ff

def z728 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x90dba73c0c6667c7 0x321b74e7818cccf8

def z729 : W := mkw 0x0fb674b321838328 0x81f6ce9664307065 0xff2458e3f387863f 0xdfe48b1c7e70f0c7

def z730 : W := mkw 0x25e035a15ad2abaa 0x24bc06b42b5a5575 0x57c46723ff87f9c1 0x2af88ce47ff0ff38

def z731 : W := mkw 0x0a1fc23fa507d249 0x8143f847f4a0fa49 0x501fc03ff007f801 0x0a03f807fe00ff00

def z732 : W := mkw 0x10010b6dd02aaedd 0x6200216dba0555db 0xf8fffffff07fffff 0xff1ffffffe0fffff

def z733 : W := mkw 0x0a1d023fa5078249 0x8143a047f4a0f049 0x101c003ff0078001 0x02038007fe00f000

def z734 : W := mkw 0x0b1c301605850161 0x81638602c0b0a02c 0x0718301c0f8007fa 0x20e3060381f000ff

def z735 : W := mkw 0x10498b6cdc6e6ed5 0x6209316d9b8dcdda 0xf8fbfffcfc7e7fff 0xff1f7fff9f8fcfff

def z736 : W := mkw 0x1049834d9c4cc8dd 0x62093069b389991b 0x08fff7df3c1999f8 0x611ffefbe783333f

def z737 : W := mkw 0x25e035800ad001a2 0x04bc06b0015a0034 0x0fc027000f8007fc 0x21f804e001f000ff

def z738 : W := mkw 0x30498b6cce7e66d7 0x4609316d99cfccda 0xf0dbaf3ccc7e67c7 0xbe1b75e7998fccf8

def z739 : W := mkw 0x0b1c30375587ab69 0xa1638606eab0f56d 0x9f1c303fff8787ff 0x73e38607fff0f0ff

def z740 : W := mkw 0x27b7769aa2900122 0x04f6eed354520024 0xf7fffffff3800003 0xfefffffffe700000

def z741 : W := mkw 0x0b1c30375587ab69 0xa1638606eab0f56d 0xff3c78ffff87ffff 0xffe78f1ffff0ffff

def z742 : W := mkw 0x05a3769aa0000000 0x00b46ed354000000 0xf0fbfffff0000003 0xbe1f7ffffe000000

def z743 : W := mkw 0x1049832c8c4642c1 0x420930659188c858 0xf0dbaf3ccc0607c7 0xbe1b75e79980c0f8

def z744 : W := mkw 0x021ec00005055000 0x0043d80000a0aa00 0xcf3fc0000ffff805 0xf9e7f80001ffff00

def z745 : W := mkw 0x0315369aa0000000 0x0062a6d354000000 0xf7dfbffff0000003 0xfefbf7fffe000000

def z746 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xafe03fc00ffffffe 0xf5fc07f801ffffff

def z747 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x00dba71c0c6661c4 0x201b74e3818ccc38

def z748 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0x30dbbffffc0007fa 0x261b77ffff8000ff

def z749 : W := mkw 0x25a034c002980136 0x04b4069800530026 0xafe03fc00f9807fe 0xf5fc07f801f300ff

def z750 : W := mkw 0x10098b2cc42666c1 0x420131659884ccd8 0xf0dbaf3cc00667c3 0xbe1b75e79800ccf8

def z751 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x9f1c303f0fffffff 0x73e38607e1ffffff

def z752 : W := mkw 0x16b74b2cc33336c1 0x42d6e965986666d8 0x3f246f3cc3999fc2 0x47e48de7987333f8

def z753 : W := mkw 0x2fb674d32399813e 0x85f6ce9a64733027 0x0f2450c333998038 0x41e48a1866733007

def z754 : W := mkw 0x0b14301301818128 0x8162860260303025 0x9f1c303f0f8187ff 0x73e38607e1f030ff

def z755 : W := mkw 0x25e27dc00af805b6 0x04bc4fb8015f00b6 0xefe3ffc00ff807fe 0xfdfc7ff801ff00ff

def z756 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xff3c78ffffffffff 0xffe78f1fffffffff

def z757 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xbff83ffc0ff807ff 0xf7ff07ff81ff00ff

def z758 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xafe43fc00fff87ff 0xf5fc87f801fff0ff

def z759 : W := mkw 0x07b7769aa1010000 0x00f6eed354202000 0xfffffffff3818003 0xfffffffffe703000

def z760 : W := mkw 0x25a03dc002b805b6 0x04b407b8005700b6 0xaf203fc00f9807fe 0x75e407f801f300ff

def z761 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf8dfaf3ccc67e7c7 0xff1bf5e7998cfcf8

def z762 : W := mkw 0x06b7420880000000 0x00d6e84110000000 0xf7fffffff0000003 0xfefffffffe000000

def z763 : W := mkw 0x2efc0df70f7f86df 0x85df81bee1eff0db 0x30fc0fff007f8001 0x861f81ffe00ff000

def z764 : W := mkw 0x35a9b6ecc69e6377 0x46b536dd98d3cc6e 0x5f3b90fcc39e6039 0x4be7721f9873cc07

def z765 : W := mkw 0x24e009400af805b6 0x049c0128015f00b6 0xafe02f000ff807fe 0xf5fc05e001ff00ff

def z766 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x2fe01fc00ff807fc 0xc5fc03f801ff00ff

def z767 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x8fc037000ff807fe 0x71f806e001ff00ff

def z768 : W := mkw 0x07b77efbf02aae1c 0x20f6efdf7e0555c3 0x0fdba71c007ffe3c 0x21fb74e3800fffc7

def z769 : W := mkw 0x10498b4c8c6c44d5 0x42093169918d889a 0xa8fbbfdc0c7807fe 0xf51f77fb818f00ff

def z770 : W := mkw 0x0fb6749221810120 0x81f6ce9244302024 0x0700000003800000 0x00e0000000700000

def z771 : W := mkw 0x25e2fdc00af855b6 0x04bc5fb8015f0ab6 0xefe7ffc00fffffff 0xfdfcfff801ffffff

def z772 : W := mkw 0x0ffff69eafd55161 0x81fffed3d5faaa2c 0x07dba71c0f8001c0 0x20fb74e381f00038

def z773 : W := mkw 0x25e0bdc00af845b6 0x04bc17b8015f08b6 0xefe3bfc00ff867fe 0xfdfc77f801ff0cff

def z774 : W := mkw 0x21003dc000a805b6 0x042007b8001500b6 0xaf203fc00ff807fe 0xf5e407f801ff00ff

def z775 : W := mkw 0x0fb6749221810120 0x81f6ce9244302024 0x072450c333800000 0x40e48a1866700000

def z776 : W := mkw 0x304889655efeefff 0x6609112cabdfddff 0x080000000ffffffc 0x0100000001ffffff

def z777 : W := mkw 0x27b6749222900122 0x04f6ce9244520024 0x072450c333800000 0x40e48a1866700000

def z778 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf8ffef3ccc7fffff 0xff1ffde7998fffff

def z779 : W := mkw 0x05e039000af005a0 0x00bc0720015e00b4 0xafe03f000ff807fe 0xf5fc07e001ff00ff

def z780 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x9718303f0f8607ff 0x32e30607e1f0c0ff

def z781 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0xf0dbaf3ccc6661c7 0xbe1b75e7998ccc38

def z782 : W := mkw 0x0b1e703705878369 0x8163ce06e0b0f06d 0xdf1ff03f0f8787ff 0x7be3fe07e1f0f0ff

def z783 : W := mkw 0x10498b0c8c6444c1 0x42093161918c8898 0x20dbaf1c0c6001c0 0xa41b75e3818c0038

def z784 : W := mkw 0x34e18fc8da786c96 0x669c31f91b4f0d92 0x60e3cfc0f0787800 0x8c1c79f81e0f0f00

def z785 : W := mkw 0x0149b69aaf555000 0x002936d355eaaa00 0x38003ffffffff806 0x070007ffffffff00

def z786 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x70dbaf3ccc6067c2 0xae1b75e7998c0cf8

def z787 : W := mkw 0x1a1d823f8507c249 0xc343b047f0a0f849 0x101f803f00078001 0x0203f007e000f000

def z788 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf8dbbffffc7fffff 0xbf1b77ffff8fffff

def z789 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0xc0dba71c0c0001c1 0xb81b74e381800038

def z790 : W := mkw 0x27fff79aafd551a2 0x04fffef355faaa34 0x07dba71c0f8001c0 0x20fb74e381f00038

def z791 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x8fdf80000ffff805 0x71fbf00001ffff00

def z792 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x2f203fc00ff807fe 0x45e407f801ff00ff

def z793 : W := mkw 0x0000002100028208 0x0000000420005041 0xf82458e3f07ffe3f 0xdf048b1c7e0fffc7

def z794 : W := mkw 0x0317769aa0000000 0x0062eed354000000 0xf0dffffff0000003 0xbe1bfffffe000000

def z795 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x70dbaf3ccc6661c1 0xae1b75e7998ccc38

def z796 : W := mkw 0x27b6749222900122 0x04f6ce9244520024 0x0700000003800000 0x00e0000000700000

def z797 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0fbeffcfc6667c7 0xbe1f7dff9f8cccf8

def z798 : W := mkw 0x26fec5800f555082 0x04dfd8b001eaaa10 0xcfffc7000ffff805 0xf9fff8e001ffff00

def z799 : W := mkw 0x10498b2cce7666c1 0x4209316599ceccd8 0xf8dbaf3ccffe67c7 0xbf1b75e799ffccf8

def z800 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x8fe027000ff807fc 0xf1fc04e001ff00ff

def z801 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xffffc820cffff807 0xfffff90419ffff00

def z802 : W := mkw 0x1b55bb1bc9e1e5a8 0xc36ab763793c3cb5 0x6fc79f03c3e1e038 0xcdf8f3e0787c3c07

def z803 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf8dbaf3ccc7fffc7 0xbf1b75e7998ffff8

def z804 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xb7fbbffff0000002 0xf6ff77fffe000000

def z805 : W := mkw 0x06fec8615f7ffe1c 0x20dfd90c2befffc3 0x37db98e3ff80063a 0x26fb731c7ff000c7

def z806 : W := mkw 0x104889655c6eeedd 0x6209112cab8ddddb 0x000000000c6667fc 0x00000000018cccff

def z807 : W := mkw 0x10010b6dd02aaedd 0x6200216dba0555db 0xf0fffffff00007fb 0xfe1ffffffe0000ff

def z808 : W := mkw 0x16fec1040f5550c1 0x42dfd82081eaaa18 0xcfffc0000ffff9c5 0xf9fff80001ffff38

def z809 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x702458e3f07ffe3b 0x8e048b1c7e0fffc7

def z810 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xa7e03fc00f8007fa 0xf4fc07f801f000ff

def z811 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf8fffffffc7fffc7 0xff1fffffff8ffff8

def z812 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x782458e3f07ff839 0xcf048b1c7e0fff07

def z813 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x382458e3f07ffe3e 0x47048b1c7e0fffc7

def z814 : W := mkw 0x00000865502aae5d 0x2000010caa0555cb 0xf82478fff07fffff 0xdf048f1ffe0fffff

def z815 : W := mkw 0x10498b6ddf7ffedd 0x6209316dbbefffdb 0xf8dbaf3ccfffffff 0xbf1b75e799ffffff

def z816 : W := mkw 0x1a1d823fd507ea49 0xe343b047faa0fd49 0x501fc03ff007f801 0x0a03f807fe00ff00

def z817 : W := mkw 0x104889655f7ffedd 0x6209112cabefffdb 0x080000000ffffffc 0x0100000001ffffff

def z818 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xcfffd0c33ffff805 0xf9fffa1867ffff00

def z819 : W := mkw 0x00410b28c8622680 0x00082165190c44d0 0xf0dbaf3ccc6667c7 0xbe1b75e7998cccf8

def z820 : W := mkw 0x06b7469aa0000000 0x00d6e8d354000000 0xf0ffeffff0000003 0xbe1ffdfffe000000

def z821 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x1f1c203f0f8787fd 0x23e38407e1f0f0ff

def z822 : W := mkw 0x231efdc005ad55b6 0x0463dfb800b5aab6 0x601fffc00007fffb 0x0c03fff80000ffff

def z823 : W := mkw 0x0100300000800120 0x0020060000100024 0x9f18303c0f8007ff 0x73e3060781f000ff

def z824 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x47ffc0000ffff801 0xa8fff80001ffff00

def z825 : W := mkw 0x10498b6ddf7ffedd 0x6209316dbbefffdb 0xf8ffffffffffffff 0xff1fffffffffffff

def z826 : W := mkw 0x0b1ef0370587d369 0x8163de06e0b0fa6d 0x9f1fb03f0f8787ff 0x73e3f607e1f0f0ff

def z827 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xff1c383fcf8787ff 0xffe38707f9f0f0ff

def z828 : W := mkw 0x25e03dc05af82db6 0x24bc07b80b5f05b6 0xafe03fc00ff87ffe 0xf5fc07f801ff0fff

def z829 : W := mkw 0x0b1c301605850161 0x81638602c0b0a02c 0x9f1c303f0f8007ff 0x73e38607e1f000ff

def z830 : W := mkw 0x06fec0040f555041 0x00dfd80081eaaa08 0xcfffe01c0ffff9c5 0xf9fffc0381ffff38

def z831 : W := mkw 0x10090b2cc42626c1 0x420121659884c4d8 0xf0dbaf3ccc0607c7 0xbe1b75e79980c0f8

def z832 : W := mkw 0x17fefdb66c6666c1 0x42ffdfb6cd8cccd8 0x072450c33c6667c4 0x40e48a18678cccf8

def z833 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xfffffffff0078007 0xfffffffffe00f000

def z834 : W := mkw 0x0108302504868369 0x00210604a090d06d 0x9f1c303f0f8787ff 0x73e38607e1f0f0ff

def z835 : W := mkw 0x06bec00007155000 0x00d7d80000e2aa00 0xcf3fc00003fff805 0xd9e7f800007fff00

def z836 : W := mkw 0x1a1fc23fc507f249 0xc343f847f8a0fe49 0x501fc03fc007f801 0x0a03f807f800ff00

def z837 : W := mkw 0x121fc22dd507fa49 0x6243f845baa0ff49 0x501fc03ff007f801 0x0a03f807fe00ff00

def z838 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xefe07fc00ff87ffe 0xfdfc0ff801ff0fff

def z839 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x0718201c0f8007f8 0x20e3040381f000ff

def z840 : W := mkw 0x10498b6cdc6e6ed5 0x6209316d9b8dcdda 0xf0dbaffcfc6667c7 0xbe1b75ff9f8cccf8

def z841 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x971c303f0f8007fb 0x72e38607e1f000ff

def z842 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x27e03fc00ff807fa 0xa4fc07f801ff00ff

def z843 : W := mkw 0x021c002505078249 0x00438004a0a0f049 0x9f1c303f0f8787ff 0x73e38607e1f0f0ff

def z844 : W := mkw 0x10498b6dcc6ee6dd 0x4209316db98ddcdb 0xf8ffbfffcc7fe7ff 0xff1ff7fff98ffcff

def z845 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xdfffc023fffff805 0xfbfff8047fffff00

def z846 : W := mkw 0x10498b2cce7676c1 0x4209316599ceced8 0xf0dbaf3ccc7e7fc7 0xbe1b75e7998fcff8

def z847 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x90dba73c0c0001c3 0x321b74e781800038

def z848 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xefe07fc0fff807fe 0xfdfc0ff81fff00ff

def z849 : W := mkw 0x10498b2ccf7776c1 0x4209316599eeeed8 0xf8ffef3ccfffffc7 0xff1ffde799fffff8

def z850 : W := mkw 0x34e3cfc8ca787496 0x469c79f9194f0e92 0x60e3cfc0c0787800 0x8c1c79f8180f0f00

def z851 : W := mkw 0x06b6400003111000 0x00d6c80000622200 0xcfffc00003fff805 0xf9fff800007fff00

def z852 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xefe47fc00ff807ff 0xfdfc8ff801ff00ff

def z853 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x9f3c703f0f9f9fff 0x73e78e07e1f3f3ff

def z854 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x80dba71c0c0007c6 0x301b74e3818000f8

def z855 : W := mkw 0x0009022c84060241 0x000120459080c048 0x90dba73c0c0607c7 0x321b74e78180c0f8

def z856 : W := mkw 0x0b1c34b725878369 0x81638696e4b0f06d 0x9f1c30ff3f8787ff 0x73e3861fe7f0f0ff

def z857 : W := mkw 0x10498b0c8c6444c1 0x42093161918c8898 0x20dbaf1c0c0007c2 0x241b75e3818000f8

def z858 : W := mkw 0x10498b2dcc66e6c9 0x42093165b98cdcd9 0xf8fffffffc67e7ff 0xff1fffffff8cfcff

def z859 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xf8e47fe3f07ffe3f 0xff1c8ffc7e0fffc7

def z860 : W := mkw 0x25e2fdc05af87db6 0x24bc5fb80b5f0fb6 0xefe3ffc0fff87ffe 0xfdfc7ff81fff0fff

def z861 : W := mkw 0x10498b2ddc66eec9 0x62093165bb8cddd9 0xf0dbaf3ffc6667c7 0xbe1b75e7ff8cccf8

def z862 : W := mkw 0x0314301200800120 0x0062860240100024 0x8f18301c0f8007fe 0x71e3060381f000ff

def z863 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x80dba71c0c0601c5 0x301b74e38180c038

def z864 : W := mkw 0x27b674d220880136 0x04f6ce9a44110026 0x072450c330000038 0x40e48a1866000007

def z865 : W := mkw 0x1001030c800000c1 0x4200206190000018 0x00dba71c000001c0 0x201b74e380000038

def z866 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xfffffffff0199803 0xfffffffffe033300

def z867 : W := mkw 0x1049832ccc4662c1 0x420930659988cc58 0xd0dba73ccc0667c7 0x3a1b74e79980ccf8

def z868 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xf7fffffff0666007 0xfefffffffe0ccc00

def z869 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x70dbaf3ccc0667c3 0x2e1b75e79980ccf8

def z870 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x00dba71c0c0007c0 0x201b74e3818000f8

def z871 : W := mkw 0x04e880000f555000 0x009d100001eaaa00 0xcffb80000ffff805 0xf9ff700001ffff00

def z872 : W := mkw 0x07b7769aa0800120 0x00f6eed354100024 0xfffffffff380003b 0xfffffffffe700007

def z873 : W := mkw 0x0001020880000000 0x0000204110000000 0xf0dbbffff0000003 0xbe1b77fffe000000

def z874 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xafe47fc33ff807fe 0xf5fc8ff867ff00ff

def z875 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0fbbffccc6667c7 0xfe1f77ff998cccf8

def z876 : W := mkw 0x04a34688a0000000 0x009468d114000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z877 : W := mkw 0x0108300404840161 0x002106008090802c 0x8f18301c0f8007fe 0x71e3060381f000ff

def z878 : W := mkw 0x34e18fc88a784496 0x469c31f9114f0892 0x20e38fc000780000 0x841c71f8000f0000

def z879 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x2fe02fc00ff807fc 0xa5fc05f801ff00ff

def z880 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x4fdfc0000ffff805 0x29fbf80001ffff00

def z881 : W := mkw 0x10498b2ddc66eec9 0x62093165bb8cddd9 0xf0dbaf3ccc67ffc7 0xbe1b75e7998cfff8

def z882 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xfffffffff000063f 0xfffffffffe0000c7

def z883 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xeffbbfc00ff807ff 0xfdff77f801ff00ff

def z884 : W := mkw 0x0315321a80000000 0x0062a64350000000 0xf7fffffff0000003 0xfefffffffe000000

def z885 : W := mkw 0x1049830c8f5550c1 0x4209306191eaaa18 0x08dba71c0ffff9c4 0x211b74e381ffff38

def z886 : W := mkw 0x07b7769aa2100000 0x00f6eed354420000 0xfffffffff3980003 0xfffffffffe730000

def z887 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x70dbaf3cc06667c3 0x8e1b75e7980cccf8

def z888 : W := mkw 0x05e03d8008e005a0 0x00bc07b0011c00b4 0xafe03fc00fe007fe 0xf5fc07f801fc00ff

def z889 : W := mkw 0x10498b2ddc66eec9 0x62093165bb8cddd9 0xf0fffffffc67ffc7 0xfe1fffffff8cfff8

def z890 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xf7dbbffff0000003 0xbefb77fffe000000

def z891 : W := mkw 0x0b1ef0375587fb69 0xa163de06eab0ff6d 0xdf1ff03fff87ffff 0x7be3fe07fff0ffff

def z892 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x9f3c70ff3f8787ff 0x73e78e1fe7f0f0ff

def z893 : W := mkw 0x0b1c30375587ab69 0xa1638606eab0f56d 0x9f1c303f0f87ffff 0x73e38607e1f0ffff

def z894 : W := mkw 0x0900301600800161 0x81200602c010002c 0x8f00301c0f8007fe 0x71e0060381f000ff

def z895 : W := mkw 0x0b1c301705858169 0x81638602e0b0b02d 0x8f1c301f0f8187fe 0x71e38603e1f030ff

def z896 : W := mkw 0x031c301205850120 0x0063860240b0a024 0x9f1c303f0f8787ff 0x73e38607e1f0f0ff

def z897 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf8dfbffffc67e7ff 0xff1bf7ffff8cfcff

def z898 : W := mkw 0x06f6c0000b515000 0x00ded800016a2a00 0xcfe7c00003fff805 0xd9fcf800007fff00

def z899 : W := mkw 0x25e03dd22af805b6 0x04bc07ba455f00b6 0xafe03fc33ff807fe 0xf5fc07f867ff00ff

def z900 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x4f3fc0000ffff805 0x49e7f80001ffff00

def z901 : W := mkw 0x0001022c80020241 0x0000204590004048 0xf0dbaf3cc00007c3 0xbe1b75e7980000f8

def z902 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xcfffe0000fffffc7 0xf9fffc0001fffff8

def z903 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xf7fffffff0787803 0xfefffffffe0f0f00

def z904 : W := mkw 0x05a0348000800120 0x00b4069000100024 0x8fc037000f8007fe 0x71f806e001f000ff

def z905 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xcfffd0000ffffe3f 0xf9fffa0001ffffc7

def z906 : W := mkw 0x14e3cb48da787c94 0x629c79691b4f0f92 0x60e3cfc0f0787800 0x8c1c79f81e0f0f00

def z907 : W := mkw 0x0fb6749320808128 0x81f6ce9264101025 0x072450c330000038 0x40e48a1866000007

def z908 : W := mkw 0x0000084000280414 0x0000010800050082 0xf82458e3f07ffe3f 0xdf048b1c7e0fffc7

def z909 : W := mkw 0x004889240c6646c1 0x00091124818cc8d8 0xf0dbaf3c0c6667c7 0xbe1b75e7818cccf8

def z910 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xa7c03fc00fe007fe 0xb4f807f801fc00ff

def z911 : W := mkw 0x10498b0ccc6464c1 0x42093161998c8c98 0x00dba71c0c6061c0 0x201b74e3818c0c38

def z912 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0dfbf3fcc6667c7 0xfe1bf7e7f98cccf8

def z913 : W := mkw 0x031c303604860361 0x00638606c090c06c 0x9f1c303f0f8607ff 0x73e38607e1f0c0ff

def z914 : W := mkw 0x06b7469aa0000000 0x00d6e8d354000000 0xf0ffdffff0000003 0xde1ffbfffe000000

def z915 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x9f18303f0f8007fe 0x73e30607e1f000ff

def z916 : W := mkw 0x0041030888400080 0x0008206111080010 0x00dba71c0c0001c0 0x201b74e381800038

def z917 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xffe47fe3ffffffff 0xfffc8ffc7fffffff

def z918 : W := mkw 0x025c80000f555000 0x004b900001eaaa00 0xcfdf80000ffff805 0xf9fbf00001ffff00

def z919 : W := mkw 0x10498b4cdc6c6cd5 0x620931699b8d8d9a 0x60fbefdcfc7879c0 0xac1f7dfb9f8f0f38

def z920 : W := mkw 0x10010b2cc02226c1 0x42002165980444d8 0xf0dbaf3cc06667c7 0xbe1b75e7980cccf8

def z921 : W := mkw 0x25e035c00ad801b6 0x04bc06b8015b0036 0x8fe037c00f9807fe 0x71fc06f801f300ff

def z922 : W := mkw 0x0908303704868369 0x81210606e090d06d 0x9f18303f0f8607ff 0x73e30607e1f0c0ff

def z923 : W := mkw 0x1009822cc4066241 0x420130459880cc48 0xf0dbaf3ccc0667c7 0xbe1b75e79980ccf8

def z924 : W := mkw 0x07b7769aa0800120 0x00f6eed354100024 0xf7fffffff00007fb 0xfefffffffe0000ff

def z925 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x60dbaf1ccc0001c0 0xac1b75e399800038

def z926 : W := mkw 0x0efec0160f555041 0x81dfd802c1eaaa08 0xcfffc01c0ffff805 0xf9fff80381ffff00

def z927 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x80dba71c0c6001c4 0xb01b74e3818c0038

def z928 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf8fbbffccc7fffff 0xff1f77ff998fffff

def z929 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x50dba73ccc0001c1 0x2a1b74e799800038

def z930 : W := mkw 0x07b6749220800120 0x00f6ce9244100024 0x0f2450c333800038 0x41e48a1866700007

def z931 : W := mkw 0x00410b0888600480 0x00082161110c0090 0xa0dbaf1c0c6007c6 0xb41b75e3818c00f8

def z932 : W := mkw 0x025c80000d454000 0x004b900001a8a800 0xcfffc0000ffff805 0xf9fff80001ffff00

def z933 : W := mkw 0x06fec0120f555000 0x00dfd80241eaaa00 0xdfffc03f0ffff805 0xfbfff807e1ffff00

def z934 : W := mkw 0x10498b6ccc6e66d5 0x4209316d998dccda 0xf0fbaffccc7e67c7 0xbe1f75ff998fccf8

def z935 : W := mkw 0x1049832ccc4662c1 0x420930659988cc58 0xd0dba73ccc6661c5 0xba1b74e7998ccc38

def z936 : W := mkw 0x0900303700828369 0x81200606e010506d 0x1700303f0f8007fa 0x22e00607e1f000ff

def z937 : W := mkw 0x10498b0ccc6464c1 0x42093161998c8c98 0xf0dbaf3ccc6061c3 0xbe1b75e7998c0c38

def z938 : W := mkw 0x1049832d8c46c2c9 0x42093065b188d859 0x98dfb73f0c0787ff 0x731bf6e7e180f0ff

def z939 : W := mkw 0x0100300000800120 0x0020060000100024 0xafc03f000f8007fe 0xf5f807e001f000ff

def z940 : W := mkw 0x10498b0c8c6444c1 0x42093161918c8898 0x00dba71c0c6007c4 0x201b74e3818c00f8

def z941 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x9f3c303f0fff87ff 0xf3e78607e1fff0ff

def z942 : W := mkw 0x0b1ef0370587d369 0x8163de06e0b0fa6d 0xdf3ff03f0fffffff 0xfbe7fe07e1ffffff

def z943 : W := mkw 0x0041030888400080 0x0008206111080010 0xf0dbaf3ccc0001c3 0xbe1b75e799800038

def z944 : W := mkw 0x25e035800ad001a2 0x04bc06b0015a0034 0xafe03fc00f8007fe 0xf5fc07f801f000ff

def z945 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x60dbaf1ccc6667c4 0xac1b75e3998cccf8

def z946 : W := mkw 0x19013b7fd0aaaffd 0xe320276ffa1555ff 0x30003ffff00007fa 0x060007fffe0000ff

def z947 : W := mkw 0x0908303705878369 0x81210606e0b0f06d 0x9f00303f0f8787fe 0x73e00607e1f0f0ff

def z948 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xffffffffff800007 0xfffffffffff00000

def z949 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf0ffeffffc7fffc7 0xbe1ffdffff8ffff8

def z950 : W := mkw 0x0a1c003705878369 0x81438006e0b0f06d 0x9f1c003f0f8787fd 0x73e38007e1f0f0ff

def z951 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x50dba73ccc6667c5 0x2a1b74e7998cccf8

def z952 : W := mkw 0x0a1d023f85078249 0x8143a047f0a0f049 0x501f803fc0078001 0x0a03f007f800f000

def z953 : W := mkw 0x21403dc00af805b6 0x042807b8015f00b6 0xaf003fc00ff807fe 0x75e007f801ff00ff

def z954 : W := mkw 0x0101369aa0000000 0x002026d354000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z955 : W := mkw 0x25e03dd20af805b6 0x04bc07ba415f00b6 0xbfe03fff0ff807fe 0xf7fc07ffe1ff00ff

def z956 : W := mkw 0x0314303300828328 0x0062860660105065 0x9f1c303f0f8787ff 0x73e38607e1f0f0ff

def z957 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xdf1c303f0fe7e7ff 0xfbe38607e1fcfcff

def z958 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xf8ffd8e3f07ffe3f 0xff1ffb1c7e0fffc7

def z959 : W := mkw 0x00000961502aae9c 0x2000012c2a0555d3 0xf8247fe3f07fffff 0xdf048ffc7e0fffff

def z960 : W := mkw 0x0b1c301605850161 0x81638602c0b0a02c 0x0f18201c0f8007fc 0x21e3040381f000ff

def z961 : W := mkw 0x00090a2cc4262641 0x000121459884c4c8 0xf0dbaf3ccc6667c7 0xbe1b75e7998cccf8

def z962 : W := mkw 0x10498b6ccc6e66d5 0x4209316d998dccda 0xf0dbbffccc6667ff 0xbe1b77ff998cccff

def z963 : W := mkw 0x10498b0c8c6444c1 0x42093161918c8898 0xf0dbaf3ccc6007c7 0xbe1b75e7998c00f8

def z964 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x30dbaf3ccc0001c2 0x261b75e799800038

def z965 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xff2458e3fffffe3f 0xffe48b1c7fffffc7

def z966 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xdfffe03c0ffff807 0xfbfffc0781ffff00

def z967 : W := mkw 0x00410b4888680494 0x00082169110d0092 0xf8fffffffc7807ff 0xff1fffffff8f00ff

def z968 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xbfdc3f3f0f8787ff 0xf7fb87e7e1f0f0ff

def z969 : W := mkw 0x0fb674d33189893c 0xa1f6ce9a66313127 0x0f2450c333999838 0x41e48a1866733307

def z970 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xefffef000ffff807 0xfdfffde001ffff00

def z971 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf0dffffffc67ffff 0xbe1bffffff8cffff

def z972 : W := mkw 0x1049832ccc4662c1 0x420930659988cc58 0x10dba73ccc0001c0 0x221b74e799800038

def z973 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0dfef3ffc6667c7 0xbe1bfde7ff8cccf8

def z974 : W := mkw 0x0b1c30375587ab69 0xa1638606eab0f56d 0xdf3c703fffffffff 0xfbe78e07ffffffff

def z975 : W := mkw 0x10498b2dcc66e6c9 0x42093165b98cdcd9 0xf0dbbf3fcc6667ff 0xbe1b77e7f98cccff

def z976 : W := mkw 0x0fb7769aa1810120 0x81f6eed354302024 0xf7fffffff3800003 0xfefffffffe700000

def z977 : W := mkw 0x10418b08c8606480 0x42083161190c0c90 0xf0dbaf3ccc6067c7 0xbe1b75e7998c0cf8

def z978 : W := mkw 0x07b7769aa0800120 0x00f6eed354100024 0xf7ffffffff8001c3 0xfefffffffff00038

def z979 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0x30dbaf3ccc6667c6 0x261b75e7998cccf8

def z980 : W := mkw 0x0a1c002505878369 0x81438004a0b0f06d 0x9f1c203c0f8787ff 0x73e3840781f0f0ff

def z981 : W := mkw 0x25e03dc05af82db6 0x24bc07b80b5f05b6 0xffe47fe3fff87fff 0xfffc8ffc7fff0fff

def z982 : W := mkw 0x0217421aa0000000 0x0042e84354000000 0xf0fffffff0000003 0xfe1ffffffe000000

def z983 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xf7fffffffc0007c7 0xfeffffffff8000f8

def z984 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0dfef3ccc67ffc7 0xbe1bfde7998cfff8

def z985 : W := mkw 0x04e009400a780494 0x009c0128014f0092 0xafe03fc00ff807fe 0xf5fc07f801ff00ff

def z986 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xefffc8c0fffff805 0xfdfff9181fffff00

def z987 : W := mkw 0x00000061500aaa1c 0x2000000c2a015543 0xd82450e3f07ff83d 0xdb048a1c7e0fff07

def z988 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf8fbeffcfc7fffff 0xbf1f7dff9f8fffff

def z989 : W := mkw 0x04e880000e544000 0x009d100001ca8800 0xcfffc0000ffff805 0xf9fff80001ffff00

def z990 : W := mkw 0x07b7769aa3111000 0x00f6eed354622200 0xfffffffff3fff807 0xfffffffffe7fff00

def z991 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x582450e3f07ffe3d 0x4b048a1c7e0fffc7

def z992 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x0fe037c00ff807fc 0x61fc06f801ff00ff

def z993 : W := mkw 0x1a1fc23fe507e249 0xc343f847fca0fc49 0x501fc03ff007e001 0x0a03f807fe00fc00

def z994 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x8ffb80000ffff804 0xf1ff700001ffff00

def z995 : W := mkw 0x031c302405870361 0x0063860480b0e06c 0x9f1c303c0f8787ff 0x73e3860781f0f0ff

def z996 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xdf1c703fff8787ff 0x7be38e07fff0f0ff

def z997 : W := mkw 0x06f640000a500000 0x00dec800014a0000 0xcfffc0000ffff805 0xf9fff80001ffff00

def z998 : W := mkw 0x04e2c0000a505000 0x009c5800014a0a00 0xcfe7c0000ffff805 0xf9fcf80001ffff00

def z999 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xdf1c703f0f87ffff 0x7be38e07e1f0ffff

def z1000 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x8f18301c0f8787fe 0x71e3060381f0f0ff

def z1001 : W := mkw 0x00410b69d86aae9c 0x2008216d3b0d55d3 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z1002 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xafc02f000ff807fe 0xb5f805e001ff00ff

def z1003 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xefe03fc00ffe67ff 0xfdfc07f801ffccff

def z1004 : W := mkw 0x25e2fdc00af855b6 0x04bc5fb8015f0ab6 0xafe3bfc00ff807fe 0xf5fc77f801ff00ff

def z1005 : W := mkw 0x0100348000800120 0x0020069000100024 0xaf003fc00f8007fe 0x75e007f801f000ff

def z1006 : W := mkw 0x34e3cfc8ea786496 0x469c79f91d4f0c92 0x60e3cfc0f0786000 0x8c1c79f81e0f0c00

def z1007 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xdfffd0230ffff807 0xfbfffa0461ffff00

def z1008 : W := mkw 0x24e00dc00af805b6 0x049c01b8015f00b6 0xafe00fc00ff807fc 0xf5fc01f801ff00ff

def z1009 : W := mkw 0x0cab46ada5878369 0x819568d5b4b0f06d 0x68e3cfc0ff8787fc 0x8d1c79f81ff0f0ff

def z1010 : W := mkw 0x0049822c8c464241 0x000930459188c848 0xf0dbaf3ccc6667c7 0xbe1b75e7998cccf8

def z1011 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x77ffeffff0000001 0xaefffdfffe000000

def z1012 : W := mkw 0x00010b0880200480 0x0000216110040090 0xf0dbaf3cc00007c3 0xbe1b75e7980000f8

def z1013 : W := mkw 0x025ec0000f555000 0x004bd80001eaaa00 0xcf1fc0000ffff805 0x79e3f80001ffff00

def z1014 : W := mkw 0x0a1f423fa5078249 0x8143e847f4a0f049 0x101f803f00078001 0x0203f007e000f000

def z1015 : W := mkw 0x0140310008c001a0 0x0028062001180034 0x8fc037000f8007fe 0x71f806e001f000ff

def z1016 : W := mkw 0x1001030c800000c1 0x4200206190000018 0xf0dbaf3cc00001c3 0xbe1b75e798000038

def z1017 : W := mkw 0x1049830ccc4460c1 0x4209306199888c18 0x40dba71ccc0061c0 0x281b74e399800c38

def z1018 : W := mkw 0x07b7769aa1011000 0x00f6eed354202200 0xf7fffffff0019803 0xfefffffffe003300

def z1019 : W := mkw 0x06fec4800f555000 0x00dfd89001eaaa00 0xefffcfc00ffff805 0xfdfff9f801ffff00

def z1020 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xf82478e3fc7fffff 0xff048f1c7f8fffff

def z1021 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0dbaf3ccc0007c3 0xbe1b75e7998000f8

def z1022 : W := mkw 0x0fb67cf371abaf3c 0xa1f6cf9e6e3575e7 0xff2458e3f3fffe3f 0xdfe48b1c7e7fffc7

def z1023 : W := mkw 0x25e035800ad001a2 0x04bc06b0015a0034 0x8fe037000ff807fe 0xf1fc06e001ff00ff

def z1024 : W := mkw 0x27b674d222980136 0x04f6ce9a44530026 0x0f2010c003980038 0x41e4021800730007

def z1025 : W := mkw 0x0009022d84068249 0x00012045b080d049 0xf8fffffffc0787ff 0xff1fffffff80f0ff

def z1026 : W := mkw 0x1049832c8c4642c1 0x420930659188c858 0xd0dba73c0c6667c7 0xba1b74e7818cccf8

def z1027 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf8fbbffffc7e67ff 0xff1f77ffff8fccff

def z1028 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x77ffdffff0000001 0xcefffbfffe000000

def z1029 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xdf3c703f0f8787ff 0xfbe78e07e1f0f0ff

def z1030 : W := mkw 0x10498b6ccc6e66d5 0x4209316d998dccda 0xf8fffffccc7fffff 0xff1fffff998fffff

def z1031 : W := mkw 0x0009020c84040041 0x0001204190808008 0x00dba71c0c0001c0 0x201b74e381800038

def z1032 : W := mkw 0x0b1cb0370587d369 0x81639606e0b0fa6d 0x9f1c303f0f87ffff 0x73e38607e1f0ffff

def z1033 : W := mkw 0x10498b6cdc6e6ed5 0x6209316d9b8dcdda 0xf8ffeffcfc7fffc7 0xff1ffdff9f8ffff8

def z1034 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf8fbaf3ccc7e67c7 0xff1f75e7998fccf8

def z1035 : W := mkw 0x25e03dc01af80db6 0x24bc07b8035f01b6 0xafe07fc03ff81ffe 0xf5fc0ff807ff03ff

def z1036 : W := mkw 0x10498b2cdc666ec1 0x620931659b8ccdd8 0xf0dbef3cfc667fc7 0xbe1b7de79f8ccff8

def z1037 : W := mkw 0x0b1c301605850161 0x81638602c0b0a02c 0x8f1c301c0f8787ff 0x71e3860381f0f0ff

def z1038 : W := mkw 0x0101369aa0000000 0x002026d354000000 0x30dbbffff0000002 0x261b77fffe000000

def z1039 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0x682458c3f07ffe3c 0xcd048b187e0fffc7

def z1040 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xb7dfbffff0000003 0x76fbf7fffe000000

def z1041 : W := mkw 0x10498b2ddc66eec9 0x62093165bb8cddd9 0xf8ffef3ffc7fffc7 0xff1ffde7ff8ffff8

def z1042 : W := mkw 0x0a1f423ff507aa49 0xa143e847fea0f549 0x501fc03ff007f801 0x0a03f807fe00ff00

def z1043 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x40dba71c0c6061c0 0xa81b74e3818c0c38

def z1044 : W := mkw 0x25e27dc00af815b6 0x04bc4fb8015f02b6 0xafe07fc00ff81ffe 0xf5fc0ff801ff03ff

def z1045 : W := mkw 0x10498b0ccc6464c1 0x42093161998c8c98 0xe0dbaf1ccc6067c6 0xbc1b75e3998c0cf8

def z1046 : W := mkw 0x1049832ddc46eac9 0x62093065bb88dd59 0x50dfe73ffc07f9c1 0x2a1bfce7ff80ff38

def z1047 : W := mkw 0x00490b2c8c6606c1 0x00092165918cc0d8 0xf0dbaf3ccc6607c7 0xbe1b75e7998cc0f8

def z1048 : W := mkw 0x21013ffbf0aaafbe 0x242027ff7e1555f7 0x30003ffff00007fa 0x060007fffe0000ff

def z1049 : W := mkw 0x0009020c84040041 0x0001204190808008 0xf0dbaf3ccc0001c3 0xbe1b75e799800038

def z1050 : W := mkw 0x10498b0ccc6464c1 0x42093161998c8c98 0xe0dbaf1ccc6661c5 0xbc1b75e3998ccc38

def z1051 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xffdbaf3ccfe667c7 0xfffb75e799fcccf8

def z1052 : W := mkw 0x27b674d33298893e 0x24f6ce9a66531127 0x0f2450c333999838 0x41e48a1866733307

def z1053 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0xc8ffe71c0c7ff9c5 0xf91ffce3818fff38

def z1054 : W := mkw 0x25e0bdc00af855b6 0x04bc17b8015f0ab6 0xafe03fc00ff87ffe 0xf5fc07f801ff0fff

def z1055 : W := mkw 0x1049830c8f5550c1 0x4209306191eaaa18 0x00dba71c0f8001c0 0x201b74e381f00038

def z1056 : W := mkw 0x35e0bdc04af865b6 0x46bc17b8095f0cb6 0xafe03fc00ff867fe 0xf5fc07f801ff0cff

def z1057 : W := mkw 0x0b1e703725878369 0x8163ce06e4b0f06d 0x9f1c703f3f8787ff 0x73e38e07e7f0f0ff

def z1058 : W := mkw 0x1049832c8c4642c1 0x420930659188c858 0x10dba73c0c0601c1 0x221b74e78180c038

def z1059 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xb0dbaf3ccc0607c7 0x361b75e79980c0f8

def z1060 : W := mkw 0x184889655defeffd 0xe309112cabbdfdff 0x080000000ffffffc 0x0100000001ffffff

def z1061 : W := mkw 0x0b1c303605870361 0x81638606c0b0e06c 0x9f18303c0f8607ff 0x73e3060781f0c0ff

def z1062 : W := mkw 0x10010b2cc02226c1 0x42002165980444d8 0x30dbaf3cc00007c2 0x261b75e7980000f8

def z1063 : W := mkw 0x31013fedd0aaafff 0x662027fdba1555ff 0x30003ffff00007fa 0x060007fffe0000ff

def z1064 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf8dfbf3fcc7fffff 0xff1bf7e7f98fffff

def z1065 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf8dbbf3ccc6667ff 0xff1b77e7998cccff

def z1066 : W := mkw 0x0b14303700828369 0x81628606e010506d 0x9f1c303f0f8007ff 0x73e38607e1f000ff

def z1067 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xafe47fc00ff99ffe 0xf5fc8ff801ff33ff

def z1068 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xfffffffff0780007 0xfffffffffe0f0000

def z1069 : W := mkw 0x0100301200800120 0x0020060240100024 0x9f00303f0f8007fe 0x73e00607e1f000ff

def z1070 : W := mkw 0x21003dc000a805b6 0x042007b8001500b6 0x27003fc00f8007fa 0x24e007f801f000ff

def z1071 : W := mkw 0x2fb674d30399913e 0x85f6ce9a60733227 0x0f2450c303999838 0x41e48a1860733307

def z1072 : W := mkw 0x06fec0122f555000 0x00dfd80245eaaa00 0xcfffc0033ffff805 0xf9fff80067ffff00

def z1073 : W := mkw 0x10498b2ddc66eec9 0x62093165bb8cddd9 0xf8dfff3ffc67ffff 0xff1bffe7ff8cffff

def z1074 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x77fbfffff0000002 0xaeff7ffffe000000

def z1075 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x171c303f0f8787fb 0x22e38607e1f0f0ff

def z1076 : W := mkw 0x10498b2ccd6766c1 0x4209316599acecd8 0xf8dbaf3ccfe7e7c7 0xbf1b75e799fcfcf8

def z1077 : W := mkw 0x10418b2cc86266c1 0x42083165990c4cd8 0xf0dbaf3cc06067c3 0xbe1b75e7980c0cf8

def z1078 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0dbbffffc6667c7 0xbe1b77ffff8cccf8

def z1079 : W := mkw 0x27b67cd222b80536 0x04f6cf9a445700a6 0xff2458e3f3f8063f 0xdfe48b1c7e7f00c7

def z1080 : W := mkw 0x25e03dc05af82db6 0x24bc07b80b5f05b6 0xefe47fc0ffffffff 0xfdfc8ff81fffffff

def z1081 : W := mkw 0x24e34fc8aa780496 0x049c69f9154f0092 0x20e38fc000780000 0x841c71f8000f0000

def z1082 : W := mkw 0x24e3cfc8aa785496 0x049c79f9154f0a92 0x60e3cfc0f0787800 0x8c1c79f81e0f0f00

def z1083 : W := mkw 0x0b14303701838369 0x81628606e030706d 0x9f04303f0f8187fe 0x73e08607e1f030ff

def z1084 : W := mkw 0x10498b0ccc6464c1 0x42093161998c8c98 0x20dbaf1ccc0001c0 0x241b75e399800038

def z1085 : W := mkw 0x0900303700828369 0x81200606e010506d 0x9f04303f0f8787ff 0x73e08607e1f0f0ff

def z1086 : W := mkw 0x04eac0000f555000 0x009d580001eaaa00 0xcfe3c0000ffff804 0xf9fc780001ffff00

def z1087 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x2fe03fc00f9807fa 0x65fc07f801f300ff

def z1088 : W := mkw 0x25e03dc04af825b6 0x04bc07b8095f04b6 0xefe03fc0cff867fe 0xfdfc07f819ff0cff

def z1089 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x9f18203c0f8787ff 0x33e3040781f0f0ff

def z1090 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0x08dba71c0c7ffffc 0x211b74e3818fffff

def z1091 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x07c027000f8007f8 0x20f804e001f000ff

def z1092 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xffe03fe0cff807ff 0xfffc07fc19ff00ff

def z1093 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf0fbfffffc7e7fff 0xbe1f7fffff8fcfff

def z1094 : W := mkw 0x07b7769aa2101000 0x00f6eed354420200 0xf7fffffff0181803 0xfefffffffe030300

def z1095 : W := mkw 0x10498b2c8c6646c1 0x42093165918cc8d8 0xb0dbaf3c0c6607c7 0xb61b75e7818cc0f8

def z1096 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0xf7fffffff007f803 0xfefffffffe00ff00

def z1097 : W := mkw 0x05e034800ad00120 0x00bc0690015a0024 0xafe03fc00ff807fe 0xf5fc07f801ff00ff

def z1098 : W := mkw 0x0908302505878369 0x81210604a0b0f06d 0x9f18303c0f8787ff 0x73e3060781f0f0ff

def z1099 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0x40dba71c0c0661c1 0x281b74e38180cc38

def z1100 : W := mkw 0x18498b2dcd67e6c9 0xc3093165b9acfcd9 0xf0dbaf3ccc67e7c7 0xbe1b75e7998cfcf8

def z1101 : W := mkw 0x27b67cf372baaf3e 0x24f6cf9e6e5755e7 0xff2458e3f3fffe3f 0xdfe48b1c7e7fffc7

def z1102 : W := mkw 0x10498b2ccf7776c1 0x4209316599eeeed8 0xf0dbaf3ccfe667c7 0xbe1b75e799fcccf8

def z1103 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xbfe03fe3fff807fe 0xf7fc07fc7fff00ff

def z1104 : W := mkw 0x0fb6749323919128 0x81f6ce9264723225 0x0f2450c333999838 0x41e48a1866733307

def z1105 : W := mkw 0x27b674d223991136 0x04f6ce9a44732226 0x0f2450c333999838 0x41e48a1866733307

def z1106 : W := mkw 0x10498b2ccd6776c1 0x4209316599aceed8 0xf0dbaf3ccc67ffc7 0xbe1b75e7998cfff8

def z1107 : W := mkw 0x00090a6dd42eae5d 0x2001214dba85d5cb 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z1108 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xf0fbef3ccc7e7fc7 0xbe1f7de7998fcff8

def z1109 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xbfe43fe30ff807ff 0xf7fc87fc61ff00ff

def z1110 : W := mkw 0x00498b088c644480 0x00093161118c8890 0xf0dbaf3ccc6667c7 0xbe1b75e7998cccf8

def z1111 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xb0dbaf3ccc6007c6 0xb61b75e7998c00f8

def z1112 : W := mkw 0x06be400005050000 0x00d7c80000a0a000 0xcfffc0000ffff805 0xf9fff80001ffff00

def z1113 : W := mkw 0x25a03dc000a805b6 0x04b407b8001500b6 0xafe03fc00f8007fe 0xf5fc07f801f000ff

def z1114 : W := mkw 0x10498b6ccc6e66d5 0x4209316d998dccda 0xf8dbaf3ccc7e67ff 0xbf1b75e7998fccff

def z1115 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x8f1c201c0f8787fd 0x71e3840381f0f0ff

def z1116 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x0fffc0000ffff804 0x61fff80001ffff00

def z1117 : W := mkw 0x21003580008001a2 0x042006b000100034 0x8f0037000f8007fe 0x71e006e001f000ff

def z1118 : W := mkw 0x10498b2dcc66e6c9 0x42093165b98cdcd9 0xf0dfaf3fcc67e7c7 0xbe1bf5e7f98cfcf8

def z1119 : W := mkw 0x10000965502aaedd 0x6200012caa0555db 0xf82458e3f07fffff 0xdf048b1c7e0fffff

def z1120 : W := mkw 0x10498b6ccc6e66d5 0x4209316d998dccda 0xf8fffffffc7e67ff 0xff1fffffff8fccff

def z1121 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x37fffffff0000002 0x66fffffffe000000

def z1122 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xefffd8c00ffff807 0xfdfffb1801ffff00

def z1123 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x4fe7c0000ffff804 0xc9fcf80001ffff00

def z1124 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf8dfef3ffc7fffff 0xbf1bfde7ff8fffff

def z1125 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xbf1c38ffff8787ff 0x77e3871ffff0f0ff

def z1126 : W := mkw 0x25e03d800af005a2 0x04bc07b0015e00b4 0xafc03f000fe007fe 0xf5f807e001fc00ff

def z1127 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x1f04303f0f8787fe 0x43e08607e1f0f0ff

def z1128 : W := mkw 0x0b1cb0370587c369 0x81639606e0b0f86d 0xdf1fb03f0f87e7ff 0x7be3f607e1f0fcff

def z1129 : W := mkw 0x0b1e703705879369 0x8163ce06e0b0f26d 0x9f1c703f0f879fff 0x73e38e07e1f0f3ff

def z1130 : W := mkw 0x0100390000a005a0 0x00200720001400b4 0xaf003f000f8007fe 0x75e007e001f000ff

def z1131 : W := mkw 0x00000861502aae1c 0x2000010c2a0555c3 0xf83c78fff07ffe3f 0xff078f1ffe0fffc7

def z1132 : W := mkw 0x05a03cc000a80534 0x00b40798001500a6 0xafe03fc00ff807fe 0xf5fc07f801ff00ff

def z1133 : W := mkw 0x24e34fc8fa782c96 0x249c69f91f4f0592 0x60e3cfc0f0787800 0x8c1c79f81e0f0f00

def z1134 : W := mkw 0x0b1c34b705878369 0x81638696e0b0f06d 0xbf1c3fff0f8787ff 0x77e387ffe1f0f0ff

def z1135 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x1f18303f0f8787fe 0x23e30607e1f0f0ff

def z1136 : W := mkw 0x10498b6cdc6e6ed5 0x6209316d9b8dcdda 0xf0dbaf3ccc7e7fc7 0xbe1b75e7998fcff8

def z1137 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0xafc03fc00f8007fe 0x75f807f801f000ff

def z1138 : W := mkw 0x10498b0c8c6444c1 0x42093161918c8898 0xe0dbaf1c0c6667c7 0xbc1b75e3818cccf8

def z1139 : W := mkw 0x10410b2cc86226c1 0x42082165990c44d8 0xf0dbaf3ccc6007c7 0xbe1b75e7998c00f8

def z1140 : W := mkw 0x214039400af805b6 0x04280728015f00b6 0xafc03f000ff807fe 0xf5f807e001ff00ff

def z1141 : W := mkw 0x10498b6cdc6e6ed5 0x6209316d9b8dcdda 0xf0fffffffc7e7fc7 0xfe1fffffff8fcff8

def z1142 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x1f1c103f0f8787fd 0x43e38207e1f0f0ff

def z1143 : W := mkw 0x0b1c30374587a369 0x81638606e8b0f46d 0xdf1c303fcf87e7ff 0x7be38607f9f0fcff

def z1144 : W := mkw 0x10498b2ccc6666c1 0x42093165998cccd8 0xc0dba71c0c6667c5 0xb81b74e3818cccf8

def z1145 : W := mkw 0x1049832ccc4662c1 0x420930659988cc58 0x00dba71c0c0661c0 0x201b74e38180cc38

def z1146 : W := mkw 0x10498b2dcc66e6c9 0x42093165b98cdcd9 0xf8ffff3fcc7fffff 0xff1fffe7f98fffff

def z1147 : W := mkw 0x1a1d023fc507a249 0xc343a047f8a0f449 0x101c003fc0078001 0x02038007f800f000

def z1148 : W := mkw 0x09013efff0aaaf7d 0xa12027dffe1555ef 0x30003ffff00007fa 0x060007fffe0000ff

def z1149 : W := mkw 0x06fec4802f555000 0x00dfd89005eaaa00 0xcfffc0c03ffff805 0xf9fff81807ffff00

def z1150 : W := mkw 0x0fb6749321818128 0x81f6ce9264303025 0x0f04100303818038 0x41e0820060703007

def z1151 : W := mkw 0x21403dc008e805b6 0x042807b8011d00b6 0xafc03fc00fe007fe 0xf5f807f801fc00ff

def z1152 : W := mkw 0x0b1c303715878b69 0xa1638606e2b0f16d 0x9f1c703f3f879fff 0x73e38e07e7f0f3ff

def z1153 : W := mkw 0x25e03dc00af805b6 0x04bc07b8015f00b6 0x2fc03fc00ff807fe 0x25f807f801ff00ff

def z1154 : W := mkw 0x07b7769aa0000000 0x00f6eed354000000 0x70fffffff0000003 0x8e1ffffffe000000

def z1155 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x4ffbc0000ffff804 0xa9ff780001ffff00

def z1156 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0x4fffc00003fff801 0xc9fff800007fff00

def z1157 : W := mkw 0x34e10fc8ca782496 0x469c21f9194f0492 0x20e00fc0c0780000 0x841c01f8180f0000

def z1158 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0xbf3c38ff0f8787ff 0xf7e7871fe1f0f0ff

def z1159 : W := mkw 0x24e10fc8aa780496 0x049c21f9154f0092 0x20e00fc0f0780000 0x841c01f81e0f0000

def z1160 : W := mkw 0x05a1369aa0000000 0x00b426d354000000 0xf7fbbffff0000003 0xfeff77fffe000000

def z1161 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf0dbaf3ccc6667ff 0xbe1b75e7998cccff

def z1162 : W := mkw 0x0b1c303705878369 0x81638606e0b0f06d 0x0f1c301f0f8787fc 0x61e38603e1f0f0ff

def z1163 : W := mkw 0x25e03dc05af82db6 0x24bc07b80b5f05b6 0xafe03fc0fff807fe 0xf5fc07f81fff00ff

def z1164 : W := mkw 0x06fec0000f555000 0x00dfd80001eaaa00 0xcfdb80000ffff805 0xb9fb700001ffff00

def z1165 : W := mkw 0x1049832c8c4642c1 0x420930659188c858 0x10dba73c0c0007c2 0x221b74e7818000f8

def z1166 : W := mkw 0x24e10fc88a780496 0x049c21f9114f0092 0x60e38fc0c0780000 0x8c1c71f8180f0000

def z1167 : W := mkw 0x1049830c8c4440c1 0x4209306191888818 0xa0dbaf1c0c0001c2 0xb41b75e381800038

def z1168 : W := mkw 0x0100302400820361 0x002006048010406c 0x9f00303c0f8007fe 0x73e0060781f000ff

def z1169 : W := mkw 0x10498b6ddc6eeedd 0x6209316dbb8ddddb 0xf0fffffffc6667ff 0xfe1fffffff8cccff

def z1170 : W := mkw 0x25e035800ad001a2 0x04bc06b0015a0034 0x07c037000f8007fa 0x20f806e001f000ff

def z1171 : W := mkw 0x10498b2dcc66e6c9 0x42093165b98cdcd9 0xf8dbaf3ccc67e7ff 0xbf1b75e7998cfcff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z8,z9,z6]),(0,[z1,z10,z3,z11,z4,z5,z6]),(0,[z1,z12,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z13,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z14])],[(0,[z1,z15,z7,z3,z4,z5,z6]),(0,[z1,z16,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z17,z4,z5,z6]),(0,[z18,z1,z7,z3,z4,z5,z6]),(0,[z1,z19,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z20,z6])],[(0,[z0,z1,z7,z3,z4,z5,z21]),(0,[z1,z7,z3,z4,z22,z23,z6]),(0,[z1,z7,z3,z24,z4,z5,z6]),(0,[z25,z1,z7,z3,z4,z5,z6]),(0,[z1,z26,z27,z7,z4,z5,z6])],[(0,[z28,z1,z7,z3,z4,z5,z29]),(0,[z30,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z31,z4,z5,z6])],[(0,[z1,z7,z3,z4,z32,z5,z6]),(0,[z1,z33,z7,z3,z4,z5,z6]),(0,[z1,z34,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z21,z6]),(0,[z1,z35,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z36,z37]),(0,[z1,z7,z4,z38,z5,z6,z39]),(0,[z1,z40,z7,z41,z3,z4,z6]),(0,[z1,z7,z3,z42,z4,z5,z6])],[(0,[z1,z43,z7,z3,z4,z23,z6]),(0,[z1,z44,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z45]),(0,[z1,z7,z3,z46,z4,z5,z6])],[(0,[z47,z1,z7,z3,z48,z5,z6]),(0,[z1,z49,z7,z3,z4,z5,z6]),(0,[z50,z1,z7,z3,z4,z5,z6]),(1,[z51,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z52,z23,z6]),(0,[z1,z7,z3,z53,z4,z5,z6]),(0,[z1,z54,z7,z3,z4,z5,z6]),(0,[z1,z55,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z56,z5,z6])]],
   [[(0,[z1,z57,z7,z3,z4,z5,z6]),(0,[z1,z58,z7,z3,z4,z5,z6]),(0,[z1,z59,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z60,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z61]),(0,[z1,z7,z3,z4,z9,z6,z62]),(0,[z1,z63,z7,z3,z4,z5,z6]),(0,[z1,z64,z7,z3,z4,z38,z6]),(0,[z1,z65,z7,z3,z4,z5,z6])],[(0,[z66,z1,z7,z3,z4,z23,z6]),(0,[z1,z3,z4,z5,z67,z6,z68]),(0,[z1,z69,z7,z3,z70,z5,z6])],[(0,[z0,z1,z7,z3,z4,z23,z6]),(1,[z1,z71,z3,z4,z5,z68])],[(0,[z1,z7,z3,z11,z4,z23,z6]),(0,[z1,z7,z3,z72,z4,z9,z6]),(0,[z1,z7,z3,z73,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z74])],[(0,[z1,z7,z3,z4,z23,z6,z75]),(0,[z76,z1,z7,z3,z4,z9,z6]),(0,[z1,z77,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z78,z6]),(0,[z1,z79,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z80])],[],[(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z81,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z82,z6]),(0,[z28,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z83,z5,z6]),(1,[z1,z16,z7,z4,z5,z39])]],
   [[(0,[z1,z7,z3,z4,z84,z5,z6])],[(0,[z1,z85,z7,z3,z4,z23,z6]),(0,[z1,z7,z86,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z87,z6]),(0,[z1,z7,z3,z4,z88,z5,z6]),(0,[z1,z85,z7,z3,z4,z5,z89])],[(0,[z1,z7,z90,z3,z4,z5,z6]),(0,[z91,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z92,z9,z6]),(0,[z1,z93,z7,z3,z4,z5,z6]),(0,[z1,z94,z7,z3,z4,z5,z6]),(0,[z1,z71,z7,z3,z4,z5,z68]),(0,[z1,z95,z7,z3,z4,z38,z5]),(0,[z1,z96,z7,z3,z4,z5,z6]),(0,[z1,z97,z7,z3,z4,z5,z98]),(0,[z1,z99,z7,z3,z4,z5,z6])],[(0,[z100,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z101,z23,z6]),(0,[z1,z7,z3,z102,z4,z5,z6]),(0,[z1,z7,z3,z103,z4,z5,z6])],[(0,[z1,z7,z3,z4,z104,z6,z80])],[(1,[z1,z7,z3,z48,z5,z6]),(0,[z0,z1,z7,z4,z105,z5,z6]),(0,[z106,z1,z7,z3,z4,z9,z6]),(0,[z1,z107,z7,z3,z108,z4,z6])],[(0,[z1,z7,z3,z4,z109,z5,z6]),(0,[z1,z7,z3,z4,z110,z9,z6]),(0,[z1,z10,z111,z7,z4,z5,z6]),(1,[z1,z7,z3,z4,z112,z6])],[(0,[z113,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z9,z6,z68]),(0,[z1,z7,z3,z4,z114,z5,z6]),(0,[z1,z115,z7,z3,z4,z116,z6]),(0,[z1,z7,z3,z117,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z118])]],
   [[(0,[z28,z7,z3,z4,z5,z6,z37])],[(0,[z1,z7,z3,z4,z119,z9,z6]),(0,[z1,z7,z3,z4,z5,z6,z120]),(0,[z121,z1,z7,z3,z4,z5,z6])],[(0,[z1,z122,z7,z3,z4,z23,z6]),(0,[z1,z7,z123,z3,z4,z5,z6]),(0,[z1,z124,z7,z3,z4,z116,z6]),(0,[z1,z7,z3,z4,z125,z5,z6]),(0,[z1,z7,z3,z126,z4,z5,z6]),(0,[z1,z71,z7,z3,z4,z5,z6]),(0,[z127,z1,z7,z3,z4,z5,z6]),(0,[z1,z107,z7,z41,z4,z5,z6])],[(0,[z128,z1,z7,z3,z4,z5,z6]),(0,[z1,z129,z7,z3,z4,z5,z6])],[(0,[z1,z7,z130,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z131,z6]),(0,[z1,z132,z7,z3,z4,z5,z6])],[(0,[z1,z85,z7,z3,z4,z5,z67]),(0,[z133,z1,z7,z3,z4,z5,z6])],[(0,[z134,z1,z7,z3,z4,z5,z6]),(0,[z50,z1,z7,z3,z4,z82,z6]),(0,[z1,z135,z7,z3,z4,z5,z6]),(0,[z1,z136,z7,z3,z4,z9,z6])],[(0,[z137,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z138,z4,z5,z6]),(0,[z1,z7,z3,z4,z139,z5,z6]),(0,[z1,z140,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z5,z29,z68])]],
   [[(0,[z1,z7,z3,z4,z5,z116,z6]),(0,[z1,z7,z3,z4,z5,z6,z141])],[(0,[z1,z142,z7,z3,z4,z5,z6]),(0,[z1,z143,z7,z4,z5,z23,z6]),(0,[z1,z111,z7,z3,z4,z9,z6]),(0,[z1,z144,z7,z3,z4,z5,z6]),(0,[z145,z1,z7,z3,z4,z5,z6]),(0,[z1,z146,z7,z3,z4,z5,z6]),(0,[z1,z40,z7,z3,z5,z98,z6])],[(1,[z1,z7,z3,z147,z5,z6]),(0,[z1,z85,z7,z3,z22,z5,z6]),(0,[z1,z7,z3,z4,z9,z104,z6])],[(0,[z0,z1,z7,z148,z4,z5,z6]),(0,[z106,z1,z7,z3,z4,z5,z149]),(0,[z1,z7,z3,z4,z5,z6,z75])],[(0,[z1,z7,z3,z150,z4,z5,z6]),(0,[z1,z151,z7,z3,z4,z5,z6]),(0,[z1,z7,z152,z3,z4,z5,z6]),(0,[z1,z153,z7,z3,z4,z5,z6]),(0,[z1,z154,z7,z3,z4,z5,z6]),(0,[z155,z1,z7,z3,z4,z9,z6]),(1,[z1,z7,z3,z156,z5,z6]),(0,[z1,z107,z7,z3,z4,z157,z6]),(0,[z1,z158,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z46,z4,z159,z5])],[(0,[z1,z160,z122,z3,z4,z5,z6]),(0,[z1,z161,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z162,z6])],[(0,[z1,z43,z7,z11,z4,z5,z6]),(0,[z1,z7,z3,z4,z163,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z164])],[(0,[z165,z1,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z166,z5,z6])]],
   [[(0,[z1,z7,z3,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z167]),(0,[z1,z168,z7,z3,z4,z5,z6])],[(0,[z1,z169,z7,z3,z4,z5,z6]),(0,[z1,z69,z7,z3,z4,z23,z6]),(0,[z28,z1,z7,z3,z4,z170,z6]),(1,[z1,z40,z7,z3,z98,z6])],[(0,[z1,z7,z3,z4,z171,z5,z6]),(0,[z106,z7,z3,z172,z4,z5,z6]),(0,[z1,z7,z3,z4,z23,z6,z89]),(0,[z1,z7,z3,z4,z5,z6,z173]),(0,[z1,z7,z41,z3,z4,z105,z6]),(0,[z1,z7,z3,z4,z5,z6,z174])],[(0,[z1,z175,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z176,z4,z5,z6])],[(1,[z1,z7,z3,z4,z177,z6])],[(0,[z47,z1,z90,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z178]),(0,[z1,z7,z3,z4,z4,z5,z6]),(0,[z1,z10,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z70,z5,z6])],[(0,[z1,z7,z3,z4,z92,z5,z6]),(0,[z1,z7,z3,z4,z179,z5,z6]),(0,[z1,z7,z3,z4,z9,z180,z6]),(0,[z1,z7,z3,z4,z9,z67,z6]),(1,[z1,z181,z7,z4,z5,z36])],[(0,[z47,z1,z7,z3,z182,z5,z6]),(0,[z183,z7,z90,z3,z4,z5,z6]),(0,[z1,z7,z3,z184,z4,z5,z6]),(0,[z1,z7,z3,z4,z185,z5,z6]),(0,[z1,z186,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z187,z6]),(0,[z1,z7,z188,z3,z4,z5,z6])]],
   [[(0,[z47,z1,z7,z3,z4,z5,z189]),(1,[z1,z7,z3,z4,z5,z190]),(0,[z1,z7,z3,z22,z5,z191,z6]),(0,[z1,z7,z3,z4,z192,z23,z6]),(0,[z1,z7,z193,z3,z4,z5,z6]),(0,[z1,z3,z4,z119,z5,z116,z6]),(0,[z1,z7,z3,z4,z5,z194,z6]),(0,[z1,z7,z3,z4,z5,z195,z98]),(0,[z1,z7,z3,z196,z4,z5,z6])],[(0,[z1,z7,z3,z197,z4,z5,z6]),(0,[z198,z1,z7,z3,z4,z199,z6]),(0,[z106,z1,z7,z3,z4,z5,z6]),(0,[z1,z200,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z201,z6]),(0,[z66,z1,z7,z3,z4,z202,z6]),(0,[z1,z7,z3,z4,z110,z5,z6]),(1,[z1,z160,z3,z101,z5,z6])],[(0,[z1,z7,z41,z3,z4,z23,z6]),(0,[z1,z3,z72,z4,z101,z5,z6]),(0,[z1,z85,z7,z3,z101,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z203]),(0,[z1,z7,z3,z4,z5,z204,z6]),(0,[z1,z205,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z206,z4,z5,z6])],[(0,[z1,z7,z3,z4,z202,z5,z6]),(1,[z1,z207,z3,z4,z5,z6]),(0,[z198,z1,z7,z3,z4,z23,z6]),(0,[z50,z7,z3,z4,z22,z5,z6]),(0,[z1,z208,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z72,z172,z5,z6]),(0,[z1,z7,z3,z4,z119,z5,z6]),(0,[z1,z69,z7,z3,z4,z5,z67]),(1,[z1,z7,z3,z5,z209,z6]),(0,[z1,z210,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z211,z4,z5,z6])],[(0,[z212,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z213,z4,z5,z6]),(0,[z1,z26,z7,z3,z38,z5,z6]),(0,[z1,z27,z7,z4,z5,z6,z39])],[(0,[z214,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z215]),(0,[z1,z7,z3,z216,z4,z5,z6]),(0,[z1,z10,z7,z4,z105,z5,z6]),(0,[z1,z7,z3,z4,z217,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z218,z7,z3,z4,z5,z6]),(0,[z1,z219,z7,z3,z4,z5,z6]),(0,[z1,z71,z3,z4,z5,z6,z68]),(0,[z1,z181,z7,z4,z38,z5,z6]),(0,[z1,z220,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z105,z23,z6]),(0,[z1,z7,z3,z108,z4,z9,z6]),(0,[z1,z107,z7,z11,z4,z5,z6]),(0,[z1,z221,z7,z3,z4,z5,z6]),(0,[z1,z85,z27,z7,z3,z5,z6]),(0,[z1,z16,z7,z4,z5,z6,z39]),(0,[z222,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z108,z192,z5,z6])],[(0,[z47,z1,z7,z223,z4,z5,z6]),(0,[z1,z136,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z224,z4,z5,z6]),(0,[z1,z7,z3,z4,z225,z9,z6]),(0,[z1,z7,z3,z4,z5,z226,z6]),(0,[z1,z227,z7,z3,z4,z5,z6]),(0,[z1,z228,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z229,z4,z5,z6]),(0,[z1,z26,z7,z4,z38,z5,z6])],[(0,[z230,z1,z7,z3,z4,z5,z6]),(0,[z1,z122,z7,z3,z101,z5,z6]),(0,[z1,z7,z3,z4,z5,z231,z6]),(0,[z1,z7,z41,z3,z4,z119,z6]),(0,[z1,z69,z71,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z232,z6]),(0,[z1,z7,z3,z192,z5,z191,z6])],[(1,[z1,z7,z3,z182,z5,z6]),(0,[z1,z183,z7,z3,z4,z9,z6]),(0,[z1,z64,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z233,z6]),(0,[z1,z7,z41,z4,z105,z5,z6]),(0,[z1,z7,z3,z4,z5,z234,z6])],[(1,[z1,z7,z3,z4,z5,z189]),(0,[z1,z7,z3,z4,z5,z235,z6]),(1,[z1,z7,z3,z4,z170,z6]),(0,[z236,z1,z7,z3,z4,z5,z6]),(0,[z237,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z41,z3,z4,z157,z6])],[(0,[z1,z207,z7,z3,z4,z5,z6]),(1,[z1,z43,z10,z4,z5,z6]),(0,[z1,z238,z7,z3,z4,z5,z6]),(0,[z1,z7,z239,z3,z4,z5,z6])]],
   [[(1,[z1,z7,z3,z4,z199,z6]),(0,[z1,z7,z3,z4,z5,z240,z6]),(0,[z1,z241,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z242,z6]),(0,[z1,z40,z7,z3,z5,z191,z6]),(0,[z1,z7,z3,z4,z5,z6,z89])],[(0,[z1,z7,z3,z4,z243,z5,z6]),(0,[z1,z7,z244,z3,z4,z5,z6]),(1,[z1,z7,z3,z245,z4,z5]),(0,[z1,z246,z7,z3,z4,z5,z6])],[(0,[z247,z1,z7,z3,z4,z5,z6]),(1,[z50,z7,z3,z22,z5,z6]),(0,[z1,z248,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z249,z4,z5,z6]),(1,[z1,z7,z250,z4,z5,z6]),(1,[z1,z64,z7,z3,z4,z6])],[(0,[z1,z7,z3,z4,z5,z251,z6]),(1,[z1,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z5,z252,z6]),(1,[z1,z7,z3,z4,z6,z253])],[(0,[z1,z7,z3,z4,z23,z254,z6]),(0,[z1,z7,z3,z4,z255,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z39]),(0,[z1,z256,z7,z3,z4,z5,z6])],[(0,[z66,z1,z90,z3,z4,z5,z6]),(0,[z1,z257,z7,z3,z4,z5,z6]),(0,[z1,z10,z7,z148,z4,z5,z6]),(0,[z1,z43,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z258,z4,z5,z6]),(0,[z1,z259,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z260]),(0,[z1,z7,z3,z4,z5,z261,z6])],[(0,[z1,z7,z3,z4,z5,z262,z6]),(0,[z1,z263,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z264])],[(0,[z1,z7,z3,z148,z4,z23,z6]),(0,[z155,z51,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z265,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z266]),(0,[z1,z7,z3,z267,z4,z5,z6]),(0,[z1,z26,z7,z3,z5,z191,z6]),(0,[z1,z7,z3,z4,z5,z268,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z67,z37]),(0,[z1,z7,z3,z4,z5,z269,z6])],[(0,[z1,z7,z3,z4,z5,z270,z6]),(0,[z1,z40,z7,z3,z4,z23,z6]),(0,[z155,z7,z3,z4,z9,z5,z6]),(0,[z1,z7,z3,z271,z4,z5,z6])],[(0,[z0,z1,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z5,z272,z6]),(0,[z1,z7,z3,z4,z5,z6,z273])],[(0,[z1,z7,z3,z274,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z275,z6])],[(1,[z1,z7,z3,z4,z276,z6]),(0,[z198,z1,z7,z148,z4,z5,z6]),(1,[z7,z3,z4,z9,z23,z6]),(1,[z1,z115,z3,z4,z119,z6]),(0,[z1,z85,z7,z3,z4,z5,z191]),(0,[z1,z7,z3,z4,z5,z6,z277])],[(0,[z1,z181,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z23,z116,z6]),(0,[z1,z85,z7,z3,z4,z5,z37]),(0,[z1,z7,z278,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z253,z39])],[(0,[z1,z7,z4,z279,z5,z23,z6]),(0,[z1,z7,z3,z4,z9,z6,z80]),(0,[z1,z7,z3,z280,z4,z5,z6]),(0,[z281,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z282,z6]),(0,[z283,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z284,z4,z23,z6]),(0,[z1,z7,z3,z4,z5,z285,z6]),(0,[z286,z1,z7,z3,z4,z5,z6]),(1,[z1,z158,z7,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z172,z4,z9,z6]),(0,[z1,z26,z7,z3,z4,z23,z6]),(0,[z1,z160,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z112,z5,z6]),(0,[z1,z115,z7,z250,z4,z5,z6]),(0,[z1,z7,z3,z4,z287,z5,z6]),(0,[z1,z40,z7,z3,z4,z192,z6]),(0,[z1,z85,z7,z3,z192,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z288]),(0,[z1,z143,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z23,z36,z6]),(0,[z1,z289,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z290,z6]),(0,[z1,z7,z291,z3,z4,z5,z6]),(0,[z1,z7,z3,z292,z4,z5,z6]),(0,[z1,z181,z7,z3,z4,z5,z39])],[(0,[z1,z293,z7,z3,z4,z5,z6]),(0,[z1,z294,z7,z3,z4,z5,z6])],[(0,[z1,z107,z7,z3,z4,z105,z6]),(0,[z1,z7,z3,z4,z5,z6,z295])],[(0,[z1,z7,z3,z4,z23,z29,z6]),(0,[z1,z124,z7,z3,z4,z23,z6]),(0,[z296,z1,z7,z3,z4,z5,z6])],[(0,[z0,z1,z7,z3,z4,z297,z6]),(0,[z1,z7,z3,z4,z5,z170,z6]),(0,[z1,z298,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z299,z6]),(0,[z300,z1,z7,z3,z4,z5,z6])],[(0,[z1,z301,z7,z3,z4,z5,z6]),(0,[z1,z302,z7,z3,z4,z5,z6]),(0,[z1,z303,z7,z3,z4,z5,z6]),(0,[z1,z40,z7,z3,z4,z98,z6]),(0,[z304,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z199,z6]),(0,[z1,z1,z7,z3,z4,z9,z6]),(1,[z1,z7,z3,z46,z5,z191])]],
   [[(0,[z1,z305,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z306]),(1,[z1,z122,z3,z72,z5,z6]),(0,[z1,z7,z3,z4,z5,z307,z6]),(0,[z1,z7,z3,z4,z5,z308,z6]),(0,[z1,z7,z3,z309,z4,z5,z6])],[(0,[z1,z183,z7,z3,z4,z5,z6]),(0,[z1,z310,z7,z3,z4,z23,z6]),(0,[z1,z122,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z38,z9,z6]),(0,[z1,z7,z3,z4,z5,z311,z6]),(0,[z1,z312,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z254,z6]),(0,[z50,z1,z7,z3,z4,z313,z6]),(0,[z51,z1,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z314,z5,z6]),(1,[z1,z7,z41,z4,z105,z6]),(0,[z1,z7,z3,z4,z5,z6,z253])],[(1,[z1,z7,z4,z279,z23,z6]),(0,[z1,z7,z3,z315,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z36,z29]),(0,[z1,z316,z7,z3,z4,z5,z6]),(0,[z1,z317,z7,z3,z4,z5,z6]),(0,[z1,z107,z40,z7,z3,z4,z6])],[(0,[z318,z1,z7,z3,z4,z5,z6]),(0,[z1,z107,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z159,z23,z6]),(0,[z1,z7,z3,z4,z5,z6,z319])],[(0,[z47,z1,z7,z3,z4,z5,z320]),(0,[z1,z7,z3,z4,z321,z5,z6]),(0,[z1,z27,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z322,z4,z5,z6]),(0,[z1,z248,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z323,z6])],[(0,[z1,z7,z3,z4,z8,z5,z6]),(1,[z76,z7,z3,z4,z5,z29]),(0,[z1,z324,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z46,z5,z191,z6])]],
   [[(0,[z1,z7,z3,z284,z22,z5,z6]),(0,[z1,z7,z3,z4,z9,z9,z6]),(0,[z76,z1,z7,z3,z4,z5,z29]),(1,[z1,z69,z3,z4,z5,z67]),(0,[z1,z16,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z192,z5,z98,z6]),(0,[z1,z85,z158,z7,z4,z5,z6]),(0,[z1,z7,z3,z4,z325,z5,z6])],[(0,[z1,z7,z3,z4,z48,z5,z6]),(0,[z1,z326,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z327,z23,z6]),(0,[z1,z7,z3,z4,z5,z328,z6]),(0,[z1,z7,z3,z4,z329,z5,z6])],[(0,[z1,z7,z3,z330,z4,z5,z6]),(0,[z1,z331,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z332,z6]),(0,[z1,z7,z3,z22,z38,z5,z6]),(0,[z1,z7,z3,z156,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z276,z6]),(0,[z76,z7,z3,z4,z5,z29,z6]),(0,[z1,z7,z3,z4,z5,z333,z6]),(0,[z1,z334,z7,z3,z4,z5,z6]),(1,[z1,z310,z7,z3,z4,z80]),(0,[z1,z335,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z336,z6]),(0,[z1,z7,z3,z4,z5,z337,z6]),(0,[z1,z338,z7,z3,z4,z5,z6]),(0,[z1,z85,z7,z3,z4,z5,z68]),(0,[z1,z339,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z340,z6])],[(1,[z1,z7,z3,z4,z5,z87]),(0,[z1,z341,z7,z3,z4,z5,z6]),(0,[z1,z107,z7,z3,z4,z119,z6]),(0,[z1,z7,z3,z4,z5,z157,z6])],[(0,[z0,z1,z7,z3,z4,z5,z6]),(0,[z1,z342,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z343]),(0,[z1,z7,z3,z4,z23,z6,z37]),(0,[z344,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z345,z6]),(0,[z1,z346,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z347,z6]),(0,[z1,z7,z3,z4,z348,z5,z6])],[(0,[z1,z349,z7,z3,z4,z5,z6]),(0,[z0,z1,z7,z3,z179,z5,z6]),(0,[z1,z350,z7,z3,z4,z9,z6]),(0,[z76,z1,z7,z3,z4,z321,z6]),(0,[z1,z351,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z352,z6]),(0,[z1,z353,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z36,z6]),(0,[z1,z181,z7,z3,z46,z4,z5]),(0,[z1,z7,z3,z4,z5,z98,z6])]],
   [[(0,[z1,z7,z3,z46,z4,z23,z6]),(0,[z354,z1,z7,z3,z4,z5,z6]),(0,[z355,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z356]),(0,[z1,z7,z3,z4,z357,z5,z6]),(0,[z1,z7,z3,z4,z358,z5,z6]),(0,[z1,z7,z3,z46,z4,z5,z89])],[(0,[z50,z1,z7,z3,z4,z23,z6]),(0,[z359,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z360,z6])],[(0,[z1,z7,z3,z361,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z29,z6]),(0,[z28,z1,z7,z3,z4,z5,z37]),(0,[z1,z7,z362,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z195])],[(1,[z1,z7,z3,z4,z5,z320]),(1,[z1,z7,z3,z4,z202,z6]),(0,[z0,z198,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z72,z4,z5,z6]),(0,[z1,z122,z3,z72,z4,z5,z6]),(1,[z1,z107,z7,z4,z157,z6]),(0,[z1,z7,z363,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z364,z5,z6]),(0,[z1,z7,z3,z172,z4,z5,z6]),(0,[z76,z1,z7,z3,z4,z5,z6]),(0,[z1,z160,z7,z3,z4,z5,z6]),(0,[z1,z69,z7,z3,z365,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z366])],[(0,[z1,z367,z7,z3,z4,z5,z6]),(0,[z1,z160,z7,z3,z72,z5,z6]),(0,[z1,z7,z3,z4,z5,z368,z6]),(0,[z369,z1,z7,z3,z4,z5,z6]),(0,[z370,z1,z7,z3,z4,z5,z6]),(0,[z1,z371,z7,z3,z4,z5,z6])],[(0,[z372,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z23,z373,z6]),(1,[z1,z111,z11,z4,z5,z6]),(0,[z1,z374,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z192,z9,z6]),(0,[z1,z7,z3,z4,z375,z38,z6]),(0,[z1,z376,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z6,z190]),(0,[z1,z7,z3,z4,z23,z191,z6]),(0,[z1,z7,z3,z377,z4,z5,z6])],[(0,[z28,z1,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z23,z6,z39]),(0,[z76,z1,z7,z3,z4,z242,z6]),(0,[z1,z378,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z379,z5,z6]),(1,[z1,z7,z3,z5,z6,z380])],[(0,[z47,z7,z90,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z381,z6]),(0,[z1,z382,z7,z3,z4,z5,z6]),(0,[z1,z7,z41,z3,z4,z9,z6]),(0,[z1,z111,z3,z11,z4,z5,z6]),(0,[z1,z383,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z384,z6])],[(0,[z1,z1,z7,z3,z4,z5,z6]),(1,[z106,z7,z3,z172,z5,z6]),(0,[z1,z27,z7,z3,z5,z191,z6]),(0,[z1,z385,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z386,z4,z5,z6]),(0,[z1,z310,z7,z3,z46,z4,z5])],[(0,[z47,z66,z7,z3,z4,z5,z6]),(0,[z47,z1,z7,z3,z4,z9,z6]),(0,[z1,z7,z90,z3,z4,z23,z6]),(0,[z1,z387,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z46,z4,z5,z67]),(0,[z1,z26,z7,z3,z284,z5,z6])],[(0,[z1,z7,z3,z182,z4,z5,z6]),(0,[z0,z1,z7,z152,z4,z5,z6]),(0,[z1,z122,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z388,z6]),(0,[z1,z7,z3,z4,z38,z5,z6]),(0,[z1,z7,z3,z4,z5,z389,z6])],[(0,[z1,z7,z3,z4,z5,z131,z6]),(0,[z1,z122,z7,z3,z72,z5,z6]),(0,[z1,z85,z181,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z5,z390,z6]),(0,[z1,z7,z41,z3,z4,z104,z6]),(0,[z1,z7,z3,z4,z5,z391,z6])]],
   [[(0,[z392,z1,z7,z3,z4,z5,z6])],[(0,[z1,z85,z7,z3,z172,z5,z6]),(1,[z1,z7,z3,z4,z375,z6]),(0,[z1,z7,z3,z4,z5,z6,z393])],[(0,[z1,z7,z3,z147,z4,z5,z6]),(0,[z50,z1,z7,z3,z22,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z394]),(0,[z1,z7,z3,z4,z5,z6,z395]),(0,[z1,z40,z7,z3,z108,z5,z6])],[(0,[z1,z7,z223,z3,z4,z5,z6]),(0,[z1,z396,z7,z3,z4,z5,z6]),(0,[z1,z397,z7,z3,z4,z5,z6]),(0,[z1,z7,z284,z4,z38,z5,z6]),(1,[z1,z27,z7,z284,z5,z6])],[(0,[z1,z7,z3,z4,z5,z189,z6]),(0,[z398,z1,z7,z3,z4,z5,z6]),(0,[z1,z399,z7,z3,z4,z5,z6]),(0,[z400,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z9,z5,z6]),(0,[z1,z71,z7,z3,z4,z23,z6]),(0,[z1,z401,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z9,z226,z6]),(0,[z1,z7,z3,z4,z9,z402,z6]),(0,[z1,z7,z3,z4,z5,z6,z37]),(0,[z1,z69,z7,z3,z4,z5,z68])],[(0,[z1,z7,z3,z4,z403,z5,z6]),(1,[z1,z7,z3,z4,z5,z21])],[(0,[z1,z404,z7,z3,z4,z5,z6]),(0,[z1,z405,z7,z3,z4,z5,z6]),(0,[z406,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z407]),(0,[z1,z7,z3,z4,z408,z5,z6]),(0,[z1,z7,z3,z409,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z410]),(0,[z1,z7,z3,z411,z4,z5,z6])]],
   [[(0,[z1,z111,z7,z3,z4,z5,z6])],[(0,[z412,z1,z7,z3,z4,z5,z6]),(0,[z198,z1,z7,z4,z105,z5,z6]),(0,[z413,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z414,z6]),(0,[z1,z7,z3,z4,z9,z6,z89]),(0,[z1,z7,z3,z72,z5,z191,z6]),(0,[z1,z7,z3,z4,z5,z6,z415]),(0,[z1,z7,z3,z4,z416,z5,z6]),(0,[z1,z7,z3,z4,z5,z209,z6]),(0,[z1,z40,z85,z7,z3,z5,z6])],[(1,[z1,z7,z3,z4,z9,z6]),(0,[z1,z417,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z418])],[(0,[z1,z7,z3,z4,z419,z5,z6]),(0,[z198,z7,z152,z3,z4,z5,z6]),(0,[z155,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z279,z5,z6]),(0,[z1,z350,z7,z3,z4,z5,z6]),(0,[z76,z1,z7,z3,z255,z5,z6]),(0,[z1,z7,z3,z4,z5,z420,z6]),(0,[z421,z1,z7,z3,z4,z5,z6]),(0,[z422,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z22,z9,z6]),(0,[z1,z7,z3,z423,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z373,z6]),(0,[z424,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z62]),(0,[z1,z7,z3,z425,z4,z5,z6]),(0,[z426,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z152,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z5,z177,z6]),(0,[z1,z7,z3,z4,z427,z5,z6]),(0,[z1,z428,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z365,z5,z6]),(0,[z1,z7,z3,z4,z5,z191,z6])],[(0,[z1,z429,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z23,z23,z6]),(1,[z1,z7,z3,z4,z114,z6]),(0,[z1,z85,z26,z7,z3,z5,z6]),(0,[z1,z7,z3,z430,z4,z5,z6])]],
   [[(0,[z1,z71,z7,z3,z4,z5,z67]),(0,[z1,z85,z7,z3,z46,z5,z6])],[(0,[z1,z7,z3,z431,z4,z5,z6]),(0,[z1,z7,z3,z4,z432,z5,z6]),(0,[z1,z433,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z250,z4,z5,z6]),(0,[z434,z1,z7,z3,z4,z5,z6])],[(0,[z1,z435,z7,z3,z4,z5,z6]),(0,[z1,z436,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z437,z5,z6])],[(1,[z1,z7,z223,z4,z5,z6]),(1,[z1,z26,z7,z38,z5,z6]),(0,[z1,z7,z3,z4,z438,z5,z6]),(0,[z1,z439,z7,z3,z4,z5,z6])],[(0,[z66,z1,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z440,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z441]),(0,[z1,z442,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z443])],[(1,[z1,z7,z3,z4,z297,z6]),(0,[z1,z444,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z445,z4,z5,z6])],[(0,[z66,z183,z7,z3,z4,z5,z6]),(0,[z1,z183,z3,z11,z4,z5,z6]),(0,[z446,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z11,z4,z9,z6]),(0,[z1,z7,z3,z447,z4,z5,z6]),(0,[z1,z7,z448,z3,z4,z5,z6]),(0,[z1,z449,z7,z3,z4,z5,z6])],[(0,[z1,z450,z7,z3,z4,z5,z6]),(0,[z1,z43,z10,z3,z4,z5,z6]),(1,[z1,z124,z3,z4,z116,z6]),(0,[z1,z7,z451,z3,z4,z5,z6])]],
   [[(0,[z47,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z5,z149]),(0,[z1,z7,z452,z3,z4,z5,z6]),(0,[z1,z107,z310,z7,z3,z4,z6]),(0,[z1,z7,z3,z4,z5,z6,z453]),(0,[z1,z85,z16,z7,z3,z4,z5]),(1,[z1,z97,z7,z3,z4,z5])],[(0,[z1,z7,z3,z4,z5,z37,z39]),(0,[z1,z7,z3,z4,z454,z5,z6])],[(1,[z0,z7,z148,z4,z5,z6]),(0,[z1,z455,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z23,z157,z6]),(0,[z1,z7,z3,z4,z5,z6,z456]),(0,[z1,z7,z3,z4,z457,z5,z6])],[(1,[z47,z90,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z458]),(0,[z106,z1,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z5,z459,z6]),(0,[z1,z85,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z460,z5,z6]),(0,[z1,z7,z461,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z462,z5,z6])],[(0,[z1,z463,z7,z3,z4,z5,z6]),(0,[z1,z115,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z23,z98,z6])],[(0,[z1,z90,z3,z11,z4,z5,z6]),(0,[z1,z7,z3,z4,z464,z23,z6]),(0,[z1,z7,z3,z4,z101,z9,z6]),(0,[z1,z465,z7,z3,z4,z9,z6]),(0,[z466,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z467,z3,z4,z5,z6]),(0,[z1,z7,z3,z468,z4,z5,z6])],[(0,[z469,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z119,z23,z6]),(0,[z1,z7,z3,z4,z5,z6,z470])]],
   [[(0,[z1,z310,z7,z3,z4,z9,z6]),(0,[z76,z28,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z108,z4,z5,z6])],[(0,[z47,z1,z7,z197,z4,z5,z6]),(0,[z51,z1,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z5,z471,z6]),(0,[z1,z472,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z225,z5,z6]),(0,[z473,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z474,z4,z5,z6]),(0,[z1,z475,z7,z3,z4,z5,z6]),(0,[z1,z476,z7,z3,z4,z5,z6]),(1,[z1,z85,z7,z3,z5,z89]),(0,[z1,z7,z477,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z159,z104])],[(1,[z1,z143,z7,z4,z23,z6]),(0,[z1,z107,z7,z3,z4,z9,z6]),(0,[z478,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z479,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z480])],[(0,[z481,z1,z7,z3,z4,z5,z6]),(0,[z482,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z23,z6]),(0,[z1,z7,z3,z4,z5,z483,z6]),(0,[z1,z124,z3,z4,z5,z116,z6]),(0,[z1,z115,z7,z3,z4,z119,z6])],[(0,[z484,z1,z7,z3,z4,z5,z6]),(0,[z485,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z22,z101,z5,z6]),(0,[z1,z7,z486,z3,z4,z5,z6]),(0,[z487,z1,z7,z3,z4,z5,z6])],[(0,[z66,z1,z7,z3,z4,z201,z6]),(1,[z1,z7,z3,z179,z5,z6]),(0,[z1,z7,z3,z4,z488,z5,z6]),(0,[z1,z7,z3,z4,z381,z5,z6])]],
   [[(0,[z1,z7,z3,z489,z4,z5,z6]),(0,[z1,z7,z3,z4,z22,z5,z6]),(1,[z1,z7,z3,z4,z5,z490]),(0,[z1,z491,z7,z3,z4,z5,z6]),(0,[z1,z492,z7,z3,z4,z5,z6]),(0,[z1,z124,z7,z3,z4,z119,z6]),(0,[z1,z107,z7,z3,z4,z104,z6]),(0,[z1,z7,z3,z4,z159,z104,z6])],[(0,[z1,z493,z7,z3,z4,z5,z6]),(0,[z494,z1,z7,z3,z4,z5,z6]),(0,[z1,z495,z7,z3,z5,z6,z80]),(0,[z1,z496,z7,z3,z4,z5,z6])],[(0,[z1,z497,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z498,z5,z6])],[(0,[z1,z499,z7,z3,z4,z5,z6]),(0,[z1,z85,z7,z3,z4,z5,z29]),(0,[z1,z7,z3,z4,z375,z5,z6]),(0,[z1,z7,z3,z46,z4,z5,z191])],[(0,[z106,z1,z7,z3,z22,z5,z6]),(0,[z1,z7,z3,z4,z9,z116,z6]),(0,[z1,z7,z3,z46,z4,z5,z37]),(0,[z1,z43,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z500])],[(0,[z1,z7,z3,z4,z52,z5,z6]),(0,[z1,z27,z7,z3,z38,z5,z6]),(0,[z1,z501,z7,z3,z4,z5,z6]),(0,[z1,z7,z502,z3,z4,z5,z6])],[(0,[z1,z7,z152,z11,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z503,z6]),(0,[z1,z504,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z505,z4,z5,z6])],[(1,[z1,z7,z197,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z506]),(0,[z0,z1,z7,z3,z147,z5,z6]),(0,[z1,z44,z7,z3,z4,z9,z6])]],
   [[(0,[z66,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z9,z36,z6]),(0,[z1,z507,z7,z3,z4,z5,z6]),(0,[z1,z160,z3,z4,z101,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z508])],[(0,[z165,z1,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z5,z509,z6])],[(0,[z1,z7,z3,z4,z5,z180,z6]),(0,[z1,z7,z3,z11,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z510,z6]),(0,[z1,z7,z3,z4,z511,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z320]),(0,[z1,z69,z7,z3,z4,z9,z6]),(1,[z28,z7,z3,z4,z5,z37])],[(0,[z0,z1,z7,z3,z4,z235,z6]),(0,[z1,z512,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z5,z191,z6,z89])],[(0,[z1,z7,z3,z4,z513,z5,z6]),(0,[z514,z1,z7,z3,z4,z5,z6]),(0,[z1,z310,z7,z3,z4,z5,z104])],[(0,[z1,z515,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z23,z516,z6])],[(0,[z1,z7,z3,z4,z5,z6,z517]),(0,[z518,z1,z7,z3,z4,z5,z6]),(0,[z1,z10,z7,z3,z4,z9,z6]),(0,[z76,z1,z7,z3,z156,z5,z6]),(0,[z1,z43,z111,z3,z4,z5,z6]),(0,[z1,z519,z7,z3,z4,z5,z6]),(0,[z1,z115,z3,z4,z119,z5,z6]),(0,[z1,z520,z7,z3,z4,z5,z6]),(0,[z521,z1,z7,z3,z4,z5,z6]),(0,[z1,z85,z7,z3,z4,z5,z6])]],
   [[(0,[z28,z1,z7,z3,z4,z9,z6]),(0,[z1,z85,z7,z3,z72,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z522]),(0,[z1,z7,z3,z4,z159,z5,z104])],[(0,[z1,z465,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z523,z4,z5,z6]),(0,[z1,z7,z3,z4,z101,z5,z6]),(0,[z1,z524,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z525,z5,z6])],[(0,[z1,z526,z7,z3,z4,z5,z6]),(1,[z198,z7,z152,z4,z5,z6]),(0,[z1,z7,z3,z4,z527,z5,z6])],[(0,[z1,z528,z7,z3,z4,z5,z6]),(0,[z1,z181,z16,z7,z4,z5,z6]),(0,[z1,z7,z3,z4,z529,z5,z6])],[(0,[z530,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z172,z38,z5,z6]),(0,[z1,z7,z3,z4,z5,z531,z6])],[(0,[z532,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z533,z6]),(0,[z534,z1,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z4,z82,z6]),(0,[z28,z1,z7,z3,z4,z114,z6]),(0,[z1,z535,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z536,z6]),(0,[z1,z7,z4,z5,z36,z6,z39])],[(0,[z7,z152,z3,z148,z4,z5,z6]),(0,[z198,z1,z7,z3,z4,z9,z6]),(0,[z1,z7,z41,z3,z4,z116,z6]),(0,[z1,z537,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z538]),(0,[z1,z7,z3,z4,z5,z539,z6]),(0,[z1,z7,z3,z4,z5,z540,z6])],[(0,[z1,z7,z3,z4,z541,z5,z6]),(0,[z1,z7,z3,z284,z172,z5,z6]),(1,[z155,z7,z3,z4,z9,z6]),(0,[z1,z542,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z543]),(0,[z1,z310,z7,z3,z4,z159,z6])]],
   [[(0,[z1,z7,z7,z3,z4,z5,z6]),(0,[z544,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z545]),(0,[z1,z546,z7,z3,z4,z5,z6])],[(0,[z0,z1,z207,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z297,z5,z6]),(0,[z547,z1,z7,z3,z4,z5,z6]),(0,[z1,z548,z7,z3,z4,z5,z6]),(0,[z1,z7,z549,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z550,z6]),(0,[z1,z551,z7,z3,z4,z5,z6])],[(0,[z552,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z553,z3,z4,z5,z6])],[(0,[z1,z183,z7,z3,z4,z23,z6]),(0,[z1,z7,z554,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z555,z5,z6]),(0,[z1,z7,z3,z4,z105,z9,z6]),(0,[z1,z7,z3,z4,z5,z556,z6]),(0,[z1,z7,z3,z46,z4,z5,z68])],[(0,[z1,z7,z557,z3,z4,z5,z6]),(0,[z558,z1,z7,z3,z4,z5,z6]),(0,[z559,z1,z7,z3,z4,z5,z6])],[(0,[z1,z560,z7,z3,z4,z5,z6]),(0,[z1,z140,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z9,z6,z37]),(0,[z1,z7,z3,z4,z5,z6,z380])],[(0,[z1,z7,z3,z4,z5,z561,z6]),(0,[z1,z562,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z108,z4,z192,z6]),(0,[z1,z7,z3,z4,z5,z563,z6])],[(0,[z106,z1,z7,z3,z4,z177,z6]),(0,[z1,z27,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z564,z4,z5,z6]),(0,[z1,z111,z7,z11,z4,z5,z6]),(0,[z1,z122,z7,z3,z4,z5,z167])]],
   [[(0,[z1,z7,z3,z4,z23,z6,z68]),(0,[z1,z565,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z566]),(0,[z1,z567,z7,z3,z4,z5,z6])],[(0,[z1,z7,z568,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z5,z6,z569]),(0,[z1,z495,z7,z3,z4,z5,z6])],[(0,[z106,z1,z7,z3,z4,z381,z6]),(0,[z1,z16,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z5,z570,z6]),(0,[z1,z571,z7,z3,z4,z5,z6]),(0,[z572,z1,z7,z3,z4,z5,z6]),(0,[z1,z85,z7,z3,z5,z6,z89])],[(0,[z1,z573,z7,z3,z4,z5,z6]),(0,[z574,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z575,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z516,z6]),(0,[z1,z7,z3,z4,z576,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z577]),(0,[z1,z7,z3,z108,z4,z98,z6])],[(0,[z165,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z152,z3,z4,z9,z6]),(0,[z1,z7,z578,z3,z4,z5,z6]),(0,[z1,z7,z3,z172,z5,z191,z6]),(0,[z1,z579,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z580,z6])],[(0,[z0,z1,z107,z7,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z581,z6]),(0,[z1,z7,z582,z3,z4,z5,z6]),(0,[z1,z16,z7,z3,z4,z5,z39])],[(0,[z198,z1,z7,z3,z4,z555,z6]),(0,[z1,z7,z3,z4,z5,z583,z6]),(0,[z1,z7,z3,z4,z9,z191,z6]),(0,[z76,z1,z7,z3,z4,z5,z37]),(0,[z1,z7,z3,z584,z4,z5,z6]),(0,[z1,z69,z7,z3,z4,z5,z6]),(0,[z1,z7,z585,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z9,z6,z39])],[(0,[z1,z7,z3,z148,z4,z9,z6]),(0,[z1,z349,z7,z3,z4,z23,z6]),(0,[z1,z586,z7,z3,z4,z5,z6]),(0,[z1,z310,z7,z3,z4,z6,z80])],[(0,[z1,z7,z587,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z588]),(1,[z1,z589,z7,z4,z5,z6]),(0,[z1,z589,z115,z7,z4,z5,z6]),(0,[z590,z1,z7,z3,z4,z5,z6])],[(0,[z591,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z23,z104,z6]),(0,[z1,z40,z7,z3,z4,z9,z6]),(0,[z1,z10,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z592])],[(0,[z1,z7,z3,z4,z5,z593,z6]),(0,[z1,z7,z3,z4,z5,z594,z6]),(0,[z595,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z11,z4,z105,z5,z6]),(0,[z1,z7,z3,z4,z596,z5,z6]),(0,[z1,z7,z3,z245,z4,z38,z5]),(0,[z1,z7,z3,z5,z6,z380,z80])],[(0,[z1,z43,z183,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z597]),(0,[z1,z7,z3,z72,z4,z23,z6]),(0,[z1,z7,z3,z598,z4,z5,z6]),(0,[z1,z589,z7,z3,z4,z5,z6]),(0,[z1,z181,z7,z3,z4,z5,z36]),(0,[z1,z85,z7,z3,z4,z159,z5])],[(0,[z1,z599,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z172,z4,z23,z6]),(0,[z76,z1,z7,z3,z4,z23,z6]),(0,[z1,z160,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z5,z6,z600]),(0,[z1,z7,z3,z4,z192,z5,z6])],[(0,[z50,z106,z7,z3,z4,z5,z6]),(0,[z1,z181,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z601,z5,z6]),(0,[z1,z43,z10,z7,z4,z5,z6]),(0,[z1,z602,z7,z3,z4,z5,z6]),(0,[z1,z603,z7,z3,z4,z5,z6])]],
   [[(0,[z604,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z149]),(0,[z1,z7,z3,z4,z5,z29,z39]),(0,[z1,z551,z7,z3,z5,z6,z39])],[(0,[z1,z7,z605,z3,z4,z5,z6]),(0,[z66,z1,z183,z3,z4,z5,z6]),(0,[z50,z1,z7,z3,z172,z5,z6]),(0,[z1,z7,z3,z284,z4,z9,z6]),(0,[z1,z606,z7,z3,z4,z5,z6]),(0,[z1,z7,z41,z3,z4,z5,z6]),(0,[z1,z97,z7,z3,z4,z5,z6])],[(0,[z198,z1,z7,z3,z4,z5,z6]),(0,[z1,z26,z7,z3,z4,z9,z6]),(0,[z1,z607,z7,z3,z4,z5,z6]),(0,[z1,z310,z7,z41,z3,z4,z6]),(0,[z1,z7,z3,z608,z4,z5,z6]),(0,[z609,z1,z7,z3,z4,z5,z6])],[(0,[z1,z115,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z5,z610,z6])],[(0,[z1,z382,z7,z3,z4,z23,z6])],[(0,[z1,z7,z3,z4,z313,z5,z6]),(0,[z1,z1,z7,z3,z4,z23,z6]),(1,[z1,z551,z7,z3,z5,z6]),(0,[z1,z611,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z612,z5,z6])],[(1,[z1,z7,z3,z4,z555,z6]),(0,[z1,z124,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z613,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z68]),(0,[z1,z7,z3,z614,z4,z5,z6])],[(0,[z1,z7,z148,z11,z4,z5,z6]),(0,[z1,z7,z3,z615,z4,z5,z6]),(0,[z1,z7,z3,z4,z23,z67,z6]),(0,[z1,z7,z3,z4,z38,z23,z6]),(0,[z1,z7,z3,z4,z616,z5,z6]),(0,[z1,z7,z3,z4,z617,z5,z6]),(0,[z1,z7,z3,z4,z105,z5,z6]),(0,[z1,z7,z3,z5,z209,z6,z39])]],
   [[(1,[z1,z7,z3,z4,z201,z6]),(0,[z0,z7,z3,z148,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z618,z6]),(0,[z1,z7,z3,z4,z5,z619,z6]),(0,[z1,z442,z7,z3,z4,z6,z39]),(0,[z1,z7,z3,z4,z5,z620,z6])],[(0,[z1,z621,z7,z3,z4,z5,z6]),(0,[z1,z43,z7,z3,z4,z112,z6])],[(0,[z1,z622,z7,z3,z4,z5,z6]),(0,[z1,z10,z7,z152,z4,z5,z6]),(0,[z1,z623,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z624,z6]),(0,[z1,z7,z625,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z626,z5,z6]),(0,[z1,z7,z3,z4,z627,z5,z6]),(0,[z1,z7,z3,z4,z628,z5,z6])],[(0,[z1,z7,z3,z629,z4,z5,z6]),(1,[z1,z7,z3,z4,z321,z6]),(0,[z1,z16,z7,z3,z46,z4,z5]),(0,[z630,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z568,z3,z4,z5,z6]),(0,[z631,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z632,z5,z6]),(0,[z1,z7,z3,z101,z5,z191,z6]),(0,[z1,z633,z7,z3,z4,z5,z6]),(0,[z634,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z635,z6]),(0,[z1,z7,z3,z4,z636,z5,z6]),(1,[z1,z7,z3,z108,z192,z6])],[(0,[z1,z7,z3,z72,z22,z5,z6]),(0,[z1,z7,z3,z4,z9,z23,z6]),(0,[z1,z401,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z9,z483,z6]),(0,[z1,z7,z3,z4,z159,z9,z6]),(0,[z1,z7,z3,z4,z5,z6,z6]),(0,[z637,z1,z7,z3,z4,z5,z6]),(1,[z1,z95,z7,z3,z4,z5])],[(0,[z1,z7,z3,z638,z4,z5,z6]),(0,[z51,z7,z3,z4,z5,z23,z6]),(0,[z1,z7,z3,z4,z23,z639,z6]),(0,[z7,z3,z4,z9,z5,z23,z6]),(0,[z1,z43,z7,z3,z4,z131,z6]),(0,[z1,z107,z7,z3,z4,z116,z6]),(0,[z1,z7,z3,z4,z640,z5,z6]),(0,[z1,z27,z7,z284,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z641,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z37,z68])],[(1,[z1,z7,z3,z4,z5,z6]),(0,[z198,z1,z7,z152,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z67,z29]),(0,[z1,z642,z7,z3,z4,z5,z6]),(0,[z1,z643,z7,z3,z4,z5,z6]),(1,[z1,z7,z3,z70,z5,z6]),(0,[z1,z644,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z104,z6])],[(0,[z1,z111,z7,z3,z4,z23,z6]),(0,[z645,z1,z7,z3,z4,z5,z6]),(0,[z1,z107,z10,z7,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z646,z6]),(0,[z1,z7,z3,z647,z4,z5,z6])],[(0,[z648,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z649,z6]),(0,[z1,z27,z7,z3,z284,z5,z6]),(0,[z1,z310,z7,z3,z4,z5,z80])],[(0,[z1,z7,z3,z650,z4,z5,z6]),(1,[z1,z7,z3,z4,z235,z6]),(0,[z1,z651,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z652,z6])],[(0,[z1,z7,z3,z148,z4,z5,z6]),(0,[z1,z7,z3,z4,z279,z23,z6]),(0,[z155,z1,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z5,z653,z6]),(0,[z1,z7,z3,z365,z4,z5,z6]),(0,[z1,z7,z3,z245,z4,z5,z6]),(0,[z1,z7,z3,z654,z4,z5,z6]),(1,[z1,z442,z7,z3,z4,z6])],[(0,[z1,z7,z3,z4,z5,z655,z6]),(1,[z1,z7,z3,z4,z242,z6]),(0,[z1,z7,z3,z4,z159,z5,z80])],[(0,[z1,z656,z7,z3,z4,z5,z6]),(0,[z1,z181,z7,z4,z5,z36,z6]),(0,[z1,z40,z7,z3,z4,z5,z6])]],
   [[(1,[z1,z7,z3,z4,z5,z167]),(0,[z1,z95,z7,z3,z4,z5,z6])],[(0,[z657,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z658,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z9,z157,z6]),(0,[z1,z7,z3,z4,z5,z6,z659]),(1,[z1,z7,z386,z4,z5,z6]),(0,[z660,z1,z7,z3,z4,z5,z6])],[(0,[z47,z1,z7,z3,z4,z419,z6]),(0,[z1,z7,z3,z46,z4,z9,z6]),(0,[z1,z7,z3,z4,z5,z661,z6])],[(0,[z50,z1,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z9,z98,z6]),(0,[z7,z3,z4,z5,z29,z6,z37]),(0,[z1,z181,z7,z3,z4,z5,z6])],[(0,[z1,z662,z7,z3,z4,z5,z6]),(0,[z1,z663,z7,z3,z4,z5,z6]),(0,[z1,z7,z41,z3,z108,z4,z6]),(0,[z1,z664,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z665,z6])],[(0,[z1,z7,z3,z4,z666,z5,z6]),(0,[z1,z667,z7,z3,z4,z5,z6]),(0,[z1,z668,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z67,z6]),(0,[z1,z7,z3,z284,z4,z5,z6]),(0,[z669,z1,z7,z3,z4,z5,z6])],[(1,[z66,z183,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z9,z29,z6]),(0,[z1,z26,z7,z3,z4,z5,z6])],[(0,[z198,z1,z107,z7,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z670]),(0,[z1,z7,z671,z3,z4,z5,z6]),(0,[z1,z143,z7,z3,z4,z5,z6]),(0,[z1,z115,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z672,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z673,z6]),(0,[z1,z7,z3,z4,z5,z195,z6])]],
   [[(0,[z1,z7,z3,z4,z674,z5,z6]),(0,[z106,z1,z7,z3,z4,z5,z490]),(0,[z1,z7,z3,z172,z101,z5,z6]),(0,[z1,z7,z3,z4,z464,z5,z6]),(0,[z1,z675,z7,z3,z4,z5,z6]),(0,[z1,z160,z7,z3,z101,z5,z6])],[(1,[z1,z7,z3,z4,z313,z6]),(0,[z1,z7,z3,z4,z676,z5,z6]),(0,[z1,z310,z85,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z677,z5,z6])],[(0,[z47,z1,z7,z3,z4,z23,z6]),(0,[z1,z7,z678,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z679,z5,z6]),(0,[z1,z124,z7,z3,z4,z5,z6]),(0,[z1,z124,z115,z3,z4,z5,z6]),(0,[z1,z680,z7,z3,z4,z5,z6])],[(0,[z1,z681,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z682,z6]),(0,[z1,z7,z3,z683,z4,z5,z6]),(0,[z1,z684,z7,z3,z4,z5,z6])],[(0,[z1,z107,z7,z4,z5,z157,z6])],[(0,[z1,z7,z3,z4,z5,z6,z685]),(0,[z1,z7,z3,z4,z5,z639,z6]),(0,[z1,z7,z3,z4,z5,z686,z6]),(0,[z1,z687,z7,z3,z4,z5,z6])],[(0,[z1,z7,z90,z3,z4,z9,z6]),(1,[z1,z143,z7,z4,z5,z6]),(0,[z1,z688,z7,z3,z4,z5,z6]),(0,[z689,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z690,z6])],[(0,[z1,z7,z3,z4,z23,z6,z80]),(0,[z1,z310,z7,z3,z4,z5,z6])]],
   [[(1,[z1,z7,z3,z4,z419,z6]),(0,[z0,z1,z7,z3,z4,z5,z190]),(0,[z51,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z5,z6]),(0,[z1,z7,z467,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z5,z402,z6]),(1,[z1,z7,z3,z255,z5,z6]),(0,[z1,z7,z4,z105,z5,z157,z6])],[(1,[z1,z7,z4,z279,z5,z6]),(0,[z1,z691,z7,z3,z4,z5,z6]),(0,[z1,z122,z7,z3,z4,z5,z87])],[(0,[z692,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z108,z4,z23,z6]),(0,[z1,z7,z3,z46,z4,z5,z29]),(0,[z693,z1,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z694,z5,z6]),(0,[z1,z107,z7,z3,z4,z5,z6]),(0,[z695,z1,z7,z3,z4,z5,z6]),(0,[z1,z85,z7,z386,z4,z5,z6]),(0,[z1,z7,z3,z4,z159,z5,z6])],[(0,[z47,z1,z7,z3,z4,z276,z6]),(0,[z106,z1,z7,z3,z172,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z696]),(1,[z1,z495,z7,z3,z5,z6])],[(0,[z47,z1,z183,z3,z4,z5,z6]),(0,[z1,z7,z3,z474,z4,z23,z6]),(0,[z1,z7,z3,z315,z4,z9,z6]),(0,[z1,z7,z3,z697,z4,z5,z6]),(0,[z1,z69,z3,z4,z5,z67,z6]),(0,[z1,z7,z3,z4,z5,z698,z6]),(0,[z1,z7,z3,z699,z4,z5,z6]),(0,[z700,z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z6,z701])],[(0,[z1,z43,z90,z3,z4,z5,z6]),(0,[z1,z702,z7,z3,z4,z5,z6]),(0,[z7,z3,z172,z4,z22,z5,z6]),(0,[z1,z71,z7,z3,z4,z9,z6]),(0,[z1,z27,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z703,z4,z5,z6]),(0,[z1,z704,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z490,z6]),(0,[z1,z7,z3,z4,z327,z5,z6]),(0,[z1,z7,z3,z4,z5,z6,z705]),(0,[z1,z7,z3,z706,z4,z5,z6]),(0,[z1,z181,z27,z7,z4,z5,z6]),(0,[z1,z16,z7,z3,z4,z5,z36])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z7,z3,z4,z707,z6]),(0,[z1,z560,z3,z101,z5,z6]),(0,[z1,z444,z7,z284,z5,z6])],[(0,[z1,z7,z708,z4,z5,z6]),(0,[z1,z7,z3,z4,z709,z6]),(0,[z1,z143,z7,z4,z9,z6]),(0,[z1,z136,z7,z3,z226,z6]),(0,[z1,z7,z3,z710,z5,z6]),(0,[z1,z7,z3,z4,z711,z6]),(0,[z1,z7,z3,z5,z712,z6])],[(0,[z1,z7,z197,z48,z5,z6]),(0,[z1,z7,z3,z713,z5,z6]),(0,[z1,z7,z3,z4,z177,z149]),(0,[z1,z310,z7,z3,z4,z62]),(0,[z1,z3,z4,z714,z5,z6]),(0,[z1,z85,z7,z3,z5,z577]),(0,[z1,z27,z7,z73,z5,z6]),(0,[z1,z85,z7,z386,z5,z89])],[(0,[z1,z7,z3,z4,z297,z190]),(1,[z7,z3,z713,z5,z6]),(0,[z1,z7,z3,z156,z321,z6]),(0,[z1,z122,z3,z714,z5,z6]),(0,[z715,z7,z3,z4,z5,z6]),(0,[z1,z716,z7,z386,z4,z6])],[(0,[z1,z7,z717,z4,z23,z6]),(0,[z1,z27,z7,z284,z23,z6]),(0,[z1,z7,z386,z4,z5,z29]),(0,[z718,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z182,z9,z6]),(0,[z1,z7,z3,z719,z5,z6]),(0,[z289,z7,z3,z4,z23,z6]),(0,[z637,z7,z3,z4,z5,z29]),(0,[z1,z208,z11,z4,z5,z6]),(0,[z1,z95,z7,z3,z4,z5]),(1,[z1,z7,z4,z5,z720])],[(0,[z1,z7,z3,z4,z9,z189]),(0,[z1,z7,z3,z147,z5,z6]),(0,[z1,z721,z3,z4,z9,z6]),(0,[z1,z722,z7,z4,z5,z6])],[(0,[z1,z7,z3,z4,z723,z6]),(0,[z1,z207,z3,z4,z297,z6]),(0,[z1,z7,z3,z4,z724,z6]),(0,[z1,z725,z7,z3,z4,z5]),(0,[z1,z401,z7,z3,z4,z75]),(0,[z1,z726,z7,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z727])]],
   [[(0,[z236,z183,z3,z4,z5,z6]),(0,[z0,z7,z148,z4,z5,z190]),(0,[z1,z7,z3,z156,z5,z6]),(0,[z1,z7,z3,z70,z5,z6])],[(0,[z1,z7,z3,z4,z728,z6]),(0,[z1,z7,z3,z147,z235,z6]),(0,[z1,z7,z3,z4,z729,z6]),(0,[z7,z3,z4,z5,z730,z6]),(0,[z1,z7,z3,z731,z4,z5]),(0,[z1,z7,z3,z4,z732,z6]),(0,[z1,z7,z3,z733,z4,z5]),(0,[z1,z7,z4,z5,z36,z720]),(0,[z1,z85,z7,z3,z5,z592])],[(0,[z1,z7,z250,z4,z9,z6]),(0,[z1,z7,z3,z734,z5,z6]),(0,[z1,z7,z3,z4,z735,z6])],[(0,[z1,z7,z3,z4,z235,z6]),(0,[z1,z2,z3,z4,z297,z6]),(0,[z1,z7,z3,z4,z736,z6]),(0,[z1,z7,z3,z4,z5,z737])],[(0,[z66,z183,z3,z4,z201,z6]),(1,[z7,z3,z4,z736,z6]),(0,[z1,z7,z3,z4,z6,z738])],[(0,[z1,z7,z3,z4,z242,z6]),(0,[z7,z3,z4,z617,z9,z6]),(0,[z1,z7,z3,z4,z5,z720])],[(0,[z1,z7,z223,z182,z5,z6]),(0,[z1,z7,z3,z739,z5,z6]),(0,[z1,z2,z4,z105,z5,z6]),(0,[z1,z26,z7,z245,z38,z5])],[(0,[z1,z7,z4,z23,z6,z740]),(0,[z1,z7,z3,z4,z5,z167])]],
   [[(0,[z0,z2,z148,z4,z5,z6]),(0,[z1,z589,z7,z4,z23,z6]),(0,[z1,z7,z386,z4,z5,z6]),(0,[z1,z181,z7,z386,z4,z5]),(0,[z1,z7,z3,z741,z5,z6])],[(0,[z7,z3,z4,z628,z9,z6]),(0,[z1,z742,z7,z4,z5,z6]),(0,[z1,z95,z7,z3,z4,z375])],[(0,[z0,z7,z148,z4,z5,z21]),(0,[z1,z7,z3,z4,z743,z6]),(0,[z1,z744,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z177,z490]),(0,[z1,z745,z7,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z746]),(0,[z1,z622,z10,z4,z5,z6]),(0,[z1,z7,z3,z4,z747,z6]),(0,[z1,z85,z7,z3,z5,z456]),(0,[z1,z371,z3,z72,z5,z6])],[(0,[z1,z26,z7,z38,z23,z6]),(0,[z7,z3,z4,z9,z736,z6]),(0,[z1,z310,z7,z3,z380,z80])],[(0,[z1,z7,z3,z179,z5,z190]),(0,[z1,z548,z7,z38,z5,z6]),(0,[z1,z7,z3,z4,z381,z490]),(0,[z121,z7,z3,z4,z9,z6])],[(0,[z47,z90,z3,z182,z5,z6]),(0,[z1,z7,z3,z4,z748,z6]),(0,[z106,z7,z3,z172,z5,z490]),(0,[z1,z7,z3,z4,z5,z749])],[(0,[z1,z158,z7,z4,z9,z6]),(0,[z1,z7,z3,z4,z750,z6])]],
   [[(0,[z1,z207,z3,z4,z5,z6]),(0,[z1,z7,z3,z751,z5,z6]),(0,[z1,z7,z3,z4,z313,z6]),(0,[z7,z3,z4,z23,z471,z6]),(0,[z1,z3,z4,z119,z752,z6]),(0,[z1,z7,z3,z4,z6,z753]),(0,[z1,z7,z3,z754,z5,z6])],[(0,[z1,z207,z3,z179,z5,z6]),(0,[z1,z7,z3,z4,z23,z149]),(0,[z1,z289,z11,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z755]),(0,[z1,z7,z3,z756,z5,z6]),(0,[z1,z7,z3,z4,z5,z757])],[(0,[z1,z7,z3,z4,z5,z758]),(0,[z7,z3,z4,z736,z23,z6]),(0,[z1,z7,z759,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z760]),(0,[z1,z26,z95,z7,z3,z5])],[(0,[z1,z7,z3,z4,z761,z6]),(0,[z1,z762,z7,z4,z5,z6]),(0,[z1,z551,z7,z3,z23,z6]),(0,[z1,z551,z7,z3,z6,z253]),(0,[z1,z85,z7,z3,z5,z763]),(0,[z1,z7,z3,z4,z764,z80])],[(0,[z1,z7,z3,z4,z5,z765]),(0,[z1,z7,z3,z4,z5,z766])],[(0,[z1,z7,z3,z4,z5,z767]),(0,[z1,z143,z7,z4,z5,z6]),(0,[z7,z768,z148,z4,z5,z6]),(0,[z1,z7,z3,z4,z769,z6])],[(0,[z7,z3,z713,z22,z5,z6]),(0,[z1,z3,z4,z5,z752,z6])],[(0,[z1,z7,z3,z4,z419,z6]),(0,[z1,z7,z3,z46,z9,z191])]],
   [[(0,[z1,z143,z7,z4,z235,z6]),(0,[z1,z7,z3,z4,z770,z6])],[(0,[z47,z90,z223,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z771]),(0,[z1,z124,z3,z4,z752,z6]),(0,[z1,z26,z7,z386,z5,z6])],[(0,[z421,z7,z3,z172,z5,z6]),(0,[z374,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z170,z6]),(0,[z7,z3,z4,z772,z5,z6]),(0,[z1,z7,z3,z4,z5,z773]),(0,[z1,z85,z7,z3,z462,z5])],[(0,[z1,z7,z3,z4,z5,z774]),(0,[z1,z7,z3,z4,z775,z6]),(0,[z1,z7,z4,z23,z6,z776]),(0,[z521,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z6,z777]),(0,[z1,z7,z3,z4,z778,z6]),(0,[z1,z779,z7,z3,z4,z5])],[(0,[z1,z7,z3,z780,z5,z6]),(0,[z1,z7,z3,z4,z781,z6]),(0,[z1,z7,z3,z4,z199,z6]),(0,[z1,z7,z3,z255,z242,z6]),(0,[z1,z7,z3,z782,z5,z6]),(0,[z1,z7,z41,z4,z56,z6])],[(0,[z1,z143,z7,z474,z4,z6]),(0,[z1,z7,z3,z4,z783,z6])],[(0,[z1,z7,z250,z4,z5,z6]),(0,[z1,z64,z7,z3,z4,z6])],[(0,[z1,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z23,z6,z784]),(0,[z76,z7,z3,z4,z9,z29]),(0,[z1,z785,z11,z4,z5,z6]),(0,[z1,z7,z3,z4,z6,z253])]],
   [[(0,[z1,z90,z197,z4,z5,z6]),(0,[z1,z7,z3,z4,z786,z6]),(0,[z1,z7,z3,z179,z23,z6]),(0,[z1,z107,z7,z4,z235,z6]),(0,[z1,z69,z3,z4,z9,z67]),(0,[z1,z7,z3,z4,z9,z787]),(0,[z30,z7,z3,z4,z5,z29]),(0,[z1,z7,z3,z4,z788,z6]),(0,[z1,z7,z3,z4,z789,z6]),(0,[z7,z3,z4,z5,z6,z790])],[(0,[z1,z791,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z792]),(0,[z793,z7,z3,z4,z5,z6]),(0,[z1,z794,z7,z4,z5,z6])],[(0,[z1,z7,z197,z182,z5,z6]),(0,[z1,z7,z3,z4,z795,z6]),(0,[z1,z16,z7,z386,z4,z5])],[(0,[z1,z7,z197,z4,z5,z189]),(0,[z106,z7,z3,z172,z381,z6]),(0,[z1,z7,z3,z4,z6,z796])],[(0,[z355,z7,z3,z4,z5,z37])],[(0,[z1,z7,z3,z4,z9,z87]),(0,[z1,z7,z3,z46,z5,z328])],[(0,[z1,z7,z3,z4,z797,z6]),(0,[z1,z551,z16,z7,z3,z5])],[(0,[z1,z3,z4,z5,z6,z798]),(0,[z634,z7,z3,z4,z9,z6]),(0,[z28,z7,z3,z4,z170,z37]),(0,[z1,z7,z3,z4,z799,z6])]],
   [[(0,[z1,z7,z3,z4,z276,z6]),(0,[z1,z7,z197,z4,z23,z6]),(0,[z1,z7,z3,z4,z5,z800]),(0,[z1,z801,z3,z4,z5,z6]),(0,[z7,z3,z4,z9,z23,z6]),(0,[z1,z7,z3,z108,z802,z6])],[(0,[z1,z7,z3,z4,z803,z6]),(0,[z1,z7,z3,z4,z104,z500])],[(0,[z558,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z9,z195])],[(0,[z1,z7,z804,z4,z5,z6]),(0,[z805,z90,z3,z4,z5,z6]),(0,[z1,z7,z4,z806,z201,z6]),(0,[z50,z7,z3,z713,z5,z6]),(0,[z1,z7,z3,z4,z807,z6]),(0,[z1,z3,z4,z9,z808,z6]),(0,[z809,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z810]),(0,[z66,z183,z3,z4,z23,z6]),(0,[z424,z7,z3,z22,z5,z6]),(0,[z28,z7,z3,z4,z23,z37]),(0,[z1,z7,z3,z4,z811,z6]),(0,[z812,z7,z3,z4,z5,z6])],[(0,[z813,z7,z3,z4,z5,z6]),(0,[z814,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z815,z6]),(0,[z1,z7,z3,z4,z5,z816]),(0,[z1,z7,z4,z817,z23,z6]),(0,[z1,z111,z11,z4,z9,z6]),(0,[z7,z3,z4,z13,z9,z6]),(0,[z1,z442,z16,z7,z4,z39])],[(0,[z1,z818,z3,z4,z5,z6]),(0,[z1,z819,z7,z3,z4,z6]),(0,[z1,z349,z3,z4,z327,z6]),(0,[z1,z85,z7,z3,z5,z538]),(0,[z1,z820,z7,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z821,z5,z6]),(0,[z1,z143,z7,z108,z4,z6]),(0,[z1,z465,z7,z4,z483,z6]),(0,[z1,z3,z4,z5,z822,z68]),(0,[z1,z823,z7,z3,z5,z6])],[(0,[z1,z7,z197,z4,z276,z6]),(0,[z1,z824,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z825,z6]),(0,[z1,z7,z4,z5,z6,z776]),(0,[z1,z181,z7,z4,z9,z36])],[(0,[z1,z7,z3,z826,z5,z6]),(0,[z1,z7,z3,z827,z5,z6]),(0,[z1,z7,z3,z4,z5,z828]),(0,[z1,z7,z3,z829,z5,z6]),(0,[z1,z830,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z831,z6]),(0,[z1,z7,z4,z105,z832,z6])],[(0,[z1,z7,z833,z4,z5,z6]),(0,[z106,z7,z3,z172,z9,z6]),(0,[z1,z834,z7,z3,z5,z6]),(0,[z1,z835,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z5,z836]),(0,[z1,z7,z3,z46,z5,z191])],[(0,[z1,z7,z3,z48,z5,z6]),(0,[z1,z7,z223,z4,z5,z320]),(0,[z1,z7,z4,z806,z5,z6]),(0,[z1,z7,z4,z279,z199,z6]),(0,[z1,z143,z7,z4,z254,z6]),(0,[z1,z7,z3,z4,z23,z837]),(0,[z1,z7,z3,z474,z52,z6]),(0,[z1,z122,z3,z72,z5,z6]),(0,[z1,z69,z3,z4,z5,z822])],[(0,[z1,z7,z3,z4,z5,z838]),(0,[z50,z7,z3,z22,z82,z6]),(0,[z1,z7,z3,z5,z6,z784]),(0,[z1,z160,z3,z101,z9,z6]),(0,[z1,z85,z7,z3,z5,z705]),(0,[z1,z7,z3,z4,z112,z6]),(0,[z1,z7,z3,z839,z5,z6]),(0,[z1,z551,z27,z7,z5,z6]),(0,[z1,z551,z7,z386,z5,z6])],[(0,[z1,z7,z3,z4,z840,z6]),(0,[z0,z546,z7,z4,z5,z6]),(0,[z1,z7,z3,z255,z23,z6]),(0,[z7,z3,z4,z60,z9,z6]),(0,[z76,z7,z3,z4,z321,z29]),(0,[z1,z310,z7,z3,z4,z569]),(0,[z1,z7,z3,z192,z802,z6])],[(0,[z1,z7,z3,z841,z5,z6]),(0,[z1,z7,z3,z4,z5,z842]),(0,[z1,z843,z7,z3,z5,z6]),(0,[z1,z7,z4,z279,z23,z6]),(0,[z1,z7,z3,z4,z844,z6])]],
   [[(0,[z1,z845,z3,z4,z5,z6]),(0,[z155,z7,z3,z4,z736,z6]),(0,[z1,z7,z3,z4,z846,z6])],[(0,[z1,z107,z7,z4,z199,z6]),(0,[z1,z95,z7,z3,z172,z5]),(0,[z1,z495,z7,z3,z23,z6]),(0,[z1,z7,z3,z4,z847,z6])],[(0,[z1,z7,z3,z4,z5,z848]),(0,[z1,z7,z3,z4,z849,z6]),(0,[z1,z7,z3,z5,z6,z850])],[(0,[z1,z2,z3,z4,z9,z6]),(0,[z1,z851,z3,z4,z5,z6]),(0,[z51,z143,z7,z4,z23,z6]),(0,[z1,z97,z7,z3,z4,z23]),(0,[z1,z27,z7,z284,z9,z6]),(0,[z79,z7,z3,z4,z9,z6]),(0,[z76,z7,z3,z4,z5,z29]),(0,[z1,z7,z3,z4,z131,z6])],[(0,[z1,z7,z3,z4,z5,z852]),(0,[z1,z7,z3,z853,z5,z6]),(0,[z47,z90,z3,z4,z5,z320]),(0,[z478,z7,z3,z4,z23,z6]),(0,[z1,z107,z7,z4,z483,z6]),(0,[z1,z7,z3,z4,z5,z787]),(0,[z1,z69,z3,z4,z5,z67]),(0,[z1,z7,z3,z4,z854,z6])],[(0,[z1,z7,z3,z4,z9,z21]),(0,[z1,z855,z7,z3,z4,z6]),(0,[z1,z143,z7,z4,z116,z6]),(0,[z1,z7,z3,z856,z5,z6]),(1,[z1,z3,z714,z5,z6]),(0,[z1,z7,z3,z4,z857,z6]),(0,[z1,z7,z3,z4,z858,z6]),(0,[z859,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z860]),(0,[z1,z7,z3,z4,z861,z6]),(0,[z7,z3,z768,z4,z5,z6]),(0,[z1,z862,z7,z3,z5,z6]),(0,[z51,z7,z4,z279,z23,z6]),(0,[z1,z7,z3,z23,z209,z6]),(0,[z1,z7,z3,z4,z863,z6]),(0,[z1,z7,z3,z4,z6,z864])],[(0,[z1,z181,z551,z7,z3,z5])]],
   [[(0,[z1,z7,z3,z4,z381,z149]),(0,[z1,z7,z3,z4,z865,z6])],[(0,[z1,z7,z866,z4,z5,z6]),(0,[z1,z7,z3,z4,z867,z6]),(0,[z106,z7,z3,z172,z5,z149]),(0,[z1,z7,z3,z4,z5,z87])],[(0,[z1,z7,z868,z4,z5,z6]),(0,[z1,z7,z3,z4,z869,z6]),(0,[z1,z43,z10,z4,z9,z6]),(0,[z1,z7,z3,z245,z4,z9]),(0,[z1,z7,z3,z4,z870,z6]),(0,[z1,z7,z3,z714,z5,z6]),(0,[z1,z7,z3,z72,z5,z87]),(0,[z1,z871,z3,z4,z5,z6]),(0,[z1,z7,z872,z4,z5,z6])],[(0,[z1,z873,z7,z4,z201,z6]),(0,[z1,z7,z3,z4,z5,z874]),(0,[z1,z7,z3,z4,z875,z6]),(0,[z1,z876,z7,z4,z23,z6]),(0,[z1,z877,z7,z3,z5,z6]),(0,[z1,z7,z3,z5,z6,z878]),(0,[z1,z85,z7,z3,z454,z5])],[(0,[z1,z7,z3,z4,z5,z879]),(0,[z1,z880,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z881,z6]),(0,[z1,z7,z882,z4,z5,z6]),(0,[z50,z7,z3,z22,z9,z6]),(0,[z1,z7,z467,z4,z279,z6]),(0,[z1,z7,z3,z4,z5,z883])],[(0,[z1,z7,z768,z4,z5,z6]),(0,[z1,z7,z3,z172,z5,z490]),(0,[z1,z95,z7,z3,z4,z23]),(0,[z1,z884,z7,z4,z23,z6]),(0,[z1,z7,z3,z4,z885,z6]),(0,[z1,z7,z3,z365,z9,z6]),(0,[z7,z3,z4,z5,z29,z730]),(0,[z1,z7,z886,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z195])],[(0,[z1,z7,z3,z4,z202,z6]),(0,[z1,z7,z3,z108,z52,z6]),(0,[z1,z7,z3,z4,z887,z6]),(0,[z1,z888,z7,z3,z4,z5]),(0,[z1,z107,z7,z4,z157,z6])]],
   [[(0,[z1,z7,z3,z4,z297,z21]),(0,[z1,z7,z3,z4,z464,z373]),(0,[z1,z7,z3,z156,z242,z6]),(0,[z1,z99,z3,z101,z5,z6]),(0,[z1,z7,z3,z4,z889,z6]),(0,[z1,z40,z7,z3,z98,z6])],[(0,[z1,z7,z890,z4,z5,z6]),(0,[z1,z7,z3,z891,z5,z6]),(0,[z1,z7,z3,z892,z5,z6]),(0,[z1,z382,z7,z3,z639,z6])],[(0,[z1,z7,z3,z893,z5,z6]),(0,[z1,z7,z3,z440,z5,z191]),(0,[z1,z7,z3,z4,z8,z402]),(0,[z1,z64,z26,z7,z38,z6]),(0,[z1,z95,z7,z4,z5,z39])],[(0,[z1,z7,z223,z4,z9,z6]),(0,[z1,z7,z3,z48,z419,z6]),(0,[z1,z7,z3,z894,z5,z6]),(0,[z198,z7,z768,z4,z5,z6]),(0,[z1,z7,z3,z4,z177,z6]),(0,[z1,z26,z7,z38,z9,z6]),(1,[z1,z3,z4,z752,z6]),(0,[z1,z107,z7,z4,z360,z6])],[(0,[z1,z873,z7,z4,z5,z6]),(0,[z1,z7,z3,z895,z5,z6])],[(0,[z1,z16,z7,z4,z23,z39]),(0,[z1,z896,z7,z3,z5,z6]),(0,[z1,z7,z3,z4,z897,z6]),(0,[z1,z181,z7,z4,z5,z36]),(0,[z1,z7,z3,z5,z6,z380])],[(0,[z1,z7,z3,z4,z381,z6]),(0,[z1,z898,z3,z4,z5,z6]),(0,[z1,z143,z382,z7,z4,z6]),(0,[z1,z7,z3,z4,z5,z899]),(0,[z1,z900,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z5,z190]),(0,[z106,z7,z3,z172,z5,z6]),(0,[z1,z835,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z159,z402]),(0,[z1,z7,z3,z4,z5,z730]),(0,[z1,z551,z7,z3,z5,z37]),(0,[z1,z901,z7,z3,z4,z6]),(0,[z1,z902,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z197,z4,z5,z320]),(0,[z1,z7,z903,z4,z5,z6]),(0,[z1,z904,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z9,z149]),(0,[z1,z143,z40,z7,z4,z6]),(1,[z7,z3,z4,z5,z730]),(0,[z1,z7,z3,z4,z159,z665])],[(0,[z1,z207,z3,z147,z5,z6]),(0,[z1,z905,z3,z4,z5,z6]),(0,[z1,z7,z3,z23,z906,z6]),(0,[z1,z433,z3,z4,z5,z67]),(0,[z1,z160,z3,z101,z5,z6])],[(0,[z1,z7,z3,z4,z235,z190]),(0,[z0,z7,z148,z4,z9,z6]),(0,[z76,z7,z3,z255,z5,z29]),(0,[z1,z160,z3,z714,z5,z6]),(0,[z1,z7,z3,z4,z907,z6])],[(0,[z47,z90,z3,z4,z9,z6]),(0,[z908,z7,z3,z4,z5,z6]),(0,[z1,z909,z7,z3,z4,z6]),(0,[z1,z7,z4,z5,z832,z6])],[(0,[z1,z7,z3,z4,z5,z910]),(0,[z66,z183,z3,z4,z202,z6]),(0,[z478,z7,z148,z4,z5,z6]),(0,[z1,z589,z7,z4,z119,z6]),(0,[z1,z7,z3,z4,z911,z6]),(0,[z1,z7,z3,z5,z209,z6]),(0,[z1,z40,z7,z3,z539,z6])],[(0,[z1,z71,z3,z4,z5,z822]),(0,[z1,z7,z3,z4,z375,z6])],[(0,[z1,z207,z3,z4,z235,z6]),(0,[z1,z350,z3,z4,z92,z6]),(0,[z1,z7,z4,z5,z720,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z912,z6]),(0,[z1,z27,z7,z284,z5,z6])]],
   [[(0,[z1,z2,z3,z179,z5,z6]),(0,[z434,z7,z3,z4,z9,z6]),(0,[z1,z3,z4,z5,z67,z822]),(0,[z1,z913,z7,z3,z5,z6]),(0,[z1,z7,z3,z5,z191,z141])],[(0,[z1,z7,z3,z4,z5,z21]),(0,[z1,z914,z7,z4,z5,z6])],[(0,[z1,z7,z3,z915,z5,z6]),(0,[z1,z2,z3,z4,z235,z6]),(0,[z1,z7,z3,z179,z5,z21]),(0,[z1,z916,z7,z3,z4,z6]),(0,[z1,z85,z7,z3,z9,z89]),(0,[z1,z7,z3,z4,z5,z917]),(0,[z1,z7,z3,z365,z5,z68]),(0,[z1,z918,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z919,z6]),(0,[z1,z785,z111,z4,z5,z6])],[(0,[z1,z7,z3,z182,z5,z6]),(0,[z1,z7,z3,z48,z276,z6]),(0,[z1,z7,z3,z4,z920,z6]),(0,[z1,z7,z3,z4,z5,z921]),(0,[z7,z3,z4,z5,z730,z37]),(0,[z1,z7,z3,z922,z5,z6]),(0,[z1,z7,z3,z4,z923,z6])],[(0,[z1,z7,z3,z4,z5,z189]),(0,[z0,z7,z148,z4,z297,z6]),(0,[z1,z721,z3,z4,z5,z6]),(0,[z1,z7,z924,z4,z5,z6]),(0,[z1,z7,z3,z4,z925,z6])],[(0,[z1,z43,z10,z4,z5,z6]),(0,[z1,z85,z158,z7,z5,z89])],[(0,[z1,z3,z4,z926,z5,z6]),(0,[z1,z7,z3,z4,z927,z6]),(0,[z1,z7,z3,z4,z928,z6]),(0,[z1,z7,z3,z4,z929,z6])]],
   [[(0,[z1,z7,z3,z147,z23,z6]),(0,[z1,z7,z3,z4,z9,z490]),(1,[z1,z785,z4,z5,z6]),(0,[z1,z10,z7,z4,z112,z6]),(0,[z1,z7,z3,z245,z4,z5]),(0,[z1,z7,z3,z5,z802,z6]),(0,[z1,z7,z930,z3,z4,z6])],[(0,[z1,z931,z7,z3,z4,z6]),(0,[z50,z7,z3,z22,z5,z6]),(0,[z1,z932,z3,z4,z5,z6]),(0,[z1,z726,z7,z4,z23,z6]),(0,[z1,z26,z7,z375,z38,z6])],[(0,[z1,z7,z3,z70,z23,z6]),(0,[z1,z115,z3,z4,z327,z6]),(0,[z1,z7,z3,z365,z5,z6]),(0,[z1,z933,z3,z4,z5,z6]),(0,[z1,z310,z7,z3,z4,z539])],[(0,[z1,z7,z3,z4,z934,z6]),(0,[z1,z7,z386,z4,z5,z37])],[(0,[z1,z7,z3,z4,z935,z6]),(0,[z1,z241,z3,z72,z5,z6]),(0,[z1,z143,z401,z7,z4,z6]),(0,[z1,z7,z3,z936,z5,z6]),(0,[z1,z40,z97,z7,z3,z5])],[(0,[z1,z7,z3,z4,z937,z6]),(0,[z1,z7,z3,z4,z938,z6]),(0,[z1,z3,z4,z752,z116,z6]),(0,[z1,z939,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z940,z6])],[(0,[z1,z7,z3,z941,z5,z6]),(0,[z1,z2,z152,z4,z5,z6]),(0,[z1,z7,z3,z942,z5,z6]),(0,[z1,z943,z7,z3,z4,z6]),(0,[z1,z27,z7,z5,z6,z410])],[(0,[z1,z7,z223,z4,z5,z6]),(0,[z1,z7,z197,z4,z9,z6]),(0,[z1,z7,z3,z5,z906,z6]),(0,[z66,z805,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z944]),(0,[z1,z26,z7,z38,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z945,z6]),(0,[z1,z85,z7,z3,z5,z670]),(0,[z1,z3,z4,z5,z946,z6]),(0,[z1,z7,z3,z947,z5,z6]),(0,[z1,z7,z948,z4,z5,z6]),(0,[z1,z7,z3,z4,z949,z6])],[(0,[z183,z805,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z23,z167]),(0,[z1,z7,z3,z950,z5,z6])],[(0,[z1,z7,z3,z179,z297,z6]),(0,[z1,z7,z3,z4,z951,z6]),(0,[z1,z7,z386,z4,z23,z6]),(0,[z1,z7,z3,z952,z4,z5])],[(0,[z637,z7,z3,z4,z23,z6]),(0,[z28,z7,z3,z4,z9,z37]),(0,[z1,z124,z3,z4,z116,z6]),(0,[z1,z115,z3,z4,z119,z6]),(0,[z1,z64,z7,z3,z245,z4]),(0,[z1,z181,z7,z4,z677,z5])],[(0,[z1,z7,z3,z4,z5,z953]),(0,[z1,z7,z3,z245,z4,z375])],[(0,[z1,z7,z3,z315,z110,z6]),(0,[z1,z7,z3,z5,z6,z763])],[(0,[z1,z7,z3,z4,z9,z320]),(0,[z0,z7,z148,z4,z5,z6]),(0,[z1,z143,z7,z4,z105,z6]),(0,[z406,z7,z3,z4,z23,z6]),(0,[z1,z158,z7,z4,z5,z6]),(0,[z1,z40,z7,z3,z802,z6])],[(0,[z47,z90,z3,z4,z5,z6]),(0,[z1,z954,z7,z4,z5,z6]),(0,[z0,z7,z148,z179,z5,z6]),(0,[z1,z7,z4,z105,z235,z6]),(0,[z246,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z4,z5,z955])]],
   [[(0,[z28,z7,z3,z4,z114,z37])],[(0,[z0,z7,z148,z4,z235,z6]),(0,[z1,z956,z7,z3,z5,z6]),(0,[z50,z7,z3,z22,z313,z6]),(0,[z417,z7,z3,z4,z23,z6]),(0,[z1,z7,z41,z4,z6,z443])],[(0,[z1,z7,z3,z957,z5,z6]),(0,[z1,z207,z3,z4,z23,z6]),(0,[z958,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z182,z419,z6]),(0,[z959,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z960,z5,z6])],[(0,[z1,z7,z3,z4,z419,z189]),(0,[z1,z342,z11,z4,z5,z6])],[(0,[z1,z961,z7,z3,z4,z6]),(0,[z1,z762,z7,z4,z23,z6])],[(0,[z1,z7,z3,z4,z962,z6]),(0,[z1,z7,z3,z4,z963,z6]),(0,[z1,z7,z3,z4,z964,z6]),(0,[z965,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z706,z5,z191]),(0,[z1,z966,z3,z4,z5,z6]),(0,[z1,z85,z7,z3,z5,z89])],[(0,[z478,z90,z3,z4,z5,z6]),(0,[z1,z143,z7,z4,z23,z6]),(0,[z1,z967,z7,z3,z4,z6]),(0,[z1,z7,z3,z968,z5,z6]),(0,[z1,z7,z3,z46,z88,z5]),(0,[z1,z716,z7,z3,z4,z6])]],
   [[(0,[z47,z90,z197,z4,z5,z6]),(0,[z1,z371,z3,z4,z5,z67])],[(0,[z7,z3,z4,z23,z261,z6]),(0,[z1,z7,z41,z4,z105,z6]),(0,[z1,z85,z7,z3,z5,z14]),(0,[z1,z7,z3,z4,z5,z763])],[(0,[z1,z7,z3,z4,z969,z6]),(0,[z7,z3,z4,z23,z262,z6]),(0,[z1,z7,z3,z23,z6,z380]),(0,[z1,z970,z3,z4,z5,z6]),(0,[z1,z7,z4,z832,z157,z6])],[(0,[z1,z7,z386,z22,z5,z6]),(0,[z1,z7,z3,z4,z971,z6]),(0,[z1,z3,z4,z5,z822,z6]),(0,[z1,z7,z3,z4,z972,z6]),(1,[z1,z7,z4,z832,z6]),(0,[z1,z310,z7,z3,z4,z764])],[(0,[z1,z7,z3,z4,z5,z490])],[(0,[z1,z7,z3,z4,z973,z6]),(0,[z0,z7,z768,z4,z5,z6]),(0,[z1,z7,z3,z46,z5,z308]),(0,[z1,z7,z3,z974,z5,z6])],[(0,[z1,z7,z3,z4,z975,z6]),(0,[z1,z7,z4,z976,z5,z6]),(0,[z1,z122,z3,z72,z5,z167]),(0,[z1,z7,z3,z4,z977,z6])],[(0,[z1,z69,z3,z70,z5,z67]),(0,[z1,z7,z3,z192,z6,z319])]],
   [[(0,[z1,z7,z978,z4,z5,z6]),(0,[z1,z7,z250,z4,z23,z6])],[(0,[z1,z7,z3,z4,z979,z6]),(0,[z1,z7,z3,z980,z5,z6]),(0,[z1,z95,z7,z386,z4,z5]),(0,[z1,z7,z3,z4,z5,z981])],[(0,[z1,z143,z7,z4,z157,z6]),(0,[z1,z16,z7,z5,z209,z39]),(0,[z1,z310,z7,z3,z4,z80])],[(0,[z1,z805,z3,z4,z5,z6]),(0,[z1,z982,z7,z4,z5,z6]),(0,[z700,z7,z3,z4,z9,z6]),(0,[z76,z7,z3,z4,z242,z29]),(0,[z1,z7,z3,z4,z832,z6]),(0,[z1,z7,z983,z4,z5,z6])],[(0,[z1,z7,z3,z182,z276,z6]),(0,[z1,z7,z3,z4,z984,z6]),(0,[z1,z985,z7,z3,z4,z5]),(0,[z1,z986,z3,z4,z5,z6]),(0,[z987,z7,z3,z4,z5,z6])],[(0,[z1,z7,z3,z4,z276,z189]),(0,[z1,z7,z3,z4,z988,z6])],[],[(0,[z1,z989,z3,z4,z23,z6]),(0,[z1,z7,z990,z4,z9,z6]),(0,[z991,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z992]),(0,[z1,z7,z3,z4,z5,z993]),(0,[z1,z107,z7,z211,z4,z6]),(0,[z1,z7,z3,z4,z6,z764])],[(0,[z1,z994,z3,z4,z5,z6]),(0,[z1,z995,z7,z3,z5,z6]),(0,[z1,z107,z7,z409,z4,z6])],[(0,[z1,z7,z3,z4,z5,z320]),(0,[z1,z7,z3,z996,z5,z6]),(1,[z7,z768,z4,z5,z6]),(0,[z1,z997,z3,z4,z5,z6]),(0,[z1,z998,z3,z4,z5,z6]),(0,[z1,z589,z7,z4,z9,z6]),(0,[z1,z40,z97,z7,z3,z98])],[(0,[z1,z7,z3,z999,z5,z6]),(0,[z1,z7,z3,z1000,z5,z6]),(0,[z1,z725,z7,z3,z4,z23]),(0,[z1,z26,z95,z7,z38,z5]),(0,[z1,z1001,z7,z3,z4,z6]),(0,[z1,z7,z3,z4,z104,z764])],[(0,[z1,z71,z3,z4,z23,z68])],[(0,[z1,z111,z11,z4,z5,z6])],[(0,[z198,z7,z152,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1002]),(0,[z630,z7,z3,z22,z5,z6]),(0,[z30,z7,z3,z4,z23,z6]),(0,[z1,z3,z714,z101,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1003]),(0,[z1,z7,z3,z4,z5,z1004]),(0,[z1,z1005,z7,z3,z4,z5]),(0,[z1,z7,z3,z5,z6,z1006])]],
   [[(0,[z1,z1007,z3,z4,z5,z6]),(0,[z1,z7,z3,z147,z5,z190]),(0,[z1,z7,z3,z4,z23,z816]),(0,[z1,z7,z3,z4,z5,z1008]),(0,[z1,z7,z4,z1009,z5,z6]),(0,[z1,z97,z7,z3,z192,z5])],[(0,[z1,z7,z3,z48,z5,z189]),(0,[z1,z830,z3,z4,z5,z6]),(0,[z1,z97,z7,z3,z4,z9]),(0,[z1,z1010,z7,z3,z4,z6])],[(0,[z1,z7,z1011,z4,z5,z6]),(0,[z1,z107,z7,z4,z279,z6]),(0,[z1,z1012,z7,z3,z4,z6]),(0,[z1,z1013,z3,z4,z5,z6])],[(0,[z1,z7,z3,z1014,z4,z5]),(0,[z341,z7,z3,z4,z9,z6]),(0,[z1,z1015,z7,z3,z4,z9]),(0,[z1,z43,z10,z4,z112,z6]),(0,[z1,z10,z785,z4,z5,z6]),(0,[z1,z7,z3,z4,z752,z6]),(0,[z1,z115,z3,z4,z752,z6]),(0,[z1,z181,z95,z7,z4,z5]),(0,[z1,z7,z284,z1009,z5,z6])],[(0,[z1,z7,z3,z4,z1016,z6]),(0,[z1,z248,z3,z4,z180,z6]),(0,[z559,z7,z3,z4,z5,z37]),(0,[z1,z7,z3,z4,z1017,z6])],[(0,[z1,z3,z4,z23,z946,z6]),(0,[z1,z7,z3,z46,z23,z191]),(0,[z1,z7,z41,z4,z279,z6]),(0,[z1,z551,z7,z3,z9,z6]),(0,[z1,z7,z3,z9,z209,z6]),(0,[z1,z7,z1018,z4,z5,z6]),(0,[z1,z1019,z3,z4,z5,z6]),(0,[z1020,z7,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z802,z6]),(0,[z1,z7,z3,z46,z5,z763])],[(0,[z1,z7,z3,z4,z1021,z6]),(0,[z1,z7,z3,z48,z23,z6]),(0,[z1,z7,z3,z4,z1022,z6])],[(0,[z25,z7,z3,z4,z23,z6]),(0,[z1,z7,z244,z4,z105,z6])]],
   [[(0,[z1,z2,z3,z147,z5,z6]),(0,[z1,z85,z181,z27,z7,z5]),(1,[z1,z7,z3,z4,z764])],[(0,[z1,z7,z3,z4,z5,z1023]),(0,[z1,z7,z3,z4,z6,z1024]),(0,[z1,z843,z7,z3,z23,z6]),(0,[z1,z1025,z7,z3,z4,z6])],[(0,[z1,z7,z3,z4,z1026,z6]),(0,[z1,z7,z717,z4,z5,z6]),(0,[z1,z7,z3,z147,z5,z21]),(0,[z198,z7,z4,z13,z5,z6]),(0,[z609,z7,z3,z4,z23,z6]),(0,[z1,z656,z7,z4,z5,z39]),(0,[z1,z785,z7,z4,z5,z6])],[(0,[z1,z7,z223,z48,z5,z6]),(0,[z1,z7,z3,z4,z1027,z6])],[(0,[z1,z7,z1028,z4,z5,z6])],[(0,[z76,z7,z3,z4,z23,z29]),(0,[z1,z785,z3,z4,z5,z6]),(0,[z1,z107,z7,z4,z556,z6])],[(0,[z1,z7,z3,z1029,z5,z6]),(0,[z1,z69,z3,z4,z23,z67]),(0,[z1,z143,z7,z4,z516,z6]),(0,[z1,z140,z3,z4,z116,z6]),(0,[z1,z7,z3,z156,z5,z37]),(0,[z1,z7,z3,z4,z1030,z6])],[(0,[z1,z7,z3,z4,z235,z21]),(0,[z7,z3,z683,z4,z23,z6]),(0,[z684,z7,z3,z4,z23,z6])]],
   [[(0,[z1,z1031,z7,z3,z4,z6]),(0,[z1,z107,z7,z4,z832,z6])],[(0,[z1,z7,z3,z4,z9,z6]),(0,[z1,z143,z7,z4,z373,z6]),(0,[z1,z7,z3,z1032,z5,z6]),(0,[z1,z7,z3,z4,z1033,z6])],[(0,[z1,z207,z3,z4,z5,z190]),(0,[z1,z7,z3,z179,z9,z6]),(0,[z1,z64,z95,z7,z3,z4]),(0,[z1,z7,z3,z4,z5,z764])],[(0,[z47,z90,z3,z48,z5,z6]),(0,[z1,z7,z3,z4,z23,z87]),(0,[z1,z7,z990,z4,z5,z6]),(0,[z1,z7,z41,z4,z832,z6])],[(0,[z1,z7,z3,z4,z1034,z6]),(0,[z1,z7,z3,z5,z191,z366])],[(0,[z1,z7,z3,z4,z5,z1035]),(0,[z1,z7,z3,z4,z1036,z6]),(0,[z1,z7,z3,z156,z23,z6]),(0,[z1,z551,z7,z3,z5,z29]),(0,[z1,z7,z3,z4,z159,z764])],[(0,[z1,z7,z3,z1037,z5,z6]),(0,[z1,z2,z3,z4,z5,z190]),(0,[z1,z7,z3,z4,z114,z6]),(0,[z1,z1038,z7,z4,z9,z6]),(0,[z1,z589,z7,z4,z5,z6])],[(0,[z1039,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z23,z195])],[(0,[z1,z7,z1040,z4,z5,z6]),(0,[z1,z7,z3,z245,z4,z23]),(0,[z1,z7,z386,z4,z9,z6]),(0,[z1,z542,z3,z4,z5,z68]),(0,[z1,z7,z3,z4,z1041,z6])],[(0,[z1,z7,z3,z1042,z4,z5]),(0,[z1,z7,z3,z4,z1043,z6]),(0,[z1,z7,z3,z4,z5,z1044])],[(0,[z1,z7,z3,z4,z1045,z6]),(0,[z1,z7,z3,z4,z1046,z6]),(0,[z7,z3,z4,z23,z391,z6]),(0,[z304,z7,z3,z4,z23,z6]),(0,[z1,z1047,z7,z3,z4,z6])],[(0,[z1,z7,z3,z4,z297,z6]),(0,[z1,z207,z3,z4,z5,z21]),(0,[z1,z3,z4,z5,z1048,z6]),(0,[z1,z1049,z7,z3,z4,z6]),(0,[z143,z7,z4,z9,z23,z6]),(0,[z286,z7,z3,z4,z23,z6])],[(0,[z1,z7,z3,z4,z1050,z6]),(0,[z1,z385,z3,z4,z119,z6])],[(0,[z66,z183,z3,z4,z9,z6]),(0,[z359,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z1051,z6])],[(0,[z0,z7,z148,z147,z5,z6]),(0,[z1,z7,z3,z4,z6,z1052]),(0,[z1,z7,z3,z4,z5,z149]),(0,[z1,z181,z7,z4,z23,z36]),(0,[z133,z7,z3,z4,z5,z29]),(0,[z1,z97,z7,z3,z4,z5])]],
   [[(0,[z7,z3,z4,z736,z5,z6]),(0,[z590,z7,z3,z4,z9,z6])],[(0,[z1,z7,z3,z4,z23,z190]),(0,[z1,z1015,z7,z3,z4,z5]),(0,[z1,z551,z7,z3,z5,z6])],[(0,[z1,z7,z3,z4,z1053,z6]),(0,[z1,z7,z3,z4,z555,z6]),(0,[z574,z7,z3,z22,z5,z6]),(0,[z421,z7,z3,z4,z23,z6])],[(0,[z1,z160,z3,z101,z23,z6]),(0,[z1,z7,z3,z4,z5,z1054]),(0,[z1,z7,z3,z4,z1055,z6]),(0,[z1,z7,z3,z4,z5,z1056]),(0,[z1,z7,z3,z1057,z5,z6]),(0,[z1,z181,z7,z4,z5,z720]),(0,[z1,z7,z3,z4,z1058,z6])],[(0,[z1,z7,z3,z4,z1059,z6]),(0,[z1,z43,z15,z4,z5,z6]),(0,[z7,z3,z4,z713,z5,z6]),(0,[z1,z7,z4,z5,z1060,z6]),(0,[z1,z7,z3,z1061,z5,z6]),(0,[z494,z7,z3,z4,z5,z37]),(0,[z1,z7,z41,z4,z527,z6])],[],[(0,[z1,z7,z3,z4,z1062,z6]),(0,[z7,z585,z3,z4,z23,z6]),(0,[z1,z3,z4,z23,z6,z1063]),(0,[z1,z7,z3,z4,z1064,z6]),(0,[z1,z310,z495,z7,z3,z5])],[(0,[z1,z7,z3,z4,z1065,z6]),(0,[z1,z95,z7,z3,z22,z5]),(0,[z1,z7,z11,z4,z112,z6]),(0,[z1,z7,z3,z1066,z5,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z1067]),(0,[z1,z7,z1068,z4,z5,z6]),(0,[z1,z107,z2,z4,z5,z6]),(0,[z1,z7,z3,z4,z321,z6]),(0,[z1,z7,z3,z255,z9,z6]),(0,[z1,z122,z3,z72,z5,z87])],[(0,[z1,z7,z3,z182,z5,z189]),(0,[z1,z2,z3,z4,z23,z6]),(0,[z1,z7,z4,z279,z9,z6]),(0,[z1,z1069,z7,z3,z5,z6]),(0,[z1,z7,z3,z108,z192,z6]),(0,[z1,z7,z3,z4,z159,z104])],[(0,[z1,z143,z7,z4,z327,z6])],[(0,[z1,z7,z3,z4,z23,z21]),(0,[z1,z7,z3,z4,z5,z1070]),(0,[z1,z143,z7,z4,z104,z6]),(0,[z1,z382,z7,z3,z98,z6]),(0,[z1,z495,z7,z3,z9,z6]),(0,[z1,z7,z3,z4,z6,z1071]),(0,[z1,z40,z7,z3,z457,z6]),(0,[z1,z85,z7,z3,z358,z5])],[(0,[z7,z3,z598,z4,z23,z6]),(0,[z1,z1072,z3,z4,z5,z6]),(0,[z1,z7,z4,z5,z720,z39]),(0,[z1,z7,z3,z4,z1073,z6])],[(0,[z1,z7,z3,z4,z5,z6])],[(0,[z1,z7,z1074,z4,z5,z6]),(0,[z1,z7,z3,z48,z5,z320]),(0,[z1,z7,z3,z182,z23,z6]),(0,[z1,z7,z3,z179,z5,z6]),(0,[z1,z7,z3,z4,z464,z104]),(0,[z28,z7,z3,z4,z5,z730]),(0,[z1,z85,z7,z3,z5,z260])],[(0,[z1,z7,z3,z1075,z5,z6]),(0,[z1,z7,z3,z4,z23,z189]),(0,[z1,z107,z7,z4,z635,z6]),(0,[z1,z442,z551,z7,z3,z6])]],
   [[(0,[z1,z43,z10,z4,z23,z6]),(0,[z1,z7,z3,z4,z1076,z6]),(0,[z1,z7,z3,z4,z1077,z6]),(0,[z1,z85,z7,z3,z5,z266]),(1,[z1,z7,z3,z802,z6])],[(0,[z1,z7,z223,z4,z419,z6]),(0,[z1,z7,z3,z4,z1078,z6]),(0,[z0,z207,z148,z4,z5,z6]),(0,[z1,z7,z3,z179,z235,z6]),(0,[z1,z7,z3,z4,z6,z1079]),(0,[z76,z7,z3,z156,z5,z29]),(0,[z1,z7,z3,z4,z5,z1080]),(0,[z1,z442,z7,z3,z4,z6])],[(0,[z106,z7,z3,z713,z5,z6]),(0,[z300,z7,z3,z172,z5,z6]),(0,[z1,z1038,z7,z4,z5,z6]),(0,[z1,z10,z385,z4,z5,z6]),(0,[z1,z7,z3,z108,z84,z6]),(0,[z1,z442,z7,z3,z209,z6])],[(0,[z1,z7,z3,z5,z1081,z6]),(0,[z50,z7,z3,z22,z23,z6]),(0,[z1,z932,z3,z4,z23,z6]),(0,[z1,z143,z7,z4,z119,z6]),(0,[z1,z7,z3,z5,z1082,z6]),(0,[z1,z7,z3,z1083,z5,z6])],[(0,[z1,z7,z223,z4,z5,z189]),(0,[z354,z7,z152,z4,z5,z6]),(0,[z1,z7,z3,z365,z23,z6]),(0,[z1,z7,z3,z4,z1084,z6]),(0,[z1,z27,z95,z7,z3,z5]),(0,[z1,z644,z85,z7,z3,z5])],[(0,[z1,z7,z3,z1085,z5,z6]),(0,[z1,z107,z7,z4,z649,z6]),(0,[z1,z7,z3,z101,z5,z87]),(0,[z1,z1086,z3,z4,z5,z6]),(0,[z1,z7,z3,z46,z5,z268])],[(0,[z1,z7,z197,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1087]),(0,[z198,z7,z152,z4,z555,z6]),(1,[z1,z7,z1009,z5,z6]),(0,[z1,z551,z7,z38,z5,z6])],[(1,[z805,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z1088]),(0,[z51,z7,z3,z4,z736,z6]),(0,[z1,z7,z3,z9,z6,z878]),(0,[z660,z7,z3,z4,z9,z6])]],
   [[(0,[z7,z805,z3,z4,z5,z6]),(0,[z1,z7,z3,z1089,z5,z6]),(0,[z1,z7,z3,z4,z1090,z6]),(0,[z1,z7,z3,z4,z5,z1091])],[(0,[z1,z7,z223,z4,z23,z6]),(0,[z47,z90,z3,z4,z419,z6]),(0,[z1,z7,z3,z4,z5,z1092]),(0,[z1,z7,z3,z4,z1093,z6]),(0,[z1,z7,z1094,z4,z5,z6])],[(0,[z66,z183,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z1095,z6]),(0,[z1,z85,z7,z3,z5,z288]),(0,[z28,z7,z3,z4,z5,z37]),(0,[z1,z589,z115,z4,z119,z6]),(0,[z1,z310,z495,z7,z3,z80])],[(0,[z1,z7,z1096,z4,z5,z6]),(0,[z1,z7,z4,z105,z199,z6]),(0,[z1,z71,z3,z4,z9,z68]),(0,[z1,z1097,z7,z3,z4,z5]),(0,[z1,z27,z7,z386,z5,z6]),(0,[z1,z7,z3,z1098,z5,z6]),(0,[z1,z65,z85,z7,z3,z5])],[(0,[z47,z90,z3,z4,z5,z189]),(0,[z1,z7,z4,z817,z5,z6]),(0,[z1,z3,z4,z5,z6,z1063]),(0,[z1,z7,z568,z4,z225,z6]),(0,[z1,z350,z3,z4,z119,z6]),(0,[z1,z115,z250,z4,z119,z6]),(0,[z1,z7,z3,z4,z1099,z6])],[(0,[z1,z985,z7,z3,z4,z23]),(0,[z1,z143,z7,z4,z279,z6]),(0,[z1,z7,z3,z4,z1100,z6]),(0,[z1,z16,z7,z4,z5,z720]),(0,[z1,z7,z3,z4,z6,z1101])],[(0,[z1,z589,z7,z4,z116,z6]),(0,[z1,z7,z3,z1009,z5,z6]),(0,[z1,z40,z7,z3,z195,z98])],[(0,[z1,z7,z3,z4,z1102,z6]),(0,[z1,z16,z7,z4,z9,z39]),(0,[z1,z7,z3,z255,z321,z6])]],
   [[(0,[z1,z7,z3,z4,z5,z1103]),(0,[z0,z7,z148,z4,z23,z6]),(0,[z7,z3,z4,z23,z311,z6]),(0,[z1,z158,z7,z4,z23,z6]),(0,[z1,z7,z3,z4,z1104,z6]),(0,[z1,z7,z3,z4,z6,z1105]),(0,[z1,z7,z3,z365,z5,z67])],[(0,[z47,z90,z3,z4,z23,z6]),(0,[z1,z2,z148,z4,z5,z6]),(0,[z1,z954,z7,z4,z23,z6]),(0,[z161,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z9,z6,z380]),(0,[z1,z7,z3,z4,z1106,z6]),(0,[z1,z1107,z7,z3,z4,z6])],[(0,[z1,z7,z223,z4,z276,z6]),(0,[z1,z7,z3,z4,z1108,z6]),(0,[z1,z7,z3,z4,z5,z837]),(0,[z1,z7,z3,z4,z5,z1109]),(0,[z1,z7,z386,z172,z5,z6]),(0,[z1,z7,z3,z5,z191,z763])],[],[(0,[z1,z7,z3,z4,z82,z6]),(0,[z1,z7,z3,z255,z5,z6]),(0,[z1,z1110,z7,z3,z4,z6])],[(0,[z1,z7,z3,z48,z9,z6]),(0,[z1,z7,z3,z4,z1111,z6]),(0,[z1,z1112,z3,z4,z5,z6]),(0,[z1,z7,z4,z279,z5,z6]),(0,[z1,z7,z3,z4,z5,z1113]),(0,[z1,z16,z7,z4,z253,z39])],[(0,[z155,z7,z3,z4,z9,z6])],[(0,[z1,z7,z3,z4,z1114,z6]),(0,[z669,z7,z3,z4,z23,z6]),(0,[z1,z7,z568,z4,z105,z6]),(0,[z1,z495,z7,z3,z5,z6])]],
   [[(0,[z1,z140,z3,z4,z254,z6]),(0,[z1,z85,z7,z3,z23,z89]),(0,[z1,z834,z7,z3,z23,z6])],[(0,[z1,z7,z3,z1115,z5,z6]),(0,[z1,z1116,z3,z4,z5,z6]),(0,[z7,z4,z279,z9,z23,z6]),(0,[z1,z40,z7,z3,z226,z6]),(0,[z76,z7,z3,z4,z5,z730])],[(0,[z47,z90,z3,z4,z276,z6]),(0,[z1,z7,z3,z4,z5,z1117]),(0,[z1,z7,z3,z4,z1118,z6]),(0,[z1,z7,z4,z5,z6,z740]),(0,[z7,z3,z4,z1119,z5,z6]),(0,[z1,z7,z3,z4,z1120,z6])],[(0,[z1,z7,z1121,z4,z5,z6]),(0,[z47,z805,z3,z4,z5,z6]),(0,[z1,z504,z3,z4,z116,z6]),(1,[z1,z3,z4,z5,z822]),(0,[z1,z551,z16,z7,z5,z39])],[(0,[z1,z1122,z3,z4,z5,z6]),(0,[z1,z851,z3,z4,z9,z6]),(0,[z370,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z315,z192,z6]),(0,[z1,z43,z10,z4,z131,z6]),(0,[z1,z1123,z3,z4,z5,z6]),(0,[z1,z7,z3,z4,z1124,z6])],[(0,[z1,z7,z197,z4,z419,z6]),(0,[z1,z7,z3,z1125,z5,z6]),(0,[z106,z7,z3,z172,z177,z6]),(0,[z1,z7,z3,z4,z5,z1126])],[(0,[z1,z7,z3,z4,z23,z490]),(0,[z1,z7,z3,z1127,z5,z6]),(0,[z1,z7,z3,z1128,z5,z6]),(0,[z1,z567,z3,z4,z5,z68])],[(0,[z1,z95,z7,z3,z4,z9]),(0,[z1,z7,z3,z1129,z5,z6]),(0,[z1,z1130,z7,z3,z4,z5]),(0,[z1131,z7,z3,z4,z5,z6])]],
   [[(0,[z1,z49,z11,z4,z5,z6]),(0,[z1,z7,z4,z976,z23,z6]),(0,[z1,z43,z785,z4,z5,z6]),(0,[z1,z7,z3,z4,z5,z822])],[(0,[z1,z1132,z7,z3,z4,z5]),(0,[z1,z7,z3,z5,z1133,z6]),(0,[z1,z876,z7,z4,z5,z6]),(0,[z1,z7,z4,z23,z1060,z6]),(0,[z1,z7,z3,z1134,z5,z6]),(0,[z1,z69,z3,z365,z5,z67]),(0,[z1,z85,z7,z477,z3,z5])],[(0,[z1,z7,z3,z1135,z5,z6]),(0,[z1,z7,z3,z147,z9,z6]),(0,[z1,z7,z3,z4,z1136,z6]),(0,[z1,z989,z3,z4,z5,z6]),(0,[z1,z27,z7,z1009,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1137]),(0,[z1,z7,z3,z4,z1138,z6]),(0,[z51,z7,z3,z4,z23,z6]),(0,[z1,z7,z3,z4,z1139,z6]),(0,[z1,z7,z3,z4,z5,z1140]),(0,[z1,z7,z3,z5,z763,z89])],[(0,[z1,z7,z3,z4,z419,z320]),(0,[z1,z257,z11,z4,z5,z6]),(0,[z1,z884,z7,z4,z5,z6]),(0,[z1,z7,z3,z156,z9,z6]),(0,[z1,z7,z3,z70,z9,z6]),(0,[z1,z877,z7,z3,z9,z6]),(0,[z1,z7,z930,z386,z4,z6])],[(0,[z1,z982,z7,z4,z23,z6]),(0,[z1,z324,z7,z4,z5,z36]),(0,[z1,z7,z3,z4,z1141,z6])],[(0,[z1,z7,z3,z182,z5,z320]),(0,[z546,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z1142,z5,z6])],[(0,[z1,z7,z3,z1143,z5,z6]),(0,[z1,z71,z3,z4,z5,z68]),(1,[z1,z7,z3,z5,z763])]],
   [[(0,[z1,z7,z3,z4,z1144,z6]),(0,[z1,z7,z3,z4,z1145,z6])],[(0,[z631,z7,z3,z4,z23,z6]),(0,[z1,z401,z7,z3,z4,z80]),(0,[z1,z7,z3,z4,z1146,z6]),(0,[z1,z7,z3,z4,z5,z1147]),(0,[z1,z7,z1009,z38,z5,z6])],[(0,[z1,z3,z4,z5,z808,z6])],[(0,[z1,z3,z1148,z4,z5,z6]),(0,[z1,z7,z3,z4,z9,z167]),(0,[z1,z1149,z3,z4,z5,z6]),(0,[z1,z181,z7,z4,z5,z619]),(0,[z1,z16,z7,z4,z5,z39])],[(0,[z1,z7,z3,z4,z23,z320]),(0,[z1,z7,z3,z4,z1150,z6]),(0,[z1,z7,z3,z4,z5,z1151])],[(0,[z1,z7,z3,z147,z297,z6]),(0,[z198,z7,z152,z4,z199,z6]),(0,[z1,z7,z3,z1152,z5,z6]),(0,[z1,z26,z7,z1009,z5,z6])],[(0,[z1,z7,z3,z4,z5,z1153]),(0,[z572,z7,z3,z4,z23,z6]),(0,[z1,z7,z1154,z4,z5,z6])],[(0,[z1,z183,z197,z4,z5,z6]),(0,[z1,z1155,z3,z4,z5,z6]),(0,[z1,z7,z3,z22,z5,z490]),(0,[z1,z111,z11,z4,z23,z6]),(0,[z1,z898,z3,z4,z9,z6]),(0,[z1,z7,z3,z209,z6,z253]),(0,[z1,z1156,z3,z4,z5,z6]),(0,[z1,z7,z3,z802,z98,z6])]],
   [[(0,[z1,z7,z3,z4,z9,z190]),(0,[z198,z7,z152,z4,z23,z6]),(0,[z7,z3,z4,z23,z6,z393]),(0,[z1,z143,z310,z7,z4,z6]),(0,[z1,z7,z3,z5,z6,z1157])],[(0,[z1,z7,z3,z1158,z5,z6]),(0,[z1,z7,z3,z5,z1159,z6])],[(0,[z1,z1160,z7,z4,z5,z6])],[(0,[z1,z7,z3,z4,z1161,z6]),(0,[z1,z2,z3,z4,z5,z21]),(0,[z1,z7,z3,z1162,z5,z6]),(0,[z7,z3,z172,z713,z5,z6]),(0,[z1,z44,z7,z3,z4,z62])],[(0,[z1,z7,z3,z4,z5,z1163]),(0,[z1,z207,z3,z4,z9,z6]),(0,[z1,z1164,z3,z4,z5,z6]),(0,[z106,z7,z3,z172,z23,z6]),(0,[z7,z3,z42,z4,z23,z6]),(0,[z695,z7,z3,z4,z9,z6]),(0,[z1,z7,z3,z156,z5,z29]),(0,[z1,z7,z3,z4,z1165,z6]),(0,[z1,z7,z3,z5,z1166,z6]),(0,[z1,z7,z3,z4,z1167,z6])],[(0,[z1,z7,z3,z4,z276,z320]),(0,[z1,z124,z3,z4,z180,z6]),(0,[z1,z3,z72,z714,z5,z6]),(0,[z1,z1168,z7,z3,z5,z6]),(0,[z1,z495,z7,z3,z159,z5])],[(0,[z30,z7,z3,z172,z5,z6]),(0,[z1,z7,z3,z4,z1169,z6]),(0,[z1,z7,z3,z4,z5,z1170])],[(0,[z1,z7,z3,z4,z201,z6]),(0,[z1,z7,z3,z4,z1171,z6]),(0,[z7,z152,z768,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 531) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 531).take 531) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1062).take 144) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1206)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [531, 531, 144] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 118).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 118).take 129).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 247).take 9).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [118, 129, 9] = true :=
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

end PEqualNP.Outside.L_meta_39145

theorem PEqualNP.Outside.L_meta_39145 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4205502464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4205502464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39145.solve