import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39669

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
  Nat.testBit (4008372896 * 2 ^ 32 + 3937058944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0000142dac2a570c#64 ++ 0x0000050b6b0a95c3#64 ++ 0x79087c7ffc7fff1f#64 ++ 0xde421f1fff1fffc7#64 : BitVec 256),
   (0x8473b19c61993174#64 ++ 0x211cec6718664c5d#64 ++ 0xfef7b39c639933fd#64 ++ 0xffbdece718e64cff#64 : BitVec 256),
   (0x1b05c2e056e1c2b8#64 ++ 0x46c170b815b870ae#64 ++ 0xbf07c3e07fe1c3fd#64 ++ 0xefc1f0f81ff870ff#64 : BitVec 256),
   (0x4bb80376837e03c1#64 ++ 0x12ee00dda0df80f0#64 ++ 0xdbf803ff83fe03e1#64 ++ 0x76fe00ffe0ff80f8#64 : BitVec 256),
   (0x23dee80003d5a800#64 ++ 0x08f7ba0000f56a00#64 ++ 0xeffffc0003fffc02#64 ++ 0x7bffff0000ffff00#64 : BitVec 256),
   (0x77ef7fdb78000000#64 ++ 0x9dfbdff6de000000#64 ++ 0xf7fffffffc000000#64 ++ 0x7dffffffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [7, 5]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x79087c7ffc7fff1f 0xde421f1fff1fffc7

def z1 : W := mkw 0x1805c0a056e1c2b8 0x4601702815b870ae 0x2c07c0007fe1c3fd 0x8b01f0001ff870ff

def z2 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z3 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xeffffc0003fffc02 0x7bffff0000ffff00

def z4 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z5 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xf7fffffffc000000 0x7dffffffff000000

def z6 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xfef7b39c639933fd 0xffbdece718e64cff

def z7 : W := mkw 0x000014292c20560c 0x0000050a4b081583 0x39007c607c61ff1f 0xce401f181f187fc7

def z8 : W := mkw 0x0042a00000812000 0x0010a80000204800 0x2407b00000013000 0x0901ec0000004c00

def z9 : W := mkw 0x8473a19041912070 0x211ce8641064481c 0xeef7b380039930e0 0x7bbdece000e64c38

def z10 : W := mkw 0x7fffffffffffc3f9 0xdffffffffffff0fe 0xffffffffffffc3fd 0xfffffffffffff0ff

def z11 : W := mkw 0x24423c0928000000 0x89108f024a000000 0x00003c0000000000 0x00000f0000000000

def z12 : W := mkw 0x23cee80002c18000 0x08f3ba0000b06000 0xeffffc0003e1c000 0x7bffff0000f87000

def z13 : W := mkw 0x0030011401180140 0x000c004500460050 0xdaf0039c039803e1 0x76bc00e700e600f8

def z14 : W := mkw 0x8443b08860813034 0x2110ec2218204c0d 0x2407b0006001301c 0x8901ec0018004c07

def z15 : W := mkw 0x1005c0805481c038 0x440170201520700e 0xbe07c3807f81c3fd 0xef81f0e01fe070ff

def z16 : W := mkw 0x4b88026282660281 0x12e20098a09980a0 0x0108006380660000 0x00420018e0198000

def z17 : W := mkw 0x23ce7c0928000000 0x08f39f024a000000 0xf7fffc7ffc000000 0x7dffff1fff000000

def z18 : W := mkw 0x23defc2dafffff0c 0x08f7bf0b6bffffc3 0xfffffc7fffffff1f 0xffffff1fffffffc7

def z19 : W := mkw 0x77ffffffffffff0c 0x9dffffffffffffc3 0xffffffffffffff1f 0xffffffffffffffc7

def z20 : W := mkw 0x34477c8978000000 0x8d11df225e000000 0x2407fc007c000000 0x0901ff001f000000

def z21 : W := mkw 0x7fff7ffffb7e03c1 0x9fffdffffedf80f0 0xfffffffffffe03e1 0x7fffffffffff80f8

def z22 : W := mkw 0x0030111c21181144 0x000c044708460451 0xfaf0339c639933fd 0xfebc0ce718e64cff

def z23 : W := mkw 0x7fff7fdb7b5400c1 0x9fffdff6ded50030 0xf7ffffffff8000e0 0x7dffffffffe00038

def z24 : W := mkw 0x0300000002400000 0x00c0000000900000 0x8b00000003e00000 0x62c0000000f80000

def z25 : W := mkw 0x1005408050000000 0x0401502014000000 0x2407c0007c000000 0x0901f0001f000000

def z26 : W := mkw 0x100440001400c008 0x4401100005003002 0x000040001c00c000 0x0000100007003000

def z27 : W := mkw 0x00000024802a0300 0x00000009200a80c0 0x5908007f807e0301 0x5642001fe01f80c0

def z28 : W := mkw 0x4bb8177faf7e57cd 0x12ee05dfebdf95f3 0xfbf87fffffffffff 0xfefe1fffffffffff

def z29 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xeef7b00003993000 0x7bbdec0000e64c00

def z30 : W := mkw 0xcffa337ea37e33c5 0x33fe8cdfa8df8cf1 0xdbf833ff83fe33e1 0x76fe0cffe0ff8cf8

def z31 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x28007c007c7fff1f 0x8a001f001f1fffc7

def z32 : W := mkw 0x8473a19041912070 0x211ce8641064481c 0x86f78380038000e0 0x21bde0e000e00038

def z33 : W := mkw 0x0463b19860810030 0x0118ec661820400c 0xfef7b39c638103fd 0xffbdece718e040ff

def z34 : W := mkw 0x1805c2e054a1c2b8 0x460170b8152870ae 0x3407c3e07c01c3fd 0x8d01f0f81f0070ff

def z35 : W := mkw 0x0b0182e042e102b0 0x02c060b810b840ac 0xbf0783e063e103fd 0xefc1e0f818f840ff

def z36 : W := mkw 0x0000002004204208 0x0000000801081082 0x390040607c61c31d 0xce4010181f1870c7

def z37 : W := mkw 0x0000140da80a1504 0x000005036a028541 0x40083c1f801e3c02 0x10020f07e0078f00

def z38 : W := mkw 0x1b05c2c052c180b0 0x46c170b014b0602c 0x86078380038000e0 0x2181e0e000e00038

def z39 : W := mkw 0x8472311c21183144 0x211c8c4708460c51 0x78f0301c6019331d 0xde3c0c0718064cc7

def z40 : W := mkw 0x180102e0542042b8 0x460040b8150810ae 0x100003e07c0003fd 0x840000f81f0000ff

def z41 : W := mkw 0x3bdfeae057f5eab8 0x4ef7fab815fd7aae 0xffffffe07fffffff 0xfffffff81fffffff

def z42 : W := mkw 0x0b00026002600280 0x02c00098009800a0 0x9b0003e003e003e1 0x66c000f800f800f8

def z43 : W := mkw 0x43a8035200000000 0x10ea00d480000000 0xd3f803ff80000000 0x74fe00ffe0000000

def z44 : W := mkw 0xa7ffe99043d5a870 0x29fffa6410f56a1c 0x86f78380038000e0 0x21bde0e000e00038

def z45 : W := mkw 0x20dee8000195a800 0x0837ba0000656a00 0x64fffc00001ffc02 0x193fff000007ff00

def z46 : W := mkw 0x8473b1bce1bb3374 0x211cec6f386eccdd 0xffffb3ffe3ff33fd 0xffffecfff8ffccff

def z47 : W := mkw 0x0000100c20081104 0x0000040308020441 0x7800301c6019331d 0xde000c0718064cc7

def z48 : W := mkw 0x0001808040810030 0x000060201020400c 0xbe078380638103fd 0xef81e0e018e040ff

def z49 : W := mkw 0x5bbdc3f6d7ffc3f9 0x56ef70fdb5fff0fe 0xffffc3ffffffc3fd 0xfffff0fffffff0ff

def z50 : W := mkw 0x0300024000000000 0x00c0009000000000 0x930003e000000000 0x64c000f800000000

def z51 : W := mkw 0x8472351da91a3544 0x211c8d476a468d51 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z52 : W := mkw 0x5bbd43f6d37e03c1 0x16ef50fdb4df80f0 0xffffc3fffffe03e1 0x7ffff0ffffff80f8

def z53 : W := mkw 0x6bfeeb7683ffabc1 0x1affbadda0ffeaf0 0xffffffff83ffffe3 0x7fffffffe0fffff8

def z54 : W := mkw 0xe4fa3d1f29183144 0xb93e8f47ca460c51 0x40f83c1f80183000 0x103e0f07e0060c00

def z55 : W := mkw 0xf7ffffdf79993174 0xbdfffff7de664c5d 0xffffffffff9933fd 0xffffffffffe64cff

def z56 : W := mkw 0x180102e0542042b8 0x460040b8150810ae 0x390043e07c61c3fd 0xce4010f81f1870ff

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0x290040000061c000 0x4a40100000187000

def z58 : W := mkw 0x8472311c21183144 0x211c8c4708460c51 0x40f0301c00183000 0x103c0c0700060c00

def z59 : W := mkw 0x3b47eae056e1eab8 0x4ed1fab815b87aae 0xbf07ffe07fe1ffff 0xefc1fff81ff87fff

def z60 : W := mkw 0x20da280001142800 0x08368a0000450a00 0x00f0000000000000 0x003c000000000000

def z61 : W := mkw 0x8473a19041912070 0x211ce8641064481c 0xbef78380638103fd 0xefbde0e018e040ff

def z62 : W := mkw 0x000014092c00540c 0x000005024b001503 0x20007c007c01fc1e 0x88001f001f007f07

def z63 : W := mkw 0x130542e054204208 0x04c150b815081082 0xbf07c3e07c61c31d 0xefc1f0f81f1870c7

def z64 : W := mkw 0x0010800003d5a800 0x0004200000f56a00 0x69087c0003fffc02 0x5a421f0000ffff00

def z65 : W := mkw 0x40b80116811e0141 0x102e0045a0478050 0x40f8001f801e0000 0x103e0007e0078000

def z66 : W := mkw 0x0010800003d5a800 0x0004200000f56a00 0x0800000003fffc02 0x0200000000ffff00

def z67 : W := mkw 0x0004c00000818000 0x0001300000206000 0x2407c0000001c000 0x0901f00000007000

def z68 : W := mkw 0x0810802487ffc3f9 0x4204200921fff0fe 0x0800000003ffc3fd 0x8200000000fff0ff

def z69 : W := mkw 0x64ea3d1b28000000 0x993a8f46ca000000 0x40f83c1f80000000 0x103e0f07e0000000

def z70 : W := mkw 0x8010800401993174 0x2004200100664c5d 0x08000000039933fd 0x8200000000e64cff

def z71 : W := mkw 0x64eb3d9b68000000 0x993acf66da000000 0xf6ffbf9fe0000000 0x7dbfefe7f8000000

def z72 : W := mkw 0x4bb80372037402c1 0x12ee00dc80dd00b0 0x9bf003e003e003e1 0x66fc00f800f800f8

def z73 : W := mkw 0x77ef7fdf78081104 0x9dfbdff7de020441 0xfffffffffc19331d 0xffffffffff064cc7

def z74 : W := mkw 0x0304c00002c18000 0x00c1300000b06000 0xaf07c00003e1c000 0x6bc1f00000f87000

def z75 : W := mkw 0x3047e8805481e838 0x4c11fa2015207a0e 0x2407fc007c01fc1e 0x8901ff001f007f07

def z76 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xc6f7b39c039830e0 0x31bdece700e60c38

def z77 : W := mkw 0x4bb80356035c01c1 0x12ee00d580d70070 0xdaf0039c039803e1 0x76bc00e700e600f8

def z78 : W := mkw 0x0031819441990170 0x000c60651066405c 0xfef7839c639903fd 0xffbde0e718e640ff

def z79 : W := mkw 0x1b0442601660c288 0x46c11098059830a2 0x9b0043e01fe0c3e1 0x66c010f807f830f8

def z80 : W := mkw 0x4bb8177fab7e17c5 0x12ee05dfeadf85f1 0xdbf83fff83fe3fe3 0x76fe0fffe0ff8ff8

def z81 : W := mkw 0x0053a08041912030 0x0014e8201064480c 0xfef7b380639933fd 0xffbdece018e64cff

def z82 : W := mkw 0x23da280003542800 0x08f68a0000d50a00 0xcbf83c0003fe3c02 0x72fe0f0000ff8f00

def z83 : W := mkw 0x0398000003540000 0x00e6000000d50000 0xcbf8000003fe0000 0x72fe000000ff8000

def z84 : W := mkw 0x2046e8000081a800 0x0811ba0000206a00 0x2407fc000001fc02 0x0901ff0000007f00

def z85 : W := mkw 0x37cf7c8978000000 0x8df3df225e000000 0xe7fffc007c000000 0x79ffff001f000000

def z86 : W := mkw 0x77ffffdb79912000 0x9dfffff6de644800 0xffffffffff993000 0x7fffffffffe64c00

def z87 : W := mkw 0x73ac4f5318000000 0x9ceb13d4c6000000 0xd3f84fff9c000000 0x74fe13ffe7000000

def z88 : W := mkw 0x1005c0805481c038 0x440170201520700e 0x2407c0007c01c01c 0x8901f0001f007007

def z89 : W := mkw 0xeffffbfee3ffbbf5 0x3bfffeffb8ffeefd 0xffffffffe3ffffff 0xfffffffff8ffffff

def z90 : W := mkw 0x0305c08042c18030 0x00c1702010b0600c 0xbf07c38063e1c3fd 0xefc1f0e018f870ff

def z91 : W := mkw 0x0000140da80a1504 0x000005036a028541 0x0000001f80000000 0x00000007e0000000

def z92 : W := mkw 0x4bb80352035400c1 0x12ee00d480d50030 0x82f00380038000e0 0x20bc00e000e00038

def z93 : W := mkw 0x542117fffc2a570c 0x950845ffff0a95c3 0x100003fffc00031d 0x840000ffff0000c7

def z94 : W := mkw 0x238c480002448800 0x08e3120000912200 0x69087c00007ffc02 0x5a421f00001fff00

def z95 : W := mkw 0x48200376802a03c1 0x120800dda00a80f0 0x100003ff800003e1 0x040000ffe00000f8

def z96 : W := mkw 0xcfb913fee37e13f5 0x33ee44ffb8df84fd 0xdbf803ffe3fe03fd 0xf6fe00fff8ff80ff

def z97 : W := mkw 0xf7ffebd251912070 0xbdfffaf49464481c 0x86f78380038000e0 0x21bde0e000e00038

def z98 : W := mkw 0x40b8011201140041 0x102e004480450010 0x00f0000000000000 0x003c000000000000

def z99 : W := mkw 0x1b05d6e97ee1c2b8 0x46c175ba5fb870ae 0xff0fffffffe1c3fd 0xffc3fffffff870ff

def z100 : W := mkw 0x0010000003540000 0x0004000000d50000 0x0800000003fe0000 0x0200000000ff8000

def z101 : W := mkw 0x0b980024837e03c1 0x02e6000920df80f0 0xcbf8000003fe03e1 0x72fe000000ff80f8

def z102 : W := mkw 0x238c480002448800 0x08e3120000912200 0x01084c000066cc02 0x004213000019b300

def z103 : W := mkw 0x8421119c60081174 0x210844671802045d 0x1000039c600003fd 0x840000e7180000ff

def z104 : W := mkw 0xcffbb3fee3ff33f5 0x33feecffb8ffccfd 0xffffb3ffe3ff33fd 0xffffecfff8ffccff

def z105 : W := mkw 0x0463319860000000 0x0118cc6618000000 0xf6f7b39c60000000 0x7dbdece718000000

def z106 : W := mkw 0x8473b59d69993174 0x211ced675a664c5d 0xffffffffff9933fd 0xffffffffffe64cff

def z107 : W := mkw 0x1b15c2e4d7ffc3f9 0x46c570b935fff0fe 0xbf07c3e07fffc3fd 0xefc1f0f81ffff0ff

def z108 : W := mkw 0x0052b00c21993104 0x0014ac0308664c41 0xfef7b01c6399331d 0xffbdec0718e64cc7

def z109 : W := mkw 0x738c4e639c224608 0x9ce31398e7089182 0x01084c639c66cc02 0x00421318e719b300

def z110 : W := mkw 0x7fef7ffb7e60c288 0xdffbdffedf9830a2 0xf7fffffffc60c000 0x7dffffffff183000

def z111 : W := mkw 0x77ffffdb7bd5a800 0x9dfffff6def56a00 0xfffffffffffffc02 0x7fffffffffffff00

def z112 : W := mkw 0x542117db78000000 0x950845f6de000000 0x100003fffc000000 0x040000ffff000000

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0x69087c00007ffc02 0x5a421f00001fff00

def z114 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xffffff9c63ffffff 0xffffffe718ffffff

def z115 : W := mkw 0x00000024802a0300 0x00000009200a80c0 0x1000007f80000301 0x0400001fe00000c0

def z116 : W := mkw 0x0030011001100040 0x000c004400440010 0x82f00380038000e0 0x20bc00e000e00038

def z117 : W := mkw 0x64ea3d3fac2a570c 0x993a8f4feb0a95c3 0x79f87c7ffc7fff1f 0xde7e1f1fff1fffc7

def z118 : W := mkw 0x1b04566dbe6ad78c 0x46c1159b6f9ab5e3 0x79087c7ffc7fff1f 0xde421f1fff1fffc7

def z119 : W := mkw 0x77ef6bd250000000 0x9dfbdaf494000000 0xb7f7c3e07c000000 0x6dfdf0f81f000000

def z120 : W := mkw 0x8473b5bdedbb777c 0x211ced6f7b6edddf 0xffffffffffffffff 0xffffffffffffffff

def z121 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xaff7c00003e1c000 0x6bfdf00000f87000

def z122 : W := mkw 0x8473b59d6d99757c 0x211ced675b665d5f 0xfef7ff9c7f99ffff 0xffbdffe71fe67fff

def z123 : W := mkw 0x77ef7bda70000000 0x9dfbdef69c000000 0xf6f7b39c60000000 0x7dbdece718000000

def z124 : W := mkw 0x130542c050000000 0x04c150b014000000 0xb707c3e07c000000 0x6dc1f0f81f000000

def z125 : W := mkw 0x1b0442601660c288 0x46c11098059830a2 0x010040601c60c000 0x0040101807183000

def z126 : W := mkw 0x8473b59de99b3574 0x211ced677a66cd5d 0xfeffbf9fe39f3fff 0xffbfefe7f8e7cfff

def z127 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xfbf87fff83ffffe3 0x7efe1fffe0fffff8

def z128 : W := mkw 0x4bb80352035400c1 0x12ee00d480d50030 0xd3f803ff838000e0 0x74fe00ffe0e00038

def z129 : W := mkw 0x20da280001142800 0x08368a0000450a00 0x40f83c00001e3c02 0x103e0f0000078f00

def z130 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x71087c7ffc00031d 0xdc421f1fff0000c7

def z131 : W := mkw 0x8c73b1bce3ff33f5 0x231cec6f38ffccfd 0xfef7b39c63ff33fd 0xffbdece718ffccff

def z132 : W := mkw 0x6bfeeb7683ffabc1 0x1affbadda0ffeaf0 0xdfff83ff83fe03e1 0x77ffe0ffe0ff80f8

def z133 : W := mkw 0xa7fff99c63ddb974 0x29fffe6718f76e5d 0xffffff9c63ffffff 0xffffffe718ffffff

def z134 : W := mkw 0x7feffffffeebd7bc 0xdffbffffffbaf5ef 0xffffffffffffffff 0xffffffffffffffff

def z135 : W := mkw 0x9c2113fc742853fc 0x670844ff1d0a14ff 0x100003fc7c0003fd 0x840000ff1f0000ff

def z136 : W := mkw 0x5bbc4376977ec3c9 0x56ef10dda5dfb0f2 0xdbf843ff9ffec3e1 0x76fe10ffe7ffb0f8

def z137 : W := mkw 0x0052a00001912000 0x0014a80000644800 0xeef7b00003993000 0x7bbdec0000e64c00

def z138 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x7800307ffc19331d 0xde000c1fff064cc7

def z139 : W := mkw 0x34677d9978000000 0x8d19df665e000000 0xf6f7ff9c7c000000 0x7dbdffe71f000000

def z140 : W := mkw 0x738c4e4318000000 0x9ce31390c6000000 0x01084c639c000000 0x00421318e7000000

def z141 : W := mkw 0x4ba80376826e03c1 0x12ea00dda09b80f0 0x110803ff806603e1 0x044200ffe01980f8

def z142 : W := mkw 0x08100024837e03c1 0x0204000920df80f0 0x0800000003fe03e1 0x0200000000ff80f8

def z143 : W := mkw 0x000004258c2a570c 0x00000109630a95c3 0x09084c639c7fff1f 0x82421318e71fffc7

def z144 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x1000007ffc00031d 0x8400001fff0000c7

def z145 : W := mkw 0x77ef7ffff82a0300 0x9dfbdffffe0a80c0 0xfffffffffc7e0301 0x7fffffffff1f80c0

def z146 : W := mkw 0x0000140da80a1504 0x000005036a028541 0x71087c7ffc1e3c02 0x5c421f1fff078f00

def z147 : W := mkw 0x3bcfeae056e1c2b8 0x4ef3fab815b870ae 0xffffffe07fe1c3fd 0xfffffff81ff870ff

def z148 : W := mkw 0x0000002000200200 0x0000000800080080 0x1900006000600301 0x46400018001800c0

def z149 : W := mkw 0x23ce680000000000 0x08f39a0000000000 0xeffffc00007ffc02 0x7bffff00001fff00

def z150 : W := mkw 0x77ef7ffffc2a570c 0x9dfbdfffff0a95c3 0xfffffffffc7fff1f 0xffffffffff1fffc7

def z151 : W := mkw 0x000194adecab573c 0x0000652b7b2ad5cf 0xff0fffffffffffff 0xffc3ffffffffffff

def z152 : W := mkw 0x5c2117fff82a03c1 0x970845fffe0a80f0 0x100003fffc0003e1 0x040000ffff0000f8

def z153 : W := mkw 0x000180a044a14238 0x000060281128508e 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z154 : W := mkw 0x7fff6bd2535400c1 0x9fffdaf494d50030 0x86f78380038000e0 0x21bde0e000e00038

def z155 : W := mkw 0x1305c2c050810030 0x04c170b01420400c 0xbf07c3e07f8103fd 0xefc1f0f81fe040ff

def z156 : W := mkw 0x080000200660c288 0x42000008019830a2 0x000000000060c000 0x0000000000183000

def z157 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x41087c7f9c7efc02 0x10421f1fe71fbf00

def z158 : W := mkw 0x0388000000000000 0x00e2000000000000 0xc3f8000000000000 0x70fe000000000000

def z159 : W := mkw 0x48300376813a03c1 0x120c00dda04e80f0 0xdaf003ff839803e1 0x76bc00ffe0e600f8

def z160 : W := mkw 0x77ef7fdb7a448800 0x9dfbdff6de912200 0xf7fffffffc66cc02 0x7dffffffff19b300

def z161 : W := mkw 0x238c480002448800 0x08e3120000912200 0x0000000000000000 0x0000000000000000

def z162 : W := mkw 0x23ce680000000000 0x08f39a0000000000 0xe7fffc0000000000 0x79ffff0000000000

def z163 : W := mkw 0x0000000000000000 0x0000000000000000 0x61087c0000000000 0x58421f0000000000

def z164 : W := mkw 0x00000024802a0300 0x00000009200a80c0 0x08000000007e0301 0x02000000001f80c0

def z165 : W := mkw 0x00000024842a570c 0x00000009210a95c3 0x08000000007fff1f 0x82000000001fffc7

def z166 : W := mkw 0x77ef6bd250000000 0x9dfbdaf494000000 0x86f7838000000000 0x21bde0e000000000

def z167 : W := mkw 0x23de680003540000 0x08f79a0000d50000 0xeffffc0003fe0000 0x7bffff0000ff8000

def z168 : W := mkw 0x0463359968000000 0x0118cd665a000000 0xf7fffffffc000000 0x7dffffffff000000

def z169 : W := mkw 0x4bbcc37683ff83c1 0x12ef30dda0ffe0f0 0xffffc3ff83ffc3e1 0x7ffff0ffe0fff0f8

def z170 : W := mkw 0x4bb8837687ffc3f9 0x52ee20dda1fff0fe 0xdbf803ff83ffc3fd 0xf6fe00ffe0fff0ff

def z171 : W := mkw 0x8473b19c63ddb974 0x211cec6718f76e5d 0xfef7b39c63ffffff 0xffbdece718ffffff

def z172 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x50083c7ffc1e3f1f 0x94020f1fff078fc7

def z173 : W := mkw 0x7b8c4e631e60c288 0xdee31398c79830a2 0x01084c639c60c000 0x00421318e7183000

def z174 : W := mkw 0x7feffffb7ee1c2b8 0xdffbfffedfb870ae 0xffffffffffe1c3fd 0xfffffffffff870ff

def z175 : W := mkw 0x9447f0887481f03c 0x6511fc221d207c0f 0x2407f0007c01f01c 0x8901fc001f007c07

def z176 : W := mkw 0x1001008054004038 0x440040201500100e 0x000000007c00001c 0x800000001f000007

def z177 : W := mkw 0x00100004811e0141 0x0004000120478050 0x00000000001e0000 0x0000000000078000

def z178 : W := mkw 0x8473319c61183144 0x211ccc6718460c51 0xf6f7b39c60183000 0x7dbdece718060c00

def z179 : W := mkw 0x8000800000813034 0x2000200000204c0d 0x000000000001301c 0x8000000000004c07

def z180 : W := mkw 0x40b80136813e0341 0x102e004da04f80d0 0x59f8007f807e0301 0x567e001fe01f80c0

def z181 : W := mkw 0x4bb80376877e57cd 0x12ee00dda1df95f3 0xdbf803ff83ffffff 0xf6fe00ffe0ffffff

def z182 : W := mkw 0x53ad43d250000000 0x14eb50f494000000 0xf7ffc3fffc000000 0x7dfff0ffff000000

def z183 : W := mkw 0x23ce680002448800 0x08f39a0000912200 0xe7fffc000066cc02 0x79ffff000019b300

def z184 : W := mkw 0x1b05d6edfeebd7bc 0x46c175bb7fbaf5ef 0xff0fffffffffffff 0xffc3ffffffffffff

def z185 : W := mkw 0x33cf6ac050000000 0x0cf3dab014000000 0xf7ffffe07c000000 0x7dfffff81f000000

def z186 : W := mkw 0x3447fc897881a800 0x8d11ff225e206a00 0x2407fc007c01fc02 0x0901ff001f007f00

def z187 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0x86f7800003800000 0x21bde00000e00000

def z188 : W := mkw 0x0052a00001912000 0x0014a80000644800 0x86f7800003800000 0x21bde00000e00000

def z189 : W := mkw 0x23def80c23ddb904 0x08f7be0308f76e41 0xfffffc1c63ffff1f 0xffffff0718ffffc7

def z190 : W := mkw 0xf7ffffdb79912070 0xbdfffff6de64481c 0xf7ffffffff8000e0 0x7dffffffffe00038

def z191 : W := mkw 0x48b80376813e03c1 0x122e00dda04f80f0 0x50f803ff801e03e1 0x143e00ffe00780f8

def z192 : W := mkw 0x1b0446619e62c688 0x46c111986798b1a2 0x01084c639c66cc02 0x00421318e719b300

def z193 : W := mkw 0x20da3c2dad3e7f0c 0x08368f0b6b4f9fc3 0x79f87c7ffc7fff1f 0xde7e1f1fff1fffc7

def z194 : W := mkw 0x4ffb33fee37e03c1 0x13feccffb8df80f0 0xffffb3ffe3fe03e1 0x7fffecfff8ff80f8

def z195 : W := mkw 0x572557db78000000 0x95c955f6de000000 0xb707c3fffc000000 0x6dc1f0ffff000000

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0x40083c00001e3c02 0x10020f0000078f00

def z197 : W := mkw 0x77ef6fd358000000 0x9dfbdbf4d6000000 0x87ffcfe39c000000 0x21fff3f8e7000000

def z198 : W := mkw 0x63feeb5203d5a800 0x18ffbad480f56a00 0xffffffff83fffc02 0x7fffffffe0ffff00

def z199 : W := mkw 0x4bb80376877e43c9 0x12ee00dda1df90f2 0xfbf843ffffffc3fd 0xfefe10fffffff0ff

def z200 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xc6ffbf9f80000000 0x31bfefe7e0000000

def z201 : W := mkw 0x4bb80352035400c1 0x12ee00d480d50030 0xcbf8038003fe00e0 0x72fe00e000ff8038

def z202 : W := mkw 0x0000000400080100 0x0000000100020040 0x5800001c00180301 0x56000007000600c0

def z203 : W := mkw 0x1800026014204288 0x46000098050810a2 0x000000601c000000 0x0000001807000000

def z204 : W := mkw 0x0800802006e1c2b8 0x4200200801b870ae 0x0800000003e1c3fd 0x8200000000f870ff

def z205 : W := mkw 0x6ffa3f7fab7e03c1 0x9bfe8fdfeadf80f0 0xdbf83fff83fe03e1 0x76fe0fffe0ff80f8

def z206 : W := mkw 0x546337db78000000 0x9518cdf6de000000 0xf6f7b3fffc000000 0x7dbdecffff000000

def z207 : W := mkw 0x77ad5fdb78000000 0x9deb57f6de000000 0x11084ffffc000000 0x044213ffff000000

def z208 : W := mkw 0x180116edfc2a57bc 0x460045bb7f0a95ef 0x100003fffc0003fd 0x840000ffff0000ff

def z209 : W := mkw 0x000080000481c038 0x400020000120700e 0x000000000001c01c 0x8000000000007007

def z210 : W := mkw 0x0001808040810030 0x000060201020400c 0x240780006001001c 0x8901e00018004007

def z211 : W := mkw 0x8030811401993174 0x200c204500664c5d 0xdaf0039c039933fd 0xf6bc00e700e64cff

def z212 : W := mkw 0x000004218c224608 0x0000010863089182 0x01084c639c66cc02 0x00421318e719b300

def z213 : W := mkw 0x37477ec978000000 0x8dd1dfb25e000000 0xb707ffe07c000000 0x6dc1fff81f000000

def z214 : W := mkw 0x00300134813a0340 0x000c004d204e80d0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z215 : W := mkw 0x0098000001140000 0x0026000000450000 0x40f80000001e0000 0x103e000000078000

def z216 : W := mkw 0x738c4e431a448800 0x9ce31390c6912200 0x01084c639c66cc02 0x00421318e719b300

def z217 : W := mkw 0x1005c08050818030 0x440170201420600c 0x0407800000000000 0x0101e00000000000

def z218 : W := mkw 0xb447fc8978813034 0xad11ff225e204c0d 0x2407fc007c01301c 0x8901ff001f004c07

def z219 : W := mkw 0x2bdee82007f5eab8 0x4af7ba0801fd7aae 0xeffffc0003ffffff 0xfbffff0000ffffff

def z220 : W := mkw 0x1b0102e0566042b8 0x46c040b8159810ae 0x9b0003e07fe003fd 0xe6c000f81ff800ff

def z221 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0x2507c0607c61c01c 0x8941f0181f187007

def z222 : W := mkw 0x43b8035601180140 0x10ee00d580460050 0xdbf803ff839803e1 0x76fe00ffe0e600f8

def z223 : W := mkw 0x0800800002c180b0 0x4200200000b0602c 0x00000000038000e0 0x0000000000e00038

def z224 : W := mkw 0x1b05d6edfeebd7bc 0x46c175bb7fbaf5ef 0xbf07c3ffffe1c3fd 0xefc1f0fffff870ff

def z225 : W := mkw 0x08100000035400c1 0x0204000000d50030 0x00000000038000e0 0x0000000000e00038

def z226 : W := mkw 0x0810802007f5eab8 0x4204200801fd7aae 0x0800000003ffffff 0x8200000000ffffff

def z227 : W := mkw 0x0304c00002c18000 0x00c1300000b06000 0x8607800003800000 0x2181e00000e00000

def z228 : W := mkw 0x64ea3d1b28000000 0x993a8f46ca000000 0x71f87c7ffc000000 0x5c7e1f1fff000000

def z229 : W := mkw 0x5bbdc3f257f5c2f9 0x56ef70fc95fd70be 0xbff7c3e07fe1c3fd 0xeffdf0f81ff870ff

def z230 : W := mkw 0x5bbdc3f6d3ff83f1 0x56ef70fdb4ffe0fc 0xdfff83ff83fe03e1 0x77ffe0ffe0ff80f8

def z231 : W := mkw 0x3b8c4a601664ca88 0x4ee31298059932a2 0x01084c601c66cc02 0x004213180719b300

def z232 : W := mkw 0x4088000280060001 0x10220000a0018000 0x0008000380060000 0x00020000e0018000

def z233 : W := mkw 0x9f77f3fc77f9f3fc 0x67ddfcff1dfe7cff 0xfff7f3fc7ff9f3fd 0xfffdfcff1ffe7cff

def z234 : W := mkw 0x30044c0118000000 0x8c01130046000000 0x00004c001c000000 0x0000130007000000

def z235 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0x92f003ff838003e1 0x24bc00ffe0e000f8

def z236 : W := mkw 0xcffbb7ffefff77fd 0x33feedfffbffddff 0xffffffffffffffff 0xffffffffffffffff

def z237 : W := mkw 0x8421019040000070 0x210840641000001c 0x00000380000000e0 0x000000e000000038

def z238 : W := mkw 0x0010000001142800 0x0004000000450a00 0x00000000001e3c02 0x0000000000078f00

def z239 : W := mkw 0x43b80356811e0141 0x10ee00d5a0478050 0xd3f803ff801e0000 0x74fe00ffe0078000

def z240 : W := mkw 0x03b80114035c0140 0x00ee004500d70050 0xdbf8039c03fe03e1 0x76fe00e700ff80f8

def z241 : W := mkw 0x23de68000354a800 0x08f79a0000d52a00 0x41f87c00007efc02 0x107e1f00001fbf00

def z242 : W := mkw 0x8453b08861913034 0x2114ec2218644c0d 0xeef7b0006399301c 0xfbbdec0018e64c07

def z243 : W := mkw 0x0398800003d5a800 0x00e6200000f56a00 0xcbf8000003fffc02 0x72fe000000ffff00

def z244 : W := mkw 0x00001429ac22560c 0x0000050a6b089583 0x21087c63fc67fc1e 0x88421f18ff19ff07

def z245 : W := mkw 0xcffbb3de63dd31f5 0x33feecf798f74c7d 0xfef7b39c639933fd 0xffbdece718e64cff

def z246 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x3900407ffc61c31d 0xce40101fff1870c7

def z247 : W := mkw 0x0030011401180140 0x000c004500460050 0x40f0001c00180000 0x103c000700060000

def z248 : W := mkw 0x23dfe88043d5a830 0x08f7fa2010f56a0c 0xffffff8063ffffff 0xffffffe018ffffff

def z249 : W := mkw 0x2056e80003d5a800 0x0815ba0000f56a00 0x2c07fc0003fffc02 0x0b01ff0000ffff00

def z250 : W := mkw 0x7fefffdb7ac180b0 0xdffbfff6deb0602c 0xf7ffffffff8000e0 0x7dffffffffe00038

def z251 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0x96f783fffc000000 0x25bde0ffff000000

def z252 : W := mkw 0x20da3c0da91e3d04 0x08368f036a478f41 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z253 : W := mkw 0x8010800403ddb974 0x2004200100f76e5d 0x0800000003ffffff 0x8200000000ffffff

def z254 : W := mkw 0x0800002082660281 0x02000008209980a0 0x0000000000660000 0x0000000000198000

def z255 : W := mkw 0x0b00826006e1c2b8 0x42c0209801b870ae 0x9b0003e003e1c3fd 0xe6c000f800f870ff

def z256 : W := mkw 0x40b8151fa91e1545 0x102e0547ea478551 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z257 : W := mkw 0x7fefebf256e1c2b8 0xdffbfafc95b870ae 0xbff7c3e07fe1c3fd 0xeffdf0f81ff870ff

def z258 : W := mkw 0x0b98026003740280 0x02e6009800dd00a0 0xdbf803e003fe03e1 0x76fe00f800ff80f8

def z259 : W := mkw 0x77ef7ffffc2a570c 0x9dfbdfffff0a95c3 0xf7fffffffc00031d 0xfdffffffff0000c7

def z260 : W := mkw 0x1b05c2c052c180b0 0x46c170b014b0602c 0xbe078380638103fd 0xef81e0e018e040ff

def z261 : W := mkw 0x5b8dc2e2d6e7c2b9 0x56e370b8b5b9f0ae 0xbf0fc3e3ffe7c3fd 0xefc3f0f8fff9f0ff

def z262 : W := mkw 0x1b05c2e052e182b0 0x46c170b814b860ac 0x9f0783e003e003e1 0x67c1e0f800f800f8

def z263 : W := mkw 0x6bfa2b76837e2bc1 0x1afe8adda0df8af0 0xdbf83fff83fe3fe3 0x76fe0fffe0ff8ff8

def z264 : W := mkw 0x8000000400081174 0x200000010002045d 0x00000000000003fd 0x80000000000000ff

def z265 : W := mkw 0x1b57e2e057f1e2b8 0x46d5f8b815fc78ae 0xfff7f3e07ff9f3fd 0xfffdfcf81ffe7cff

def z266 : W := mkw 0x180182e054a142b8 0x460060b8152850ae 0xbe0783e07f8103fd 0xef81e0f81fe040ff

def z267 : W := mkw 0x5bb903f6d77e43f9 0x56ee40fdb5df90fe 0xdbf803fffffe03fd 0xf6fe00ffffff80ff

def z268 : W := mkw 0x8052a00401993174 0x2014a80100664c5d 0xeef7b000039933fd 0xfbbdec0000e64cff

def z269 : W := mkw 0x238c5c2dae6edf0c 0x08e3170b6b9bb7c3 0x79087c7ffc7fff1f 0xde421f1fff1fffc7

def z270 : W := mkw 0x0052200001102000 0x0014880000440800 0x40f0300000183000 0x103c0c0000060c00

def z271 : W := mkw 0x43b8035203540000 0x10ee00d480d50000 0xdbf803ff83fe0000 0x76fe00ffe0ff8000

def z272 : W := mkw 0x0000140928000000 0x000005024a000000 0x71087c7ffc000000 0x5c421f1fff000000

def z273 : W := mkw 0x8473a19441993174 0x211ce86510664c5d 0x8ef78380039933fd 0xa3bde0e000e64cff

def z274 : W := mkw 0x8010800001912070 0x200420000064481c 0x00000000038000e0 0x0000000000e00038

def z275 : W := mkw 0x0001008040000000 0x0000402010000000 0xb607838060000000 0x6d81e0e018000000

def z276 : W := mkw 0x23dee82007f5ea08 0x08f7ba0801fd7a82 0xfffffc607fffff1f 0xffffff181fffffc7

def z277 : W := mkw 0x0b00024002400080 0x02c0009000900020 0x82000380038000e0 0x208000e000e00038

def z278 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x11084c7ffc66cf1f 0x8442131fff19b3c7

def z279 : W := mkw 0x0800802486ebd7bc 0x4200200921baf5ef 0x0800000003ffffff 0x8200000000ffffff

def z280 : W := mkw 0x08100024877e57cd 0x0204000921df95f3 0x0800000003ffffff 0x8200000000ffffff

def z281 : W := mkw 0x8443b4896c81743c 0x2110ed225b205d0f 0x2407fc007c01fc1e 0x8901ff001f007f07

def z282 : W := mkw 0x64ea291200000000 0x993a8a4480000000 0x00f0000000000000 0x003c000000000000

def z283 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x1800007ffc7fff1f 0x8600001fff1fffc7

def z284 : W := mkw 0x000014092c00540c 0x000005024b001503 0x71087c7ffc01fc1e 0xdc421f1fff007f07

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z286 : W := mkw 0x0030153dad3a574c 0x000c054f6b4e95d3 0xfbf87fffffffffff 0xfefe1fffffffffff

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0x380000006001031d 0xce000000180040c7

def z288 : W := mkw 0x2046fc092c81fc0c 0x0811bf024b207f03 0x2407fc007c01fc1e 0x8901ff001f007f07

def z289 : W := mkw 0x1b05c6e1dee3c6b8 0x46c171b877b8f1ae 0xbf0fcfe3ffe7cfff 0xefc3f3f8fff9f3ff

def z290 : W := mkw 0x48b80136837e03c1 0x122e004da0df80f0 0x48f8001f83fe03e1 0x123e0007e0ff80f8

def z291 : W := mkw 0x1b0542e05660c288 0x46c150b8159830a2 0xb707c3e07c60c000 0x6dc1f0f81f183000

def z292 : W := mkw 0x8443a08040812030 0x2110e8201020480c 0x0407800000000000 0x0101e00000000000

def z293 : W := mkw 0x0b300374037803c0 0x02cc00dd00de00f0 0xdbf003fc03f803e1 0x76fc00ff00fe00f8

def z294 : W := mkw 0x1b9dc2e057f5c2b8 0x46e770b815fd70ae 0xffffc3e07fffc3fd 0xfffff0f81ffff0ff

def z295 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0x960783e07f8003fd 0xa581e0f81fe000ff

def z296 : W := mkw 0x0000140dac0a550c 0x000005036b029543 0x60087c1ffc1ffc1e 0x98021f07ff07ff07

def z297 : W := mkw 0x0010800001912000 0x0004200000644800 0x0800000003993000 0x0200000000e64c00

def z298 : W := mkw 0x0000002004204208 0x0000000801081082 0x080000000061c31d 0x82000000001870c7

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a000380038003e1 0x668000e000e000f8

def z300 : W := mkw 0x27ef799860000000 0x09fbde6618000000 0xf7ffff9c60000000 0x7dffffe718000000

def z301 : W := mkw 0x4b88024202440081 0x12e2009080910020 0x0000000000000000 0x0000000000000000

def z302 : W := mkw 0x0304400000000000 0x00c1100000000000 0xa707c00000000000 0x69c1f00000000000

def z303 : W := mkw 0x0000100820000000 0x0000040208000000 0x7000301c60000000 0x5c000c0718000000

def z304 : W := mkw 0x7bffebf6d7ffebf9 0x5efffafdb5fffafe 0xffffffffffffffff 0xffffffffffffffff

def z305 : W := mkw 0x4b88166fae6e578d 0x12e2059beb9b95e3 0x79087c7ffc7fff1f 0xde421f1fff1fffc7

def z306 : W := mkw 0x77ef7ffb7c204208 0x9dfbdffedf081082 0xfffffffffc61c31d 0xffffffffff1870c7

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x01084c000066cc02 0x004213000019b300

def z308 : W := mkw 0x77ff7fdb79142800 0x9dffdff6de450a00 0xf7fffffffc1e3c02 0x7dffffffff078f00

def z309 : W := mkw 0xa7fff99c61993174 0x29fffe6718664c5d 0xffffff9c639933fd 0xffffffe718e64cff

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x08000000007ffc02 0x02000000001fff00

def z311 : W := mkw 0x842115bdec2a577c 0x2108456f7b0a95df 0x100003fffc0003fd 0x840000ffff0000ff

def z312 : W := mkw 0x0042200000000000 0x0010880000000000 0xe6f7b00000000000 0x79bdec0000000000

def z313 : W := mkw 0x08100024837e03c1 0x0204000920df80f0 0x5908007f83fe03e1 0x5642001fe0ff80f8

def z314 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0x64f7b01c6019301c 0x993dec0718064c07

def z315 : W := mkw 0x77efffdb7c81c038 0xddfbfff6df20700e 0xf7fffffffc01c01c 0xfdffffffff007007

def z316 : W := mkw 0x7b8c4e639a660281 0x9ee31398e69980a0 0x01084c639c660000 0x00421318e7198000

def z317 : W := mkw 0x1b0442601660c288 0x46c11098059830a2 0x390040607c61c31d 0xce4010181f1870c7

def z318 : W := mkw 0x000014092c00540c 0x000005024b001503 0x69087c007c7ffc1e 0xda421f001f1fff07

def z319 : W := mkw 0x77ff7fdb7b540000 0x9dffdff6ded50000 0xfffffffffffe0000 0x7fffffffffff8000

def z320 : W := mkw 0x9f25d3fc76e9d3fc 0x67c974ff1dba74ff 0xbf07c3fc7fe1c3fd 0xefc1f0ff1ff870ff

def z321 : W := mkw 0x73deee431bd5a800 0x9cf7bb90c6f56a00 0xeffffc639ffffc02 0x7bffff18e7ffff00

def z322 : W := mkw 0x8473b5bdedbb777c 0x211ced6f7b6edddf 0xfef7b3ffff9933fd 0xffbdecffffe64cff

def z323 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xcfff800003fe0000 0x73ffe00000ff8000

def z324 : W := mkw 0x0000800000810000 0x0000200000204000 0xae07800003810000 0x6b81e00000e04000

def z325 : W := mkw 0x0000002004204208 0x0000000801081082 0x79087c607c7fff1f 0xde421f181f1fffc7

def z326 : W := mkw 0x08000020042042b8 0x42000008010810ae 0x00000000000003fd 0x80000000000000ff

def z327 : W := mkw 0x0473b19861912000 0x011cec6618644800 0xfef7b39c63993000 0x7fbdece718e64c00

def z328 : W := mkw 0x0398000003540000 0x00e6000000d50000 0x82f0000003800000 0x20bc000000e00000

def z329 : W := mkw 0x43b80116835e0141 0x10ee0045a0d78050 0xcbf8001f83fe0000 0x72fe0007e0ff8000

def z330 : W := mkw 0x23de680001142800 0x08f79a0000450a00 0xe7fffc00001e3c02 0x79ffff0000078f00

def z331 : W := mkw 0x77ee7f5b38000000 0x9dfb9fd6ce000000 0x41f87c7f9c000000 0x107e1f1fe7000000

def z332 : W := mkw 0x4bb80356835e01c1 0x12ee00d5a0d78070 0xc2f8039f839e00e0 0x30be00e7e0e78038

def z333 : W := mkw 0x8810802483ff33f5 0x2204200920ffccfd 0x0800000003ff33fd 0x8200000000ffccff

def z334 : W := mkw 0x0000002080220200 0x0000000820088080 0x0108006380660000 0x00420018e0198000

def z335 : W := mkw 0x7fefebd252c180b0 0xdffbfaf494b0602c 0x86f78380038000e0 0x21bde0e000e00038

def z336 : W := mkw 0x40b80116811e0141 0x102e0045a0478050 0xdaf8039f839e03e1 0x76be00e7e0e780f8

def z337 : W := mkw 0x40a8011200000000 0x102a004480000000 0x40f8001f80000000 0x103e0007e0000000

def z338 : W := mkw 0x1b04c26016e1c288 0x46c1309805b870a2 0xaf07c0601fe1c000 0x6bc1f01807f87000

def z339 : W := mkw 0xf7efffdb78813034 0xbdfbfff6de204c0d 0xf7fffffffc01301c 0xfdffffffff004c07

def z340 : W := mkw 0x0052b42dadbb770c 0x0014ad0b6b6eddc3 0xfffffc7fffffff1f 0xffffff1fffffffc7

def z341 : W := mkw 0x77ffffdb7bd5a800 0x9dfffff6def56a00 0xf7ffffffff800000 0x7dffffffffe00000

def z342 : W := mkw 0x2042280000002800 0x08108a0000000a00 0x00003c0000003c02 0x00000f0000000f00

def z343 : W := mkw 0x1b05c2c052c180b0 0x46c170b014b0602c 0xb707c3e07f8000e0 0x6dc1f0f81fe00038

def z344 : W := mkw 0x0052a00001912000 0x0014a80000644800 0xeffffc0003fffc02 0x7bffff0000ffff00

def z345 : W := mkw 0x4b980266837e03c1 0x12e60099a0df80f0 0x0908006383fe03e1 0x02420018e0ff80f8

def z346 : W := mkw 0x5b8c42629666c289 0x56e31098a599b0a2 0x010840639c66c000 0x00421018e719b000

def z347 : W := mkw 0x3f47fee97ee1c2b8 0xcfd1ffba5fb870ae 0xbf07ffe07fe1c3fd 0xefc1fff81ff870ff

def z348 : W := mkw 0x0b000264826a0380 0x02c00099209a80e0 0xdb0803ff83fe03e1 0x76c200ffe0ff80f8

def z349 : W := mkw 0x8442300820003004 0x21108c0208000c01 0x0000300000003000 0x00000c0000000c00

def z350 : W := mkw 0x4b880266826e0381 0x12e20099a09b80e0 0x5908007f807e0301 0x5642001fe01f80c0

def z351 : W := mkw 0x100102c050000000 0x040040b014000000 0x100003e07c000000 0x040000f81f000000

def z352 : W := mkw 0xc7fbb3de61993174 0x31feecf798664c5d 0xffffb3ffe39933fd 0xffffecfff8e64cff

def z353 : W := mkw 0x9f77f7fdfffbf7fc 0x67ddfdff7ffefdff 0xffffffffffffffff 0xffffffffffffffff

def z354 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0x8ef7800003fffc02 0x23bde00000ffff00

def z355 : W := mkw 0x2088080000040800 0x0822020000010200 0x00080c0000060c02 0x0002030000018300

def z356 : W := mkw 0x3447fc897c81c038 0xcd11ff225f20700e 0x2407fc007c01c01c 0x8901ff001f007007

def z357 : W := mkw 0x77ff7fdf79180140 0x9dffdff7de460050 0xffffffffff9803e1 0x7fffffffffe600f8

def z358 : W := mkw 0x9777f3dc71993174 0x25ddfcf71c664c5d 0xfff7f3fc7f9933fd 0xfffdfcff1fe64cff

def z359 : W := mkw 0x08000024802a03c1 0x02000009200a80f0 0x00000000000003e1 0x00000000000000f8

def z360 : W := mkw 0x239c480003548800 0x08e7120000d52200 0xcbf84c0003fecc02 0x72fe130000ffb300

def z361 : W := mkw 0x9b15c2e457f9f3fc 0x66c570b915fe7cff 0xbf07c3e07ff9f3fd 0xefc1f0f81ffe7cff

def z362 : W := mkw 0x9f77f3dc73d9b1f4 0x67ddfcf71cf66c7d 0xfef7b39c639933fd 0xffbdece718e64cff

def z363 : W := mkw 0x0000000000000000 0x0000000000000000 0x5108007f80000000 0x5442001fe0000000

def z364 : W := mkw 0x0800942daeebd7bc 0x4200250b6bbaf5ef 0x79087c7fffffffff 0xde421f1fffffffff

def z365 : W := mkw 0x0314c00003d5a800 0x00c5300000f56a00 0xaf07c00003fffc02 0x6bc1f00000ffff00

def z366 : W := mkw 0x0810142daf7e57cd 0x0204050b6bdf95f3 0x79087c7fffffffff 0xde421f1fffffffff

def z367 : W := mkw 0x1b35c3f457f9c3f8 0x46cd70fd15fe70fe 0xfff7c3fc7ff9c3fd 0xfffdf0ff1ffe70ff

def z368 : W := mkw 0x8472211001102040 0x211c884400440810 0x00f0000000000000 0x003c000000000000

def z369 : W := mkw 0x0800802006e1c2b8 0x4200200801b870ae 0x390040607fe1c3fd 0xce4010181ff870ff

def z370 : W := mkw 0x7ffffffb7ff5eab8 0xdffffffedffd7aae 0xffffffffffffffff 0xffffffffffffffff

def z371 : W := mkw 0x4820177fac2a57cd 0x120805dfeb0a95f3 0x79087ffffc7fffff 0xde421fffff1fffff

def z372 : W := mkw 0x1b05d6e97ee1d6bc 0x46c175ba5fb875af 0xbf07ffe07fe1ffff 0xefc1fff81ff87fff

def z373 : W := mkw 0x0304d42daeebd70c 0x00c1350b6bbaf5c3 0xff0ffc7fffffff1f 0xffc3ff1fffffffc7

def z374 : W := mkw 0x1b05c2e4d6ebc3b8 0x46c170b935baf0ee 0xff0fc3ffffffc3fd 0xffc3f0fffffff0ff

def z375 : W := mkw 0x2bdeea6003f5aa80 0x0af7ba9800fd6aa0 0xffffffe003ffffe3 0x7ffffff800fffff8

def z376 : W := mkw 0x48300376837e03c1 0x120c00dda0df80f0 0x180003ff83fe03e1 0x060000ffe0ff80f8

def z377 : W := mkw 0xd42117df78081174 0xb50845f7de02045d 0x100003fffc0003fd 0x840000ffff0000ff

def z378 : W := mkw 0x00000004800a0100 0x0000000120028040 0x4008001f801e0000 0x10020007e0078000

def z379 : W := mkw 0x0052a00003d5a800 0x0014a80000f56a00 0xeef7b00003fffc02 0x7bbdec0000ffff00

def z380 : W := mkw 0x2346e80002c1a800 0x08d1ba0000b06a00 0xaf07fc0003e1fc02 0x6bc1ff0000f87f00

def z381 : W := mkw 0x4800026280220281 0x12000098a00880a0 0x0000006380000000 0x00000018e0000000

def z382 : W := mkw 0x1f67f3f876e1c2b8 0x47d9fcfe1db870ae 0xfff7f3fc7fe1c3fd 0xfffdfcff1ff870ff

def z383 : W := mkw 0x74eb3fdb78000000 0x9d3acff6de000000 0x50f83ffffc000000 0x143e0fffff000000

def z384 : W := mkw 0x5b25c3f6d6ebc3f9 0x56c970fdb5baf0fe 0xbf07c3ffffe1c3fd 0xefc1f0fffff870ff

def z385 : W := mkw 0x0000000400081104 0x0000000100020441 0x080000000019331d 0x8200000000064cc7

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x310040607c000000 0x4c4010181f000000

def z387 : W := mkw 0x0010800003d5a800 0x0004200000f56a00 0x0000000003800000 0x0000000000e00000

def z388 : W := mkw 0x4b88026282660281 0x12e20098a09980a0 0x9b0803e383e603e1 0x66c200f8e0f980f8

def z389 : W := mkw 0x23defc092bd5a800 0x08f7bf024af56a00 0xfffffc7ffffffc02 0x7fffff1fffffff00

def z390 : W := mkw 0x8443b08860813034 0x2110ec2218204c0d 0xbe07b380638133fd 0xef81ece018e04cff

def z391 : W := mkw 0x67ea3f5b28000000 0x99fa8fd6ca000000 0xd3f83fff80000000 0x74fe0fffe0000000

def z392 : W := mkw 0x3bdeea6017f5ea88 0x4ef7ba9805fd7aa2 0xeffffc601ffffc02 0x7bffff1807ffff00

def z393 : W := mkw 0x2046680000000000 0x08119a0000000000 0x2407fc0000000000 0x0901ff0000000000

def z394 : W := mkw 0x542117fffc2a570c 0x950845ffff0a95c3 0x79087ffffc7fff1f 0xde421fffff1fffc7

def z395 : W := mkw 0x0000002004204208 0x0000000801081082 0x010040601c60c000 0x0040101807183000

def z396 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0x96f7839c638003fd 0xa5bde0e718e000ff

def z397 : W := mkw 0x4bb8137ea37e13c5 0x12ee04dfa8df84f1 0xfbf833ffe3ff33fd 0xfefe0cfff8ffccff

def z398 : W := mkw 0x63fee91683dfa941 0x18ffba45a0f7ea50 0xeffffc1f83fffc02 0x7bffff07e0ffff00

def z399 : W := mkw 0x0000100c20081104 0x0000040308020441 0x4000301c00183000 0x10000c0700060c00

def z400 : W := mkw 0x0000000000000000 0x0000000000000000 0x49080000007e0000 0x52420000001f8000

def z401 : W := mkw 0x8463b19860813034 0x2118ec6618204c0d 0xf6f7b39c6001301c 0xfdbdece718004c07

def z402 : W := mkw 0x03980024837e0300 0x00e6000920df80c0 0xdbf8007f83fe0301 0x76fe001fe0ff80c0

def z403 : W := mkw 0x238cc80002c58800 0x08e3320000b16200 0xaf0fcc0003e7cc02 0x6bc3f30000f9f300

def z404 : W := mkw 0x23defc092fd5fc0c 0x08f7bf024bf57f03 0xeffffc007ffffc1e 0xfbffff001fffff07

def z405 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xe7fffc0003800000 0x79ffff0000e00000

def z406 : W := mkw 0x7fef7ffb7a600280 0x9ffbdffede9800a0 0xffffffffffe003e1 0x7ffffffffff800f8

def z407 : W := mkw 0x0000040188020400 0x0000010062008100 0x00080c0380060c02 0x00020300e0018300

def z408 : W := mkw 0x4bb807778f7e47c9 0x12ee01dde3df91f2 0xdbf84fff9ffecfe3 0x76fe13ffe7ffb3f8

def z409 : W := mkw 0x77efffdb78810030 0x9dfbfff6de20400c 0xffffffffff8103fd 0xffffffffffe040ff

def z410 : W := mkw 0x8401108860001034 0x210044221800040d 0x000000006000001c 0x8000000018000007

def z411 : W := mkw 0xc4fa311ea11e3145 0x313e8c47a8478c51 0x40f8301f801e3000 0x103e0c07e0078c00

def z412 : W := mkw 0x8f73b3fc63f933f4 0x23dcecff18fe4cfd 0xfff7b3fc63f933fd 0xfffdecff18fe4cff

def z413 : W := mkw 0x64fa3d1fa91e0141 0x993e8f47ea478050 0x40f83c1f801e0000 0x103e0f07e0078000

def z414 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xff0fffe07fffffff 0xffc3fff81fffffff

def z415 : W := mkw 0x0b00166dae6a578c 0x02c0059b6b9a95e3 0xfb087fffffffffff 0xfec21fffffffffff

def z416 : W := mkw 0x33dfeac053d5a800 0x0cf7fab014f56a00 0xffffffe07ffffc02 0x7ffffff81fffff00

def z417 : W := mkw 0x0010000401180140 0x0004000100460050 0x08000000039803e1 0x0200000000e600f8

def z418 : W := mkw 0xffffffff7ff9f3fc 0xffffffffdffe7cff 0xfffffffffff9f3fd 0xfffffffffffe7cff

def z419 : W := mkw 0x77ef6bd250000000 0x9dfbdaf494000000 0xe7ffff8000000000 0x79ffffe000000000

def z420 : W := mkw 0x7fff6bf6d37e03c1 0x9fffdafdb4df80f0 0xdfff83ff83fe03e1 0x77ffe0ffe0ff80f8

def z421 : W := mkw 0x0000100c20081104 0x0000040308020441 0x79087c1c607fff1f 0xde421f07181fffc7

def z422 : W := mkw 0x8010802485bb777c 0x20042009216edddf 0x0800000003ffffff 0x8200000000ffffff

def z423 : W := mkw 0xa7fef91c23ddb944 0x29ffbe4708f76e51 0xeffffc1c03fffc02 0x7bffff0700ffff00

def z424 : W := mkw 0x000004218c224608 0x0000010863089182 0x69087c639c7ffc02 0x5a421f18e71fff00

def z425 : W := mkw 0x0304c00002c18000 0x00c1300000b06000 0xef0ffc0003fffc02 0x7bc3ff0000ffff00

def z426 : W := mkw 0x8420111c20081144 0x2108044708020451 0x0000001c00000000 0x0000000700000000

def z427 : W := mkw 0x74677fdb78000000 0x9d19dff6de000000 0x3407fffffc000000 0x0d01ffffff000000

def z428 : W := mkw 0x77ffebd253d5a800 0x9dfffaf494f56a00 0x86f7838003800000 0x21bde0e000e00000

def z429 : W := mkw 0x00000024842a570c 0x00000009210a95c3 0x69087c00007fff1f 0xda421f00001fffc7

def z430 : W := mkw 0xa4fa391c211c3944 0x293e8e4708470e51 0x40f83c1c001e3c02 0x103e0f0700078f00

def z431 : W := mkw 0xa447f8886081b834 0x2911fe2218206e0d 0x2407fc006001fc1e 0x8901ff0018007f07

def z432 : W := mkw 0x0000002084224608 0x0000000821089182 0x000000000066cc02 0x000000000019b300

def z433 : W := mkw 0x8472b11c21993144 0x211cac4708664c51 0xeef7b01c03993000 0x7bbdec0700e64c00

def z434 : W := mkw 0x9477f19c7599f17c 0x651dfc671d667c5f 0xfef7f39c7f99f3fd 0xffbdfce71fe67cff

def z435 : W := mkw 0x4020035200000000 0x100800d480000000 0x100003ff80000000 0x040000ffe0000000

def z436 : W := mkw 0x080180a046e1c2b8 0x4200602811b870ae 0xbe07838063e1c3fd 0xef81e0e018f870ff

def z437 : W := mkw 0x180102c0500000b0 0x460040b01400002c 0x00000380000000e0 0x000000e000000038

def z438 : W := mkw 0x33dfe88057d5e838 0x4cf7fa2015f57a0e 0xeffffc007ffffc1e 0xfbffff001fffff07

def z439 : W := mkw 0x0421119860000000 0x0108446618000000 0x1000039c60000000 0x040000e718000000

def z440 : W := mkw 0x2bdee82483ffabc1 0x0af7ba0920ffeaf0 0xeffffc0003ffffe3 0x7bffff0000fffff8

def z441 : W := mkw 0x130542c050000000 0x04c150b014000000 0x8607838000000000 0x2181e0e000000000

def z442 : W := mkw 0x1b0542e0542042b8 0x46c150b8150810ae 0xb707c3e07c0003fd 0xedc1f0f81f0000ff

def z443 : W := mkw 0x0810802483ffabc1 0x0204200920ffeaf0 0x0800000003ffffe3 0x0200000000fffff8

def z444 : W := mkw 0x20daa80001952800 0x0836aa0000654a00 0xeeffbc00039f3c02 0x7bbfef0000e7cf00

def z445 : W := mkw 0xcbb8837683ff33f5 0x32ee20dda0ffccfd 0xdbf803ff83ff33fd 0xf6fe00ffe0ffccff

def z446 : W := mkw 0x6bfeff7fafffffcd 0x1affbfdfebfffff3 0xffffffffffffffff 0xffffffffffffffff

def z447 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xa6f7fc000381fc02 0x29bdff0000e07f00

def z448 : W := mkw 0x87fbb19c63dd3174 0x21feec6718f74c5d 0xffffb39c63ff33fd 0xffffece718ffccff

def z449 : W := mkw 0x0473319c61180140 0x011ccc6718460050 0xfef7b39c639803e1 0x7fbdece718e600f8

def z450 : W := mkw 0x23cee80002c5a800 0x08f3ba0000b16a00 0x250ffc000067fc02 0x0943ff000019ff00

def z451 : W := mkw 0x0000140928000000 0x000005024a000000 0x40083c1f80000000 0x10020f07e0000000

def z452 : W := mkw 0x0b04c02006e1c2b8 0x42c1300801b870ae 0xaf07c00003e1c3fd 0xebc1f00000f870ff

def z453 : W := mkw 0x0000142da82a0300 0x0000050b6a0a80c0 0x79087c7ffc7e0301 0x5e421f1fff1f80c0

def z454 : W := mkw 0x000004258c2a4708 0x00000109630a91c2 0x59084c7f9c7ecf03 0x5642131fe71fb3c0

def z455 : W := mkw 0x1005d4897c81d43c 0x440175225f20750f 0x2407fc007c01fc1e 0x8901ff001f007f07

def z456 : W := mkw 0xcffba3f6c3ff23f1 0x33fee8fdb0ffc8fc 0xdfff83ff83fe03e1 0x77ffe0ffe0ff80f8

def z457 : W := mkw 0x582103f6d42a43f9 0x560840fdb50a90fe 0x100003fffc0003fd 0x840000ffff0000ff

def z458 : W := mkw 0x8463b19c60893174 0x2118ec6718224c5d 0x3407b39c600133fd 0x8d01ece718004cff

def z459 : W := mkw 0x239cc80003d5a800 0x08e7320000f56a00 0x09084c0003fffc02 0x0242130000ffff00

def z460 : W := mkw 0x7fff7fffff7e57cd 0x9fffdfffffdf95f3 0xffffffffffffffff 0xffffffffffffffff

def z461 : W := mkw 0x6bbc4b76837e8bc1 0x1aef12dda0dfa2f0 0xdbf84fff83fecfe3 0x76fe13ffe0ffb3f8

def z462 : W := mkw 0x73ce6e4318000000 0x9cf39b90c6000000 0xe7fffc639c000000 0x79ffff18e7000000

def z463 : W := mkw 0x8421919c60891174 0x210864671822445d 0xbe07839c638103fd 0xef81e0e718e040ff

def z464 : W := mkw 0xe4fbbd9f69993174 0xb93eef67da664c5d 0xfeffbf9fe39933fd 0xffbfefe7f8e64cff

def z465 : W := mkw 0x8453b08c61993174 0x2114ec2318664c5d 0x2c07b000639933fd 0x8b01ec0018e64cff

def z466 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xfffffffffc7ffc02 0x7fffffffff1fff00

def z467 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0x8af0038003fe03e1 0x22bc00e000ff80f8

def z468 : W := mkw 0x1b05d2ec76e9d3bc 0x46c174bb1dba74ef 0xff07f3fc7ff9f3fd 0xffc1fcff1ffe7cff

def z469 : W := mkw 0x0b00026002600280 0x02c00098009800a0 0x0100006000600000 0x0040001800180000

def z470 : W := mkw 0x0462311820000000 0x01188c4608000000 0x40f0301c00000000 0x103c0c0700000000

def z471 : W := mkw 0x0398142daf7e570c 0x00e6050b6bdf95c3 0xfbf87c7fffffff1f 0xfefe1f1fffffffc7

def z472 : W := mkw 0x60fa2916811e2941 0x183e8a45a0478a50 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z473 : W := mkw 0x4bfaa37683ff23c1 0x12fea8dda0ffc8f0 0xffffb3ff83ff33e1 0x7fffecffe0ffccf8

def z474 : W := mkw 0x8473b1bc65b9737c 0x211cec6f196e5cdf 0xfff7f3fc7ff9f3fd 0xfffdfcff1ffe7cff

def z475 : W := mkw 0x0000140928000000 0x000005024a000000 0x20007c007c000000 0x08001f001f000000

def z476 : W := mkw 0x000004010c004408 0x0000010043001102 0x00004c001c00cc02 0x0000130007003300

def z477 : W := mkw 0x34477c897c00540c 0x8d11df225f001503 0x2407fc007c01fc1e 0x8901ff001f007f07

def z478 : W := mkw 0x0001008040000030 0x000040201000000c 0x10000380600003fd 0x840000e0180000ff

def z479 : W := mkw 0xb477fd9d79993174 0xad1dff675e664c5d 0xfef7ff9c7f9933fd 0xffbdffe71fe64cff

def z480 : W := mkw 0x0000100820001004 0x0000040208000401 0x200030006001301c 0x88000c0018004c07

def z481 : W := mkw 0xa7ffe99043d5a870 0x29fffa6410f56a1c 0xefffff8003fffce2 0x7bffffe000ffff38

def z482 : W := mkw 0x9c73b3fc75b973fc 0x671cecff1d6e5cff 0xfef7b3fc7f9933fd 0xffbdecff1fe64cff

def z483 : W := mkw 0x8c73b1bc67f9f3fc 0x631cec6f19fe7cff 0xfef7b39c63f9f3fd 0xffbdece718fe7cff

def z484 : W := mkw 0x8463319c60081174 0x2118cc671802045d 0xf6f7b39c600003fd 0xfdbdece7180000ff

def z485 : W := mkw 0x8473a19441992170 0x211ce8651066485c 0xdef7839c039803e1 0x77bde0e700e600f8

def z486 : W := mkw 0x77ffebd253d5a800 0x9dfffaf494f56a00 0xefffff8003fffc02 0x7bffffe000ffff00

def z487 : W := mkw 0x77ff7fdff91e0141 0x9dffdff7fe478050 0xf7fffffffc1e0000 0x7dffffffff078000

def z488 : W := mkw 0x60880c0308000000 0x98220300c2000000 0x00080c0380000000 0x00020300e0000000

def z489 : W := mkw 0x0020011400080140 0x0008004500020050 0x1000039c000003e1 0x040000e7000000f8

def z490 : W := mkw 0x0800002002600280 0x02000008009800a0 0x0800000003e003e1 0x0200000000f800f8

def z491 : W := mkw 0x000080000081a800 0x0000200000206a00 0x000000000001fc02 0x0000000000007f00

def z492 : W := mkw 0x03daa00003d52000 0x00f6a80000f54800 0xefffb00003ff3000 0x7bffec0000ffcc00

def z493 : W := mkw 0x8473b19861912070 0x211cec661864481c 0xf6f7b39c638000e0 0x7dbdece718e00038

def z494 : W := mkw 0x1305c08056c1c038 0x44c1702015b0700e 0xaf07c0007fe1c01c 0xebc1f0001ff87007

def z495 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xa6f7ff807c000000 0x29bdffe01f000000

def z496 : W := mkw 0x1b0542e05660c2b8 0x46c150b8159830ae 0x110043e07c60c3fd 0x844010f81f1830ff

def z497 : W := mkw 0x47eb33da60000000 0x11faccf698000000 0xf7ffb3ffe0000000 0x7dffecfff8000000

def z498 : W := mkw 0x542117db78000000 0x950845f6de000000 0x71087ffffc000000 0x5c421fffff000000

def z499 : W := mkw 0xf7ff7fdf79183144 0xbdffdff7de460c51 0xf7fffffffc183000 0x7dffffffff060c00

def z500 : W := mkw 0x4ba8037202600280 0x12ea00dc809800a0 0xdbf803ff83e003e1 0x76fe00ffe0f800f8

def z501 : W := mkw 0x0010802487ffff0c 0x0004200921ffffc3 0x0800000003ffff1f 0x8200000000ffffc7

def z502 : W := mkw 0x23dee82483ffab00 0x08f7ba0920ffeac0 0xfffffc7f83ffff03 0x7fffff1fe0ffffc0

def z503 : W := mkw 0x4bb80372837602c1 0x12ee00dca0dd80b0 0x83f803e383e600e0 0x20fe00f8e0f98038

def z504 : W := mkw 0x0800026000200280 0x02000098000800a0 0x100003e0000003e1 0x040000f8000000f8

def z505 : W := mkw 0x00000024842a4308 0x00000009210a90c2 0x7908407ffc7fc31d 0xde42101fff1ff0c7

def z506 : W := mkw 0x1305c2c05481c038 0x44c170b01520700e 0xb707c3e07c01c01c 0xedc1f0f81f007007

def z507 : W := mkw 0x9f47f2e876e1f2bc 0x67d1fcba1db87caf 0xbf07f3e07fe1f3fd 0xefc1fcf81ff87cff

def z508 : W := mkw 0x2046e8000081a800 0x0811ba0000206a00 0x6d0ffc00007ffc02 0x5b43ff00001fff00

def z509 : W := mkw 0x6bfe6b76837e03c1 0x1aff9adda0df80f0 0xffffffff83fe03e1 0x7fffffffe0ff80f8

def z510 : W := mkw 0x7bbc4f779b7e03c1 0x9eef13dde6df80f0 0xdbf84fff9ffe03e1 0x76fe13ffe7ff80f8

def z511 : W := mkw 0x0463319c60081104 0x0118cc6718020441 0xfef7b39c6019331d 0xffbdece718064cc7

def z512 : W := mkw 0x4ba8037282660281 0x12ea00dca09980a0 0xd3f803ff80660000 0x74fe00ffe0198000

def z513 : W := mkw 0x0304400002408000 0x00c1100000902000 0x010040000060c000 0x0040100000183000

def z514 : W := mkw 0x77ef6bd250000000 0x9dfbdaf494000000 0xd7ff83ff80000000 0x75ffe0ffe0000000

def z515 : W := mkw 0x23dee82487ffff0c 0x08f7ba0921ffffc3 0xeffffc0003ffff1f 0xfbffff0000ffffc7

def z516 : W := mkw 0x738d4ec358000000 0x9ce353b0d6000000 0xb70fcfe3fc000000 0x6dc3f3f8ff000000

def z517 : W := mkw 0x37dffc897bd5a800 0x8df7ff225ef56a00 0xeffffc007ffffc02 0x7bffff001fffff00

def z518 : W := mkw 0x27fff99863d5a800 0x09fffe6618f56a00 0xffffff9c63fffc02 0x7fffffe718ffff00

def z519 : W := mkw 0x00000024842a570c 0x00000009210a95c3 0x000000000000031d 0x80000000000000c7

def z520 : W := mkw 0x23ce680000000000 0x08f39a0000000000 0x86f7800000000000 0x21bde00000000000

def z521 : W := mkw 0x039cc00003d58000 0x00e7300000f56000 0xefffc00003ffc000 0x7bfff00000fff000

def z522 : W := mkw 0x180182e056e1c2b8 0x460060b815b870ae 0x180003e07fe1c3fd 0x860000f81ff870ff

def z523 : W := mkw 0x0000000004004008 0x0000000001001002 0x200040007c01c01c 0x880010001f007007

def z524 : W := mkw 0x0000140da80a1504 0x000005036a028541 0x69087c1f807ffc02 0x5a421f07e01fff00

def z525 : W := mkw 0x0000102c2428530c 0x0000040b090a14c3 0x7900707c7c79f31d 0xde401c1f1f1e7cc7

def z526 : W := mkw 0x63ee6b5200000000 0x18fb9ad480000000 0xf7ffffff80000000 0x7dffffffe0000000

def z527 : W := mkw 0x43a8035200000000 0x10ea00d480000000 0x82f0038000000000 0x20bc00e000000000

def z528 : W := mkw 0x0010000001100000 0x0004000000440000 0xcaf0000003980000 0x72bc000000e60000

def z529 : W := mkw 0x7fef7ffbfa660281 0x9ffbdffefe9980a0 0xf7fffffffc660000 0x7dffffffff198000

def z530 : W := mkw 0xdffff3fef7fff3fd 0x77fffcffbdfffcff 0xfffff3fffffff3fd 0xfffffcfffffffcff

def z531 : W := mkw 0x43a8177fac2a570c 0x10ea05dfeb0a95c3 0xfbf87ffffc7fff1f 0xfefe1fffff1fffc7

def z532 : W := mkw 0x00000004800a1504 0x0000000120028541 0x00000000001e3c02 0x0000000000078f00

def z533 : W := mkw 0x4420151b28000000 0x91080546ca000000 0x0000001f80000000 0x00000007e0000000

def z534 : W := mkw 0x000004218c224608 0x0000010863089182 0x39084c63fc67cf1f 0xce421318ff19f3c7

def z535 : W := mkw 0x3b8dcae056e5cab8 0x4ee372b815b972ae 0xbf0fcfe07fe7cfff 0xefc3f3f81ff9f3ff

def z536 : W := mkw 0x130556c978000000 0x04c155b25e000000 0xf70ffffffc000000 0x7dc3ffffff000000

def z537 : W := mkw 0x20daa80003d5a800 0x0836aa0000f56a00 0x48f83c0003fffc02 0x123e0f0000ffff00

def z538 : W := mkw 0x0000140da80a1504 0x000005036a028541 0x78083c1fe01f3f1f 0xde020f07f807cfc7

def z539 : W := mkw 0x00000024802a0300 0x00000009200a80c0 0x79087c7f807fff03 0x5e421f1fe01fffc0

def z540 : W := mkw 0x0010942dafffff0c 0x0004250b6bffffc3 0x79087c7fffffff1f 0xde421f1fffffffc7

def z541 : W := mkw 0xd473b7df79993174 0xb51cedf7de664c5d 0xfef7b3ffff9933fd 0xffbdecffffe64cff

def z542 : W := mkw 0x5bbdd7ffffffd7fd 0x56ef75fffffff5ff 0xffffffffffffffff 0xffffffffffffffff

def z543 : W := mkw 0x542103d250000000 0x950840f494000000 0x0000038000000000 0x000000e000000000

def z544 : W := mkw 0x1005d4adfcabd73c 0x4401752b7f2af5cf 0x7d0ffc7ffc7fff1f 0xdf43ff1fff1fffc7

def z545 : W := mkw 0x3bdfeac053d5a8b0 0x4ef7fab014f56a2c 0xefffff8003fffce2 0x7bffffe000ffff38

def z546 : W := mkw 0x1005c0a054a1c238 0x440170281528708e 0x3d07c0607c61c31d 0xcf41f0181f1870c7

def z547 : W := mkw 0x8777f19c63d9b174 0x21ddfc6718f66c5d 0xfff7f39c63f9f3fd 0xfffdfce718fe7cff

def z548 : W := mkw 0x0072a11401992140 0x001ca84500664850 0xfef7b39c039933e1 0x7fbdece700e64cf8

def z549 : W := mkw 0x842115bdec2a577c 0x2108456f7b0a95df 0x79087ffffc7fffff 0xde421fffff1fffff

def z550 : W := mkw 0x34477cadfc2a570c 0x8d11df2b7f0a95c3 0x7d0ffc7ffc7fff1f 0xdf43ff1fff1fffc7

def z551 : W := mkw 0x48200352000000c1 0x120800d480000030 0x00000380000000e0 0x000000e000000038

def z552 : W := mkw 0x0000800002c18000 0x0000200000b06000 0x0800000003e1c000 0x0200000000f87000

def z553 : W := mkw 0x3bdffeedffffffbc 0x4ef7ffbb7fffffef 0xffffffffffffffff 0xffffffffffffffff

def z554 : W := mkw 0xbffffbfc77fdfbfc 0x6ffffeff1dff7eff 0xfffffffc7fffffff 0xffffffff1fffffff

def z555 : W := mkw 0x738c5e6fbc2a570c 0x9ce3179bef0a95c3 0x79087c7ffc7fff1f 0xde421f1fff1fffc7

def z556 : W := mkw 0x2046e8000081a800 0x0811ba0000206a00 0x0407800000000000 0x0101e00000000000

def z557 : W := mkw 0x4820177fac2a57cd 0x120805dfeb0a95f3 0x100003fffc0003fd 0x840000ffff0000ff

def z558 : W := mkw 0x0304c02006e1c208 0x00c1300801b87082 0xbf07c0607fe1c31d 0xefc1f0181ff870c7

def z559 : W := mkw 0x0000040108000000 0x0000010042000000 0x01084c639c000000 0x00421318e7000000

def z560 : W := mkw 0x8472311c21183144 0x211c8c4708460c51 0xdaf0339c039833e1 0x76bc0ce700e60cf8

def z561 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x5908007ffc7e031d 0xd642001fff1f80c7

def z562 : W := mkw 0x5f25d7fb7ee1c2b8 0xd7c975fedfb870ae 0xbf07c3ffffe1c3fd 0xefc1f0fffff870ff

def z563 : W := mkw 0x08300134837e03c1 0x020c004d20df80f0 0xdaf0039c03fe03e1 0x76bc00e700ff80f8

def z564 : W := mkw 0x1304424010000000 0x04c1109004000000 0x010040601c000000 0x0040101807000000

def z565 : W := mkw 0x77cf7ecb78000000 0x9df3dfb2de000000 0x250ffc63fc000000 0x0943ff18ff000000

def z566 : W := mkw 0xa3dee80403ddb974 0x28f7ba0100f76e5d 0xeffffc0003ffffff 0xfbffff0000ffffff

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x20007c000001fc02 0x08001f0000007f00

def z568 : W := mkw 0xcc2113fee02a13f5 0x330844ffb80a84fd 0x100003ffe00003fd 0x840000fff80000ff

def z569 : W := mkw 0x0000102ca42a570c 0x0000040b290a95c3 0x7800301c607fff1f 0xde000c07181fffc7

def z570 : W := mkw 0x77ef7fdff80a1504 0x9dfbdff7fe028541 0xf7fffffffc1e3c02 0x7dffffffff078f00

def z571 : W := mkw 0x7fef7ffb7c2042b8 0xdffbdffedf0810ae 0xf7fffffffc0003fd 0xfdffffffff0000ff

def z572 : W := mkw 0x7ffffffffbffabc1 0x9ffffffffeffeaf0 0xffffffffffffffe3 0x7ffffffffffffff8

def z573 : W := mkw 0xa7fffdbdefffff7c 0x29ffff6f7bffffdf 0xffffffffffffffff 0xffffffffffffffff

def z574 : W := mkw 0x67fefd1b2bd5a800 0x99ffbf46caf56a00 0xeffffc1f83fffc02 0x7bffff07e0ffff00

def z575 : W := mkw 0x1b05c2c052c180b0 0x46c170b014b0602c 0xaf07c38003e1c0e0 0x6bc1f0e000f87038

def z576 : W := mkw 0xf7ef7fdf78081174 0xbdfbdff7de02045d 0xf7fffffffc0003fd 0xfdffffffff0000ff

def z577 : W := mkw 0x000014092c00540c 0x000005024b001503 0x000000007c00001c 0x800000001f000007

def z578 : W := mkw 0xa7fff99c63ddb974 0x29fffe6718f76e5d 0xfef7b39c639933fd 0xffbdece718e64cff

def z579 : W := mkw 0x0463219040000000 0x0118c86410000000 0x86f7838000000000 0x21bde0e000000000

def z580 : W := mkw 0x0356e00003d1a000 0x00d5b80000f46800 0xeff7f00003f9f000 0x7bfdfc0000fe7c00

def z581 : W := mkw 0xfffffffffbff33f5 0xbffffffffeffccfd 0xffffffffffff33fd 0xffffffffffffccff

def z582 : W := mkw 0x8010942dadbb777c 0x2004250b6b6edddf 0x79087c7fffffffff 0xde421f1fffffffff

def z583 : W := mkw 0x4388024200000000 0x10e2009080000000 0x0108006380000000 0x00420018e0000000

def z584 : W := mkw 0x77ef7ffbfc224608 0x9dfbdffeff089182 0xf7fffffffc66cc02 0x7dffffffff19b300

def z585 : W := mkw 0xc4fbb19ee19f3175 0x313eec67b867cc5d 0xfeffb39fe39f33fd 0xffbfece7f8e7ccff

def z586 : W := mkw 0x000014292c204208 0x0000050a4b081082 0x79087c7ffc61c31d 0xde421f1fff1870c7

def z587 : W := mkw 0x1401148978000000 0x850045225e000000 0x000000007c000000 0x000000001f000000

def z588 : W := mkw 0x7fef7ffff82a03c1 0x9ffbdffffe0a80f0 0xf7fffffffc0003e1 0x7dffffffff0000f8

def z589 : W := mkw 0x0000000002448800 0x0000000000912200 0x000000000066cc02 0x000000000019b300

def z590 : W := mkw 0x180116edfc2a57bc 0x460045bb7f0a95ef 0x79087ffffc7fffff 0xde421fffff1fffff

def z591 : W := mkw 0x5000064318000000 0x94000190c6000000 0x000000639c000000 0x00000018e7000000

def z592 : W := mkw 0x0000002004204208 0x0000000801081082 0x100000607c00031d 0x840000181f0000c7

def z593 : W := mkw 0x64ea3d1fa80a1504 0x993a8f47ea028541 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z594 : W := mkw 0x0000142da82a1704 0x0000050b6a0a85c1 0x59083c7f807e3f03 0x56420f1fe01f8fc0

def z595 : W := mkw 0x130556edfc2a570c 0x04c155bb7f0a95c3 0xff0ffffffc7fff1f 0xffc3ffffff1fffc7

def z596 : W := mkw 0x8431919c61993174 0x210c646718664c5d 0x1800039c639933fd 0x860000e718e64cff

def z597 : W := mkw 0xcffba3d243d520f1 0x33fee8f490f5483c 0x86f78380038000e0 0x21bde0e000e00038

def z598 : W := mkw 0x8443b4adecab773c 0x2110ed2b7b2addcf 0x7d0ffc7ffc7fff1f 0xdf43ff1fff1fffc7

def z599 : W := mkw 0x3bdfeae057f5eab8 0x4ef7fab815fd7aae 0xbff7c3e07fe1c3fd 0xeffdf0f81ff870ff

def z600 : W := mkw 0x43a80376802a0300 0x10ea00dda00a80c0 0xdbf803ff807e0301 0x76fe00ffe01f80c0

def z601 : W := mkw 0x176773d870000000 0x05d9dcf61c000000 0xf7f7f3fc7c000000 0x7dfdfcff1f000000

def z602 : W := mkw 0x0000140928000000 0x000005024a000000 0x79087c7ffc7ffc02 0x5e421f1fff1fff00

def z603 : W := mkw 0x0020011000000000 0x0008004400000000 0xd2f0039c00000000 0x74bc00e700000000

def z604 : W := mkw 0x0b00026006604288 0x02c00098019810a2 0xbb0043e07fe1c3fd 0xeec010f81ff870ff

def z605 : W := mkw 0x6bfeeb5203d5a8c1 0x1affbad480f56a30 0x86f78380038000e0 0x21bde0e000e00038

def z606 : W := mkw 0x2004480000008800 0x0801120000002200 0x00004c000000cc02 0x0000130000003300

def z607 : W := mkw 0x4bb8837683ffabc1 0x12ee20dda0ffeaf0 0xdbf803ff83ffffe3 0x76fe00ffe0fffff8

def z608 : W := mkw 0xa4fbb99c619d3974 0x293eee6718674e5d 0xfeffbf9c639f3fff 0xffbfefe718e7cfff

def z609 : W := mkw 0x8473319c61183174 0x211ccc6718460c5d 0x50f0339c601833fd 0x943c0ce718060cff

def z610 : W := mkw 0x0388000002440000 0x00e2000000910000 0x0108000000660000 0x0042000000198000

def z611 : W := mkw 0x1b15c2e057f5eab8 0x46c570b815fd7aae 0xbf07c3e07fffffff 0xefc1f0f81fffffff

def z612 : W := mkw 0x0000140d2c08550c 0x000005034b021543 0x78007c1c7c19ff1f 0xde001f071f067fc7

def z613 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0x8e07838003e1c3fd 0xa381e0e000f870ff

def z614 : W := mkw 0xf7ffffdf7bddb974 0xbdfffff7def76e5d 0xffffffffffffffff 0xffffffffffffffff

def z615 : W := mkw 0x1b0542e052600280 0x06c150b8149800a0 0xbf07c3e07fe003e1 0x6fc1f0f81ff800f8

def z616 : W := mkw 0x0000140928001404 0x000005024a000501 0x00003c0000003c02 0x00000f0000000f00

def z617 : W := mkw 0xf7fffffffdbb777c 0xbdffffffff6edddf 0xffffffffffffffff 0xffffffffffffffff

def z618 : W := mkw 0x48200376802a03c1 0x120800dda00a80f0 0x590803ff807e03e1 0x564200ffe01f80f8

def z619 : W := mkw 0x8421119c60081174 0x210844671802045d 0x7800339c601933fd 0xde000ce718064cff

def z620 : W := mkw 0x8431119c61181174 0x210c44671846045d 0xdaf0039c639803fd 0xf6bc00e718e600ff

def z621 : W := mkw 0x238c480000000000 0x08e3120000000000 0x01084c0000000000 0x0042130000000000

def z622 : W := mkw 0x0001908c60891134 0x000064231822444d 0xfe07b39c639933fd 0xff81ece718e64cff

def z623 : W := mkw 0xf7fffbde71993174 0xbdfffef79c664c5d 0xfef7b39c639933fd 0xffbdece718e64cff

def z624 : W := mkw 0x40b8153fad3e574d 0x102e054feb4f95d3 0x79f87c7ffc7fff1f 0xde7e1f1fff1fffc7

def z625 : W := mkw 0x23ce7c2dac2a570c 0x08f39f0b6b0a95c3 0xfffffc7ffc7fff1f 0xffffff1fff1fffc7

def z626 : W := mkw 0x7b8dcee35ee1c2b8 0xdee373b8d7b870ae 0xbf0fcfe3ffe1c3fd 0xefc3f3f8fff870ff

def z627 : W := mkw 0x6bdeea6283f7aa81 0x1af7ba98a0fdeaa0 0xeffffc6383fffc02 0x7bffff18e0ffff00

def z628 : W := mkw 0x5c2117fb7c2042b8 0xd70845fedf0810ae 0x100003fffc0003fd 0x840000ffff0000ff

def z629 : W := mkw 0x9f77e3f057f1e2f8 0x67ddf8fc15fc78be 0xbff7c3e07fe1c3fd 0xeffdf0f81ff870ff

def z630 : W := mkw 0x5fb917fffb7e03c1 0x97ee45fffedf80f0 0xdbf803fffffe03e1 0x76fe00ffffff80f8

def z631 : W := mkw 0x1b05c2e4d6ebd7bc 0x46c170b935baf5ef 0xbf07c3e07fffffff 0xefc1f0f81fffffff

def z632 : W := mkw 0x8010000401183144 0x2004000100460c51 0x0000000000183000 0x0000000000060c00

def z633 : W := mkw 0x77efffdb7881a800 0x9dfbfff6de206a00 0xf7fffffffc01fc02 0x7dffffffff007f00

def z634 : W := mkw 0x0b04c26002e18280 0x02c1309800b860a0 0xbf07c3e003e1c3e1 0x6fc1f0f800f870f8

def z635 : W := mkw 0x00000024842a570c 0x00000009210a95c3 0x5908007f807fff1f 0xd642001fe01fffc7

def z636 : W := mkw 0x0000102ca02a1304 0x0000040b280a84c1 0x7908307fe07f331d 0xde420c1ff81fccc7

def z637 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xc6ffbc00039e3c02 0x31bfef0000e78f00

def z638 : W := mkw 0x4bb8177fab7e03c1 0x12ee05dfeadf80f0 0xfbf87ffffffe03e1 0x7efe1fffffff80f8

def z639 : W := mkw 0x5badc3f256e1c2b8 0x56eb70fc95b870ae 0xffffc3ffffe1c3fd 0xfffff0fffff870ff

def z640 : W := mkw 0x23defc0dabdfbd04 0x08f7bf036af7ef41 0xeffffc1f83fffc02 0x7bffff07e0ffff00

def z641 : W := mkw 0x64fa3d1b29142800 0x993e8f46ca450a00 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z642 : W := mkw 0x8010900c21993174 0x2004240308664c5d 0x7800301c639933fd 0xde000c0718e64cff

def z643 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0x41f8007f807e0000 0x107e001fe01f8000

def z644 : W := mkw 0x4ba80376802a03c1 0x12ea00dda00a80f0 0xd3f803ff800003e1 0x74fe00ffe00000f8

def z645 : W := mkw 0x0443308860000000 0x0110cc2218000000 0x2407b00060000000 0x0901ec0018000000

def z646 : W := mkw 0x738c5e4b38000000 0x9ce31792ce000000 0x71087c7ffc000000 0x5c421f1fff000000

def z647 : W := mkw 0x77efffdb7ac18000 0x9dfbfff6deb06000 0xffffffffffe1c000 0x7ffffffffff87000

def z648 : W := mkw 0x57a917db78000000 0x95ea45f6de000000 0xd3f803fffc000000 0x74fe00ffff000000

def z649 : W := mkw 0x4b8806638e664689 0x12e20198e39991a2 0x01084c639c66cc02 0x00421318e719b300

def z650 : W := mkw 0x4bb983f6c3ff03f1 0x12ee60fdb0ffc0fc 0xffff83ffe3ff03fd 0xffffe0fff8ffc0ff

def z651 : W := mkw 0x2046fc2dacabff0c 0x0811bf0b6b2affc3 0x7d0ffc7ffc7fff1f 0xdf43ff1fff1fffc7

def z652 : W := mkw 0x4b200376826a03c1 0x12c800dda09a80f0 0x9b0003ff83e003e1 0x66c000ffe0f800f8

def z653 : W := mkw 0x1b04424012408080 0x46c1109004902020 0x0000000000000000 0x0000000000000000

def z654 : W := mkw 0x000000000400540c 0x0000000001001503 0x000000000001fc1e 0x8000000000007f07

def z655 : W := mkw 0x00000024842a570c 0x00000009210a95c3 0x390040607c7fff1f 0xce4010181f1fffc7

def z656 : W := mkw 0x8443b08c60893134 0x2110ec2318224c4d 0x7c07b01c6019331d 0xdf01ec0718064cc7

def z657 : W := mkw 0xa7dff88863d5b834 0x29f7fe2218f56e0d 0xeffffc0063fffc1e 0xfbffff0018ffff07

def z658 : W := mkw 0x23fee91403dda940 0x08ffba4500f76a50 0xffffff9c03ffffe3 0x7fffffe700fffff8

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800300000193000 0x5a000c0000064c00

def z660 : W := mkw 0x1305c2c052c18000 0x04c170b014b06000 0xbf07c3e07fe1c000 0x6fc1f0f81ff87000

def z661 : W := mkw 0x8473b1bce5bb777c 0x211cec6f396edddf 0xfef7b39c63ffffff 0xffbdece718ffffff

def z662 : W := mkw 0x40200116800a0141 0x10080045a0028050 0x0000001f80000000 0x00000007e0000000

def z663 : W := mkw 0x8011808441993174 0x2004602110664c5d 0xbe078380639933fd 0xef81e0e018e64cff

def z664 : W := mkw 0x8810802407f9f3fc 0x6204200901fe7cff 0x0800000003f9f3fd 0x8200000000fe7cff

def z665 : W := mkw 0x43a8175b28000000 0x10ea05d6ca000000 0xf3f87ffffc000000 0x7cfe1fffff000000

def z666 : W := mkw 0x8472b11c21993174 0x211cac4708664c5d 0x48f0301c039933fd 0x923c0c0700e64cff

def z667 : W := mkw 0x0001808040810030 0x000060201020400c 0x86078380038000e0 0x2181e0e000e00038

def z668 : W := mkw 0x8472353dad3a774c 0x211c8d4f6b4e9dd3 0x79f87c7ffc7fff1f 0xde7e1f1fff1fffc7

def z669 : W := mkw 0x2056e8000191a800 0x0815ba0000646a00 0xeef7fc000399fc02 0x7bbdff0000e67f00

def z670 : W := mkw 0x0000140d28081104 0x000005034a020441 0x79087c7ffc19331d 0xde421f1fff064cc7

def z671 : W := mkw 0x0000140928000000 0x000005024a000000 0x1000007ffc000000 0x0400001fff000000

def z672 : W := mkw 0x6bfeeb5203d5a8c1 0x1affbad480f56a30 0xefffff8003fffce2 0x7bffffe000ffff38

def z673 : W := mkw 0x5bbdc3d253d580f1 0x56ef70f494f5603c 0x86f78380038000e0 0x21bde0e000e00038

def z674 : W := mkw 0x0000100c20081104 0x0000040308020441 0x1000001c6000031d 0x84000007180000c7

def z675 : W := mkw 0x238c4c218e66ce08 0x08e313086399b382 0x01084c639c66cc02 0x00421318e719b300

def z676 : W := mkw 0x000004218c224608 0x0000010863089182 0x000000639c000000 0x00000018e7000000

def z677 : W := mkw 0x1b05c2c056c1c0b8 0x46c170b015b0702e 0xa607c3807f81c0fc 0xa981f0e01fe0703f

def z678 : W := mkw 0x34477c8978000000 0x8d11df225e000000 0x750ffc7ffc000000 0x5d43ff1fff000000

def z679 : W := mkw 0xa477f99c6199b974 0x291dfe6718666e5d 0xfef7ff9c6399ffff 0xffbdffe718e67fff

def z680 : W := mkw 0x738c4a4210000000 0x9ce3129084000000 0x0000000000000000 0x0000000000000000

def z681 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0x8707c3e01fe0c0e0 0x21c1f0f807f83038

def z682 : W := mkw 0x20ca280000000000 0x08328a0000000000 0x40f83c0000000000 0x103e0f0000000000

def z683 : W := mkw 0x4bb8177faf7e57cd 0x12ee05dfebdf95f3 0xdbf803fffffe03fd 0xf6fe00ffffff80ff

def z684 : W := mkw 0x6b8c4a6282668a81 0x1ae31298a099a2a0 0x01084c638066cc02 0x00421318e019b300

def z685 : W := mkw 0x23dee80001912000 0x08f7ba0000644800 0xeffffc0003993000 0x7bffff0000e64c00

def z686 : W := mkw 0x0398000003540000 0x00e6000000d50000 0xebf87c0003fffc02 0x7afe1f0000ffff00

def z687 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0x87ffcc0003e6cc02 0x21fff30000f9b300

def z688 : W := mkw 0x74ef7d9b78000000 0x9d3bdf66de000000 0x64fffc1ffc000000 0x193fff07ff000000

def z689 : W := mkw 0x77ef7fdb7c00540c 0x9dfbdff6df001503 0xf7fffffffc01fc1e 0xfdffffffff007f07

def z690 : W := mkw 0x0000800000810030 0x000020000020400c 0x08000000038103fd 0x8200000000e040ff

def z691 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x30007c7ffc01ff1f 0x8c001f1fff007fc7

def z692 : W := mkw 0x8473b19861913074 0x211cec6618644c1d 0xa6f7b380638130fc 0xa9bdece018e04c3f

def z693 : W := mkw 0x4b98026283760281 0x12e60098a0dd80a0 0xcbf8006383fe0000 0x72fe0018e0ff8000

def z694 : W := mkw 0x3447688050000000 0x8d11da2014000000 0x0407800000000000 0x0101e00000000000

def z695 : W := mkw 0x67ee7d1b28000000 0x99fb9f46ca000000 0xe7fffc1f80000000 0x79ffff07e0000000

def z696 : W := mkw 0x0b100264837e03c1 0x02c4009920df80f0 0x9b0003e003fe03e1 0x66c000f800ff80f8

def z697 : W := mkw 0x23cee8000081a800 0x08f3ba0000206a00 0xe7fffc000001fc02 0x79ffff0000007f00

def z698 : W := mkw 0x23deec218ff7ee08 0x08f7bb0863fdfb82 0xeffffc639ffffc02 0x7bffff18e7ffff00

def z699 : W := mkw 0x9f77e3d053d1a0f0 0x67ddf8f414f4683c 0x86f78380038000e0 0x21bde0e000e00038

def z700 : W := mkw 0xcc73b3fee1bb33f5 0x331cecffb86eccfd 0xfef7b3ffe39933fd 0xffbdecfff8e64cff

def z701 : W := mkw 0x20da280001142800 0x08368a0000450a00 0x69f87c00007ffc02 0x5a7e1f00001fff00

def z702 : W := mkw 0x3bdfeac053d5a8b0 0x4ef7fab014f56a2c 0x86f78380038000e0 0x21bde0e000e00038

def z703 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x48083c1f807fff1f 0x92020f07e01fffc7

def z704 : W := mkw 0x046335bdec2a570c 0x0118cd6f7b0a95c3 0xfffffffffc7fff1f 0xffffffffff1fffc7

def z705 : W := mkw 0x1b04c26016e1c2b8 0x46c1309805b870ae 0x090040601fe1c3fd 0x8240101807f870ff

def z706 : W := mkw 0x00001429ac224608 0x0000050a6b089182 0x71087c7ffc66cc02 0x5c421f1fff19b300

def z707 : W := mkw 0x63deea4203d5a800 0x18f7ba9080f56a00 0xeffffc6383fffc02 0x7bffff18e0ffff00

def z708 : W := mkw 0x000180a044a14238 0x000060281128508e 0xbe0783e07f8103fd 0xef81e0f81fe040ff

def z709 : W := mkw 0xa473b99c61993974 0x291cee6718664e5d 0xfef7bf9c63993fff 0xffbdefe718e64fff

def z710 : W := mkw 0x8431919c61991174 0x210c64671866445d 0xfef7839c639903fd 0xffbde0e718e640ff

def z711 : W := mkw 0xa473bd9d69993174 0xa91cef675a664c5d 0xfef7bf9c639933fd 0xffbdefe718e64cff

def z712 : W := mkw 0x9f76737c3778f3cc 0x67dd9cdf0dde3cf3 0x41f0707c1c78f000 0x107c1c1f071e3c00

def z713 : W := mkw 0x8473a19441992170 0x211ce8651066485c 0xfef7839c639903fd 0xffbde0e718e640ff

def z714 : W := mkw 0xa7ad599c624c9974 0x29eb56671893265d 0x11084f9c6066cfff 0x844213e71819b3ff

def z715 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xf7fffffffc01fc02 0x7dffffffff007f00

def z716 : W := mkw 0x8473a19441993174 0x211ce86510664c5d 0xeef7b380039933fd 0xfbbdece000e64cff

def z717 : W := mkw 0x3b05cae056e1cab8 0x4ec172b815b872ae 0xbf07cfe07fe1cfff 0xefc1f3f81ff873ff

def z718 : W := mkw 0x43a8035200000000 0x10ea00d480000000 0xdbf803ff838003e1 0x76fe00ffe0e000f8

def z719 : W := mkw 0xb447fc897c81f03c 0xed11ff225f207c0f 0x2407fc007c01f01c 0x8901ff001f007c07

def z720 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xc7fffc0003fefc02 0x31ffff0000ffbf00

def z721 : W := mkw 0x6bbc4b76837e8bc1 0x1aef12dda0dfa2f0 0xfbf87fff83ffffe3 0x7efe1fffe0fffff8

def z722 : W := mkw 0x4bbc4376837e83c1 0x12ef10dda0dfa0f0 0xdbf843ff83fec3e1 0x76fe10ffe0ffb0f8

def z723 : W := mkw 0x8453b08861913034 0x2114ec2218644c0d 0xfef7b380639933fd 0xffbdece018e64cff

def z724 : W := mkw 0x8443b48968813434 0x2110ed225a204d0d 0x2407bc0060013c1e 0x8901ef0018004f07

def z725 : W := mkw 0x1b05c2e056e5cab8 0x46c170b815b972ae 0xbf07c3e07fe7cfff 0xefc1f0f81ff9f3ff

def z726 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xf6f7b39c638003fd 0xfdbdece718e000ff

def z727 : W := mkw 0x4bb80376837e13c5 0x12ee00dda0df84f1 0xdbf803ff83ff33fd 0xf6fe00ffe0ffccff

def z728 : W := mkw 0x3b8c4a601660c288 0x4ee31298059830a2 0x01084c601c60c000 0x0042131807183000

def z729 : W := mkw 0xb447fc897881b834 0xad11ff225e206e0d 0x2407fc007c01fc1e 0x8901ff001f007f07

def z730 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xfbf843ff83ffc3e1 0x7efe10ffe0fff0f8

def z731 : W := mkw 0x0810802487ffffbc 0x4204200921ffffef 0x0800000003ffffff 0x8200000000ffffff

def z732 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xdbf803ff83ffffe3 0x76fe00ffe0fffff8

def z733 : W := mkw 0x7b8dcae2d6e7cab9 0x5ee372b8b5b9f2ae 0xbf0fcfe3ffe7cfff 0xefc3f3f8fff9f3ff

def z734 : W := mkw 0x77ef6bf6d42a570c 0x9dfbdafdb50a95c3 0x8ef78380007fff1f 0xa3bde0e0001fffc7

def z735 : W := mkw 0x5c2117fffc2a57cd 0x970845ffff0a95f3 0x100003fffc0003fd 0x840000ffff0000ff

def z736 : W := mkw 0x03daa00003d52000 0x00f6a80000f54800 0xeffffc0003fffc02 0x7bffff0000ffff00

def z737 : W := mkw 0x1001808054814038 0x440060201520500e 0xbe0783807f8103fd 0xef81e0e01fe040ff

def z738 : W := mkw 0x77ef7fdb78008800 0x9dfbdff6de002200 0xf7fffffffc00cc02 0x7dffffffff003300

def z739 : W := mkw 0x48300376837e03c1 0x120c00dda0df80f0 0xdaf003ff83fe03e1 0x76bc00ffe0ff80f8

def z740 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xd6ffbffffc000000 0x35bfefffff000000

def z741 : W := mkw 0x64eb3d9b68000000 0x993acf66da000000 0xf7fffffffc000000 0x7dffffffff000000

def z742 : W := mkw 0x6bb80b76837e0bc1 0x1aee02dda0df82f0 0xdbf80fff83fe0fe3 0x76fe03ffe0ff83f8

def z743 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xfffffffffc7e0000 0x7fffffffff1f8000

def z744 : W := mkw 0x0053b08c61993134 0x0014ec2318664c4d 0xfef7b39c639933fd 0xffbdece718e64cff

def z745 : W := mkw 0x7fef7fdb7a440081 0x9ffbdff6de910020 0xf7fffffffc000000 0x7dffffffff000000

def z746 : W := mkw 0x0042340928000000 0x00108d024a000000 0xf7fffc7ffc000000 0x7dffff1fff000000

def z747 : W := mkw 0x73ad4fd358000000 0x9ceb53f4d6000000 0xf7ffcffffc000000 0x7dfff3ffff000000

def z748 : W := mkw 0x8473a5b1cdb36678 0x211ce96c736cd99e 0x87ffcfe39fe6cce2 0x21fff3f8e7f9b338

def z749 : W := mkw 0x4bb80376877e43c9 0x12ee00dda1df90f2 0xdbf803ff83ffc3fd 0xf6fe00ffe0fff0ff

def z750 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0x9bf003ff83e003e1 0x66fc00ffe0f800f8

def z751 : W := mkw 0x77ef7fdb78001004 0x9dfbdff6de000401 0xf7fffffffc01301c 0xfdffffffff004c07

def z752 : W := mkw 0x73ef6bd250000000 0x1cfbdaf494000000 0xf7fffffffc000000 0x7dffffffff000000

def z753 : W := mkw 0xcfcbb2eae2e732b5 0x33f2ecbab8b9ccad 0x250fb063e067301c 0x8943ec18f819cc07

def z754 : W := mkw 0x0010802485bb770c 0x00042009216eddc3 0x0800000003ffff1f 0x8200000000ffffc7

def z755 : W := mkw 0x6bbc4b76837e8bc1 0x1aef12dda0dfa2f0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z756 : W := mkw 0x8473b59de99b3574 0x211ced677a66cd5d 0xffffffffff9f3fff 0xffffffffffe7cfff

def z757 : W := mkw 0x77ef6bd250000000 0x9dfbdaf494000000 0xf7ffc3fffc000000 0x7dfff0ffff000000

def z758 : W := mkw 0x40b80116811e0141 0x102e0045a0478050 0xc2f8039f839e00e0 0x30be00e7e0e78038

def z759 : W := mkw 0x2bdee80003d5a8c1 0x0af7ba0000f56a30 0xeffffc0003fffce2 0x7bffff0000ffff38

def z760 : W := mkw 0x8472351d29183544 0x211c8d474a460d51 0x40f03c1c00183c02 0x103c0f0700060f00

def z761 : W := mkw 0x4bb80376837e8bc1 0x12ee00dda0dfa2f0 0xdbf803ff83fecfe3 0x76fe00ffe0ffb3f8

def z762 : W := mkw 0x48300376813a03c1 0x120c00dda04e80f0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z763 : W := mkw 0x2bdee80003d5a8b0 0x4af7ba0000f56a2c 0xeffffc0003fffce2 0x7bffff0000ffff38

def z764 : W := mkw 0x546337db78000000 0x9518cdf6de000000 0xf7fffffffc000000 0x7dffffffff000000

def z765 : W := mkw 0x23de680003540000 0x08f79a0000d50000 0xeffffc0003fffc02 0x7bffff0000ffff00

def z766 : W := mkw 0x0030011401180140 0x000c004500460050 0xdbf803ff839803e1 0x76fe00ffe0e600f8

def z767 : W := mkw 0x43b8035201100040 0x10ee00d480440010 0xd3f803ff838000e0 0x74fe00ffe0e00038

def z768 : W := mkw 0x8473b59de99b3574 0x211ced677a66cd5d 0xffffff9fe3ffffff 0xffffffe7f8ffffff

def z769 : W := mkw 0x7fef7fdb7a400080 0x9ffbdff6de900020 0xf7ffffffff8000e0 0x7dffffffffe00038

def z770 : W := mkw 0xf7ef7fdb78003004 0xbdfbdff6de000c01 0xf7fffffffc003000 0x7dffffffff000c00

def z771 : W := mkw 0x3c577cadfb7e03c1 0x8f15df2b7edf80f0 0x2c07fc007ffe03e1 0x0b01ff001fff80f8

def z772 : W := mkw 0x4bb80372037402c1 0x12ee00dc80dd00b0 0xdbf803ff83e003e1 0x76fe00ffe0f800f8

def z773 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xaef7fc0003fffc02 0x2bbdff0000ffff00

def z774 : W := mkw 0x1b05d6cdfacb95b4 0x46c175b37eb2e56d 0xc60fbf9f839e3ce2 0x3183efe7e0e78f38

def z775 : W := mkw 0xa4fa3d1da91e3d44 0x293e8f476a478f51 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z776 : W := mkw 0x0b04c26006e1c288 0x02c1309801b870a2 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z777 : W := mkw 0x1005c0a054a1c238 0x440170281528708e 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z778 : W := mkw 0x8443b48968813034 0x2110ed225a204c0d 0x2407fc007c01301c 0x8901ff001f004c07

def z779 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xfff7f3fc7f9933fd 0xfffdfcff1fe64cff

def z780 : W := mkw 0x0810802487ffffcd 0x0204200921fffff3 0x0800000003ffffff 0x8200000000ffffff

def z781 : W := mkw 0x8473b59d69993174 0x211ced675a664c5d 0xfeffbf9fe39933fd 0xffbfefe7f8e64cff

def z782 : W := mkw 0x00300114811a0140 0x000c004520468050 0xdaf8039f839e03e1 0x76be00e7e0e780f8

def z783 : W := mkw 0x23defc2dafffff0c 0x08f7bf0b6bffffc3 0x96f7807fff80031d 0xa5bde01fffe000c7

def z784 : W := mkw 0x0052a00003d5a800 0x0014a80000f56a00 0xeffffc0003fffc02 0x7bffff0000ffff00

def z785 : W := mkw 0x77ee7f5b38000000 0x9dfb9fd6ce000000 0xe7fffc7f9c000000 0x79ffff1fe7000000

def z786 : W := mkw 0x6866eb7680ababc1 0x1a19badda02aeaf0 0x3407ffff8001ffe3 0x0d01ffffe0007ff8

def z787 : W := mkw 0xe4fa3d1fa91e3145 0xb93e8f47ea478c51 0x40f83c1f801e3000 0x103e0f07e0078c00

def z788 : W := mkw 0x8473a19041912070 0x211ce8641064481c 0xfef7b380639933fd 0xffbdece018e64cff

def z789 : W := mkw 0xe4fa3d1fa91a3544 0xb93e8f47ea468d51 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z790 : W := mkw 0x0011808041910030 0x000460201064400c 0xfef78380639903fd 0xffbde0e018e640ff

def z791 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xfff7f39c63f9f3fd 0xfffdfce718fe7cff

def z792 : W := mkw 0x0000140d28081104 0x000005034a020441 0x79087c7ffc7fff1f 0xde421f1fff1fffc7

def z793 : W := mkw 0x0031919c61991174 0x000c64671866445d 0xfef7b39c639933fd 0xffbdece718e64cff

def z794 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0x61087c7ffc7ffc1e 0x98421f1fff1fff07

def z795 : W := mkw 0x1305c2c05481c038 0x44c170b01520700e 0xbf07c3e07f81c3fd 0xefc1f0f81fe070ff

def z796 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0x9af003ff83fe03e1 0x26bc00ffe0ff80f8

def z797 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0x9ef7839c639933fd 0xa7bde0e718e64cff

def z798 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xfffffffffc193000 0x7fffffffff064c00

def z799 : W := mkw 0x47eb37db68000000 0x11facdf6da000000 0xf7fffffffc000000 0x7dffffffff000000

def z800 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xffffff8003ffffe3 0x7fffffe000fffff8

def z801 : W := mkw 0xf39cce4719993174 0xbce73391c6664c5d 0x09084c639f9933fd 0x82421318e7e64cff

def z802 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xfffffc607ffffc02 0x7fffff181fffff00

def z803 : W := mkw 0x7bbc4b76977ecbc9 0x5eef12dda5dfb2f2 0xdbf84fff9ffecfe3 0x76fe13ffe7ffb3f8

def z804 : W := mkw 0x23de680001142800 0x08f79a0000450a00 0xeffffc00007ffc02 0x7bffff00001fff00

def z805 : W := mkw 0x8473319c61181174 0x211ccc671846045d 0xfef7b39c639803fd 0xffbdece718e600ff

def z806 : W := mkw 0x74ef7fdb78000000 0x9d3bdff6de000000 0x74fffffffc000000 0x1d3fffffff000000

def z807 : W := mkw 0x43b80356811e0141 0x10ee00d5a0478050 0xdbf803ff839e03e1 0x76fe00ffe0e780f8

def z808 : W := mkw 0x5b8c46639e66c689 0x56e31198e799b1a2 0x01084c639c66cc02 0x00421318e719b300

def z809 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0x97ffcffffc000000 0x25fff3ffff000000

def z810 : W := mkw 0x1805c2e056e1c2b8 0x460170b815b870ae 0x3c07c3e07fe1c3fd 0x8f01f0f81ff870ff

def z811 : W := mkw 0x8810802487fff3fd 0x6204200921fffcff 0x0800000003fff3fd 0x8200000000fffcff

def z812 : W := mkw 0x23ce680002448800 0x08f39a0000912200 0xeffffc00007ffc02 0x7bffff00001fff00

def z813 : W := mkw 0x77ef7fdb7a448800 0x9dfbdff6de912200 0xfffffffffc7ffc02 0x7fffffffff1fff00

def z814 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xfbf803ffe3ff03fd 0xfefe00fff8ffc0ff

def z815 : W := mkw 0x8810802487fbf7fc 0x6204200921fefdff 0x0800000003ffffff 0x8200000000ffffff

def z816 : W := mkw 0x3bdeea4013d5a880 0x4ef7ba9004f56a20 0xeffffc0003fffc02 0x7bffff0000ffff00

def z817 : W := mkw 0x4bb80376877e43c9 0x12ee00dda1df90f2 0xdbf843ff9ffec3e1 0x76fe10ffe7ffb0f8

def z818 : W := mkw 0x50bdc196d59fc179 0x542f7065b567f05e 0x64ffc01ffc1fc01c 0x993ff007ff07f007

def z819 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0x9707c3e07fe0c3fd 0xa5c1f0f81ff830ff

def z820 : W := mkw 0xc473b19ee19b3175 0x311cec67b866cc5d 0xfef7b39fe39933fd 0xffbdece7f8e64cff

def z821 : W := mkw 0x0072b11c21993144 0x001cac4708664c51 0xfef7b39c639933fd 0xffbdece718e64cff

def z822 : W := mkw 0x38db2ae055346ab8 0x4e36cab8154d1aae 0x50f83fe07c1e3fff 0x943e0ff81f078fff

def z823 : W := mkw 0x8473b19861912070 0x211cec661864481c 0xfef7b39c638103fd 0xffbdece718e040ff

def z824 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xd3f803ff838003e1 0x74fe00ffe0e000f8

def z825 : W := mkw 0x73ee6f5318000000 0x9cfb9bd4c6000000 0xf7ffffff9c000000 0x7dffffffe7000000

def z826 : W := mkw 0x180182e056e1c2b8 0x460060b815b870ae 0xbe0783e07fe1c3fd 0xef81e0f81ff870ff

def z827 : W := mkw 0xb447fc897c81743c 0xad11ff225f205d0f 0x2407fc007c01fc1e 0x8901ff001f007f07

def z828 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xbf0fcfe07fe7cfff 0xefc3f3f81ff9f3ff

def z829 : W := mkw 0xcbb80376837e33c5 0x32ee00dda0df8cf1 0xdbf803ff83fe33e1 0x76fe00ffe0ff8cf8

def z830 : W := mkw 0x7b8c4e639e62c688 0xdee31398e798b1a2 0x01084c639c66cc02 0x00421318e719b300

def z831 : W := mkw 0x77ef7fdb78001404 0x9dfbdff6de000501 0xf7fffffffc003c02 0x7dffffffff000f00

def z832 : W := mkw 0x40300116811a0141 0x100c0045a0468050 0xdaf0039f839803e1 0x76bc00e7e0e600f8

def z833 : W := mkw 0x8443b4896c81743c 0x2110ed225b205d0f 0x2407b0007c01301c 0x8901ec001f004c07

def z834 : W := mkw 0x4bb8175b2f5454cd 0x12ee05d6cbd51533 0xa2f07f807f81fcfe 0xa8bc1fe01fe07f3f

def z835 : W := mkw 0x1b05c2e052e102b0 0x06c170b814b840ac 0xbf07c3e07fe103fd 0xefc1f0f81ff840ff

def z836 : W := mkw 0x8010802485bb777c 0x20042009216edddf 0x08000000039933fd 0x8200000000e64cff

def z837 : W := mkw 0xcc2117ffec2a57fd 0x330845fffb0a95ff 0x100003fffc0003fd 0x840000ffff0000ff

def z838 : W := mkw 0x73ce7e4b38000000 0x9cf39f92ce000000 0xf7fffc7ffc000000 0x7dffff1fff000000

def z839 : W := mkw 0x3b8c4a601664ca88 0x4ee31298059932a2 0x010040601c60c000 0x0040101807183000

def z840 : W := mkw 0x3447fc897c81e838 0xcd11ff225f207a0e 0x2407fc007c01fc1e 0x8901ff001f007f07

def z841 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xd7ff83fffc000000 0x75ffe0ffff000000

def z842 : W := mkw 0x48b80376813e03c1 0x122e00dda04f80f0 0xdaf803ff839e03e1 0x76be00ffe0e780f8

def z843 : W := mkw 0x0001808040810030 0x000060201020400c 0xbf07c3e07f8103fd 0xefc1f0f81fe040ff

def z844 : W := mkw 0x0000142dac2a570c 0x0000050b6b0a95c3 0xfb087fffffffffff 0xfec21fffffffffff

def z845 : W := mkw 0x53ad57db78000000 0x14eb55f6de000000 0xf7fffffffc000000 0x7dffffffff000000

def z846 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xb6f7b39c638133fd 0xadbdece718e04cff

def z847 : W := mkw 0x8010802487ffff7c 0x2004200921ffffdf 0x0800000003ffffff 0x8200000000ffffff

def z848 : W := mkw 0x2056e80003d5a800 0x0815ba0000f56a00 0xeef7fc0003fffc02 0x7bbdff0000ffff00

def z849 : W := mkw 0x5b8dc2e256e5c2b9 0x56e370b895b970ae 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z850 : W := mkw 0x7b8dcae256e1c2b8 0xdee372b895b870ae 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z851 : W := mkw 0x1b0542e0566042b8 0x46c150b8159810ae 0xbf07c3e07fe003fd 0xefc1f0f81ff800ff

def z852 : W := mkw 0x0b300374837a03c0 0x02cc00dd20de80f0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z853 : W := mkw 0x8473b59d69993174 0x211ced675a664c5d 0xfef7b3ffff9933fd 0xffbdecffffe64cff

def z854 : W := mkw 0x74eb3fdb78000000 0x9d3acff6de000000 0xf6ffbffffc000000 0x7dbfefffff000000

def z855 : W := mkw 0x57ad57db78000000 0x95eb55f6de000000 0xf7ffc3fffc000000 0x7dfff0ffff000000

def z856 : W := mkw 0x4ba80376826a0380 0x12ea00dda09a80e0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z857 : W := mkw 0x4bb80372837602c1 0x12ee00dca0dd80b0 0xd3f803ff83e600e0 0x74fe00ffe0f98038

def z858 : W := mkw 0x57ef73da70000000 0x15fbdcf69c000000 0xf7fff3fffc000000 0x7dfffcffff000000

def z859 : W := mkw 0x0042200000000000 0x0010880000000000 0xeffffc00007ffc02 0x7bffff00001fff00

def z860 : W := mkw 0x4b300376837a03c1 0x12cc00dda0de80f0 0xdbf003ff83f803e1 0x76fc00ffe0fe00f8

def z861 : W := mkw 0xf7ffebd253d5a870 0xbdfffaf494f56a1c 0x86f78380038000e0 0x21bde0e000e00038

def z862 : W := mkw 0x7fef7fdb780000b0 0xdffbdff6de00002c 0xf7fffffffc0000e0 0x7dffffffff000038

def z863 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xff0fffe07fe1c3fd 0xffc3fff81ff870ff

def z864 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0x9e0783e07fe1c3fd 0xa781e0f81ff870ff

def z865 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xae07c3807fe1c3fd 0xab81f0e01ff870ff

def z866 : W := mkw 0x4bb80352035400c1 0x12ee00d480d50030 0x92f003ff838000e0 0x24bc00ffe0e00038

def z867 : W := mkw 0x3b8dcae056e5cab8 0x4ee372b815b972ae 0xff0fffe07fffffff 0xffc3fff81fffffff

def z868 : W := mkw 0x77ef7fdb7a440000 0x9dfbdff6de910000 0xf7fffffffc660000 0x7dffffffff198000

def z869 : W := mkw 0x543197db7bd5a800 0x950c65f6def56a00 0x180003fffffffc02 0x060000ffffffff00

def z870 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xd2f803ff839e03e1 0x34be00ffe0e780f8

def z871 : W := mkw 0x180182e054a142b8 0x460060b8152850ae 0x960783e07f8003fd 0xa581e0f81fe000ff

def z872 : W := mkw 0x3447fc8978818030 0xcd11ff225e20600c 0x2407fc007c000000 0x0901ff001f000000

def z873 : W := mkw 0x3447fc897c81d43c 0xcd11ff225f20750f 0x2407fc007c01fc1e 0x8901ff001f007f07

def z874 : W := mkw 0x23dee80001912000 0x08f7ba0000644800 0xeffffc0003fffc02 0x7bffff0000ffff00

def z875 : W := mkw 0x08300134837e03c1 0x020c004d20df80f0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z876 : W := mkw 0x8463b19c60891174 0x2118ec671822445d 0xfef7b39c638103fd 0xffbdece718e040ff

def z877 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xf7fffffffc1e3c02 0x7dffffffff078f00

def z878 : W := mkw 0xa447fc896c81fc3c 0x2911ff225b207f0f 0x2407fc007c01fc1e 0x8901ff001f007f07

def z879 : W := mkw 0x5bbc4376977ec3c9 0x56ef10dda5dfb0f2 0xfbf843ffffffc3fd 0xfefe10fffffff0ff

def z880 : W := mkw 0x1b8c42601664c288 0x46e31098059930a2 0x010840601c66c000 0x004210180719b000

def z881 : W := mkw 0x1b8dc2e056e1c2b8 0x46e370b815b870ae 0xffffc3e07fe1c3fd 0xfffff0f81ff870ff

def z882 : W := mkw 0x3047fc897c81fc3c 0x4c11ff225f207f0f 0x2407fc007c01fc1e 0x8901ff001f007f07

def z883 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xd6f7b39c639833fd 0xb5bdece718e60cff

def z884 : W := mkw 0x23cee80002c18000 0x08f3ba0000b06000 0xeffffc0003fffc02 0x7bffff0000ffff00

def z885 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0x9f0783e07fe003fd 0xe7c1e0f81ff800ff

def z886 : W := mkw 0x1b8dc2e056e5c2b8 0x46e370b815b970ae 0xbf0fc3e07fe7c3fd 0xefc3f0f81ff9f0ff

def z887 : W := mkw 0x4bb80376877e43c9 0x12ee00dda1df90f2 0xdbf803fffffe03fd 0xf6fe00ffffff80ff

def z888 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xceffbc0003fffc02 0x33bfef0000ffff00

def z889 : W := mkw 0x0473b19861912030 0x011cec661864480c 0xfef7b39c639933fd 0xffbdece718e64cff

def z890 : W := mkw 0x7fef7fdb7a408080 0xdffbdff6de902020 0xf7fffffffc000000 0x7dffffffff000000

def z891 : W := mkw 0x8473b19ce19f3175 0x211cec673867cc5d 0xfef7b39c639f33fd 0xffbdece718e7ccff

def z892 : W := mkw 0x1005c08050810030 0x040170201420400c 0xbe07c3807f8103fd 0xef81f0e01fe040ff

def z893 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xc7ffffff9c000000 0x31ffffffe7000000

def z894 : W := mkw 0x8473b19ce19b3574 0x211cec673866cd5d 0xfef7b39c639f3fff 0xffbdece718e7cfff

def z895 : W := mkw 0x0810802487ffebf9 0x4204200921fffafe 0x0800000003ffffff 0x8200000000ffffff

def z896 : W := mkw 0x40b8011601180140 0x102e004580460050 0xdaf8039f839803e1 0x76be00e7e0e600f8

def z897 : W := mkw 0x6b8c4e638e66ce89 0x1ae31398e399b3a2 0x01084c639c66cc02 0x00421318e719b300

def z898 : W := mkw 0x0021819040810030 0x000860641020400c 0xfef7839c638103fd 0xffbde0e718e040ff

def z899 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xcaf8039f83fe03e1 0x32be00e7e0ff80f8

def z900 : W := mkw 0x0b980264837e0380 0x02e6009920df80e0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z901 : W := mkw 0x8810802487ff77fd 0x2204200921ffddff 0x0800000003ffffff 0x8200000000ffffff

def z902 : W := mkw 0x77ef7fdb78000030 0x9dfbdff6de00000c 0xf7fffffffc0003fd 0xfdffffffff0000ff

def z903 : W := mkw 0x039cc00003d58000 0x00e7300000f56000 0xeffffc0003fffc02 0x7bffff0000ffff00

def z904 : W := mkw 0x001094092bd5a800 0x000425024af56a00 0x79087c7ffffffc02 0x5e421f1fffffff00

def z905 : W := mkw 0x1b05c2c052c180b0 0x46c170b014b0602c 0xbf07c3e07f8103fd 0xefc1f0f81fe040ff

def z906 : W := mkw 0x546337db78000000 0x9518cdf6de000000 0x96f783fffc000000 0x25bde0ffff000000

def z907 : W := mkw 0x8053a08441993174 0x2014e82110664c5d 0xfef7b380639933fd 0xffbdece018e64cff

def z908 : W := mkw 0xe4fa3d1f291c3944 0xb93e8f47ca470e51 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z909 : W := mkw 0x0043a08040810030 0x0010e8201020400c 0xfef7b380638103fd 0xffbdece018e040ff

def z910 : W := mkw 0x4ba8037282660281 0x12ea00dca09980a0 0xdbf803ff83e603e1 0x76fe00ffe0f980f8

def z911 : W := mkw 0x4bb80356835e01c1 0x12ee00d5a0d78070 0xdaf8039f839e03e1 0x76be00e7e0e780f8

def z912 : W := mkw 0x23cee8000081a800 0x08f3ba0000206a00 0xeffffc00007ffc02 0x7bffff00001fff00

def z913 : W := mkw 0x5b8c42621660c288 0x56e31098859830a2 0x010840639c60c000 0x00421018e7183000

def z914 : W := mkw 0x042115bdec2a570c 0x0108456f7b0a95c3 0x100003fffc00031d 0x840000ffff0000c7

def z915 : W := mkw 0x8473a19441993174 0x211ce86510664c5d 0xbef78380639933fd 0xefbde0e018e64cff

def z916 : W := mkw 0x4ba8035202400080 0x12ea00d480900020 0xd3f803ff838000e0 0x74fe00ffe0e00038

def z917 : W := mkw 0x4bb80356035c01c1 0x12ee00d580d70070 0xdbf803ff839803e1 0x76fe00ffe0e600f8

def z918 : W := mkw 0xf7ef7fdb78001034 0xbdfbdff6de00040d 0xf7fffffffc00001c 0xfdffffffff000007

def z919 : W := mkw 0x4bb80376837e2bc1 0x12ee00dda0df8af0 0xdbf803ff83fe3fe3 0x76fe00ffe0ff8ff8

def z920 : W := mkw 0x6ceabd3b2ee1c2b8 0xdb3aaf4ecbb870ae 0x48f83c1f83e1c3fd 0x923e0f07e0f870ff

def z921 : W := mkw 0x4bb8037203740280 0x12ee00dc80dd00a0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z922 : W := mkw 0x8473b59d69993174 0x211ced675a664c5d 0xffffffffffffffff 0xffffffffffffffff

def z923 : W := mkw 0x23dee80003d5a830 0x08f7ba0000f56a0c 0xeffffc0003ffffff 0xfbffff0000ffffff

def z924 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xdaf003ff839803e1 0x76bc00ffe0e600f8

def z925 : W := mkw 0x0800142dac2a57cd 0x0200050b6b0a95f3 0x79087c7ffc7fffff 0xde421f1fff1fffff

def z926 : W := mkw 0xc472351f29183144 0xb11c8d47ca460c51 0x40f0301f80183000 0x103c0c07e0060c00

def z927 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xff0fc3e07fffc3fd 0xffc3f0f81ffff0ff

def z928 : W := mkw 0x7b8c4a629666ca89 0x5ee31298a599b2a2 0x01084c639c66cc02 0x00421318e719b300

def z929 : W := mkw 0x7b8c4e639e66c289 0xdee31398e799b0a2 0x01084c639c66c000 0x00421318e719b000

def z930 : W := mkw 0x1b05c2e054a142b8 0x46c170b8152850ae 0xbf07c3e07f8103fd 0xefc1f0f81fe040ff

def z931 : W := mkw 0x67ee7d1b28000000 0x99fb9f46ca000000 0xf7fffc7ffc000000 0x7dffff1fff000000

def z932 : W := mkw 0x5b05c2e2d6e3c2b9 0x56c170b8b5b8f0ae 0xbf07c3e3ffe1c3fd 0xefc1f0f8fff870ff

def z933 : W := mkw 0x77ef7fdb7a448800 0x9dfbdff6de912200 0xf7fffffffc000000 0x7dffffffff000000

def z934 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xfbf87fff83fe03e1 0x7efe1fffe0ff80f8

def z935 : W := mkw 0x9447f4897c81f43c 0x6511fd225f207d0f 0x2407fc007c01fc1e 0x8901ff001f007f07

def z936 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xdbf83fff83fe3fe3 0x76fe0fffe0ff8ff8

def z937 : W := mkw 0xc473b59f69993174 0xb11ced67da664c5d 0xfef7b39fe39933fd 0xffbdece7f8e64cff

def z938 : W := mkw 0x7bbc4b76937e03c1 0x9eef12dda4df80f0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z939 : W := mkw 0x176777d978000000 0x05d9ddf65e000000 0xf7fffffffc000000 0x7dffffffff000000

def z940 : W := mkw 0x4bb80376877e57cd 0x12ee00dda1df95f3 0xfbf87fff83ffffff 0xfefe1fffe0ffffff

def z941 : W := mkw 0x8473a19441993174 0x211ce86510664c5d 0xdef7839c039933fd 0xf7bde0e700e64cff

def z942 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xbef7839c638103fd 0xefbde0e718e040ff

def z943 : W := mkw 0x4bb80352035400c1 0x12ee00d480d50030 0xdbf803ff83fe00e0 0x76fe00ffe0ff8038

def z944 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xffffb3ffe39933fd 0xffffecfff8e64cff

def z945 : W := mkw 0x4bb80356835e01c1 0x12ee00d5a0d78070 0x82f0039f838000e0 0x20bc00e7e0e00038

def z946 : W := mkw 0x20dee80003d5a800 0x0837ba0000f56a00 0x6cfffc0003fffc02 0x1b3fff0000ffff00

def z947 : W := mkw 0x20daa80001952800 0x0836aa0000654a00 0xeffffc0003fffc02 0x7bffff0000ffff00

def z948 : W := mkw 0x3b8dcae056e5cab8 0x4ee372b815b972ae 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z949 : W := mkw 0x1b05c2e0d6e3c6b8 0x46c170b835b8f1ae 0xbf07c3e07fe7cfff 0xefc1f0f81ff9f3ff

def z950 : W := mkw 0x4bb80376813a03c1 0x12ee00dda04e80f0 0xdbf803ff839803e1 0x76fe00ffe0e600f8

def z951 : W := mkw 0x4bb80376837e17c5 0x12ee00dda0df85f1 0xdbf803ff83fe3fe3 0x76fe00ffe0ff8ff8

def z952 : W := mkw 0x8473a19441993174 0x211ce86510664c5d 0x86f78380038003fd 0xa1bde0e000e000ff

def z953 : W := mkw 0x7b8c4a621660c288 0xdee31298859830a2 0x010040601c60c000 0x0040101807183000

def z954 : W := mkw 0x3447fc8978810030 0x8d11ff225e20400c 0x2407fc007c01001c 0x8901ff001f004007

def z955 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xfbf833ff83ff33e1 0x7efe0cffe0ffccf8

def z956 : W := mkw 0x4030035601180140 0x100c00d580460050 0xdaf003ff839803e1 0x76bc00ffe0e600f8

def z957 : W := mkw 0x5bbc4376937e83c1 0x56ef10dda4dfa0f0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z958 : W := mkw 0x73deea4213d5a800 0x9cf7ba9084f56a00 0xeffffc0003fffc02 0x7bffff0000ffff00

def z959 : W := mkw 0x20daa80003d5a800 0x0836aa0000f56a00 0xeeffbc0003fffc02 0x7bbfef0000ffff00

def z960 : W := mkw 0x4bb80376877e43c9 0x12ee00dda1df90f2 0xfbf87fffffffffff 0xfefe1fffffffffff

def z961 : W := mkw 0x8463b19860813034 0x2118ec6618204c0d 0xfef7b39c638133fd 0xffbdece718e04cff

def z962 : W := mkw 0xa3dee80003d5a870 0x28f7ba0000f56a1c 0xeffffc0003fffce2 0x7bffff0000ffff38

def z963 : W := mkw 0x0473b19c61990170 0x011cec671866405c 0xfef7b39c639903fd 0xffbdece718e640ff

def z964 : W := mkw 0x4bb80352035400c1 0x12ee00d480d50030 0xc2f8039f838000e0 0x30be00e7e0e00038

def z965 : W := mkw 0x03b80134837e0340 0x00ee004d20df80d0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z966 : W := mkw 0x43b80356035c0140 0x10ee00d580d70050 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z967 : W := mkw 0x9c2117fdfc2a57fc 0x670845ff7f0a95ff 0x100003fffc0003fd 0x840000ffff0000ff

def z968 : W := mkw 0x8472351da91a3544 0x211c8d476a468d51 0x40f0301f80183000 0x103c0c07e0060c00

def z969 : W := mkw 0x1805c0a056e1c2b8 0x4601702815b870ae 0xbe07c3807fe1c3fd 0xef81f0e01ff870ff

def z970 : W := mkw 0x40b80136813e0341 0x102e004da04f80d0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z971 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xfbf843fffffe03e1 0x7efe10ffffff80f8

def z972 : W := mkw 0x4bb80376877e57cd 0x12ee00dda1df95f3 0xdbf803ff83fe03fd 0xf6fe00ffe0ff80ff

def z973 : W := mkw 0x0473319c61181144 0x011ccc6718460451 0xfef7b39c639933fd 0xffbdece718e64cff

def z974 : W := mkw 0x8472351d29183144 0x211c8d474a460c51 0x40f83c1f80183000 0x103e0f07e0060c00

def z975 : W := mkw 0x4bb80376877e47c9 0x12ee00dda1df91f2 0xdbf803ff83fecfe3 0x76fe00ffe0ffb3f8

def z976 : W := mkw 0x9473b59d79993174 0xa51ced675e664c5d 0xfef7b39c7f9933fd 0xffbdece71fe64cff

def z977 : W := mkw 0x48b80136837e03c1 0x122e004da0df80f0 0xdaf8039f83fe03e1 0x76be00e7e0ff80f8

def z978 : W := mkw 0x0810802487ffd7fd 0x4204200921fff5ff 0x0800000003ffffff 0x8200000000ffffff

def z979 : W := mkw 0x4bb80376877e57cd 0x12ee00dda1df95f3 0xfbf843ffffffffff 0xfefe10ffffffffff

def z980 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xc3f803ff83fe00e0 0x30fe00ffe0ff8038

def z981 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xbf07c3e07fffffff 0xefc1f0f81fffffff

def z982 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xaef7b380639933fd 0xabbdece018e64cff

def z983 : W := mkw 0x23deea4003d5a800 0x08f7ba9000f56a00 0xffffffe003fffc02 0x7ffffff800ffff00

def z984 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0x65fffc00007ffc02 0x197fff00001fff00

def z985 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xfeffbf9c639f3fff 0xffbfefe718e7cfff

def z986 : W := mkw 0x582117fffc2a57fd 0x560845ffff0a95ff 0x100003fffc0003fd 0x840000ffff0000ff

def z987 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xb607c3e07f81c3fd 0xad81f0f81fe070ff

def z988 : W := mkw 0x0463a19040810030 0x0118e8641020400c 0xbef78380638103fd 0xefbde0e018e040ff

def z989 : W := mkw 0x1b05c2c056c1c0b8 0x46c170b015b0702e 0xbe07c3807f81c3fd 0xef81f0e01fe070ff

def z990 : W := mkw 0x8031819441993174 0x200c606510664c5d 0xfef7839c639933fd 0xffbde0e718e64cff

def z991 : W := mkw 0x00000024842a4308 0x00000009210a90c2 0x79087c7ffc7fff1f 0xde421f1fff1fffc7

def z992 : W := mkw 0x9443b48978813034 0xa510ed225e204c0d 0x2407b0007c01301c 0x8901ec001f004c07

def z993 : W := mkw 0x4bb80356835e01c1 0x12ee00d5a0d78070 0xd3f803ff839e00e0 0x74fe00ffe0e78038

def z994 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xfffffffffc01031d 0xffffffffff0040c7

def z995 : W := mkw 0x5c2117fffc2a57bc 0xd70845ffff0a95ef 0x100003fffc0003fd 0x840000ffff0000ff

def z996 : W := mkw 0x23ce6824842a570c 0x08f39a09210a95c3 0xeffffc00007fff1f 0xfbffff00001fffc7

def z997 : W := mkw 0x0b0182e046e142b8 0x02c060b811b850ae 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z998 : W := mkw 0x5b8c42621664c289 0x56e31098859930a2 0x010040601c60c000 0x0040101807183000

def z999 : W := mkw 0x000014292c204208 0x0000050a4b081082 0x79087c7ffc7fff1f 0xde421f1fff1fffc7

def z1000 : W := mkw 0x0073a19441992170 0x001ce8651066485c 0xfef7b39c639933fd 0xffbdece718e64cff

def z1001 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xff0fc3ffffe1c3fd 0xffc3f0fffff870ff

def z1002 : W := mkw 0x3b8c4e619e66ce88 0x4ee313986799b3a2 0x01084c639c66cc02 0x00421318e719b300

def z1003 : W := mkw 0x7fef7fdb780000c1 0x9ffbdff6de000030 0xf7fffffffc0000e0 0x7dffffffff000038

def z1004 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xb6f7fffffc000000 0x2dbdffffff000000

def z1005 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xb707c3e07f8003fd 0xedc1f0f81fe000ff

def z1006 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xcef7b39c039933fd 0xb3bdece700e64cff

def z1007 : W := mkw 0x000014092c00540c 0x000005024b001503 0x79087c7ffc7ffc1e 0xde421f1fff1fff07

def z1008 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xbf07ffe07fe1ffff 0xefc1fff81ff87fff

def z1009 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xffffffffff8003e1 0x7fffffffffe000f8

def z1010 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xff07f3e07ff9f3fd 0xffc1fcf81ffe7cff

def z1011 : W := mkw 0x8473b19c619d3974 0x211cec6718674e5d 0xfef7b39c639f3fff 0xffbdece718e7cfff

def z1012 : W := mkw 0x6bdeea4203d5a881 0x1af7ba9080f56a20 0xeffffc0003fffc02 0x7bffff0000ffff00

def z1013 : W := mkw 0x1305c2e054a14238 0x04c170b81528508e 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z1014 : W := mkw 0x7fffebd253d5a8b0 0xdffffaf494f56a2c 0x86f78380038000e0 0x21bde0e000e00038

def z1015 : W := mkw 0x8473a19041912070 0x211ce8641064481c 0x96f78380638003fd 0xa5bde0e018e000ff

def z1016 : W := mkw 0x64fa3d1fa91e1545 0x993e8f47ea478551 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z1017 : W := mkw 0x8473b59d69993174 0x211ced675a664c5d 0xfef7ff9c7f9933fd 0xffbdffe71fe64cff

def z1018 : W := mkw 0x20dee8000195a800 0x0837ba0000656a00 0x6dfffc00007ffc02 0x5b7fff00001fff00

def z1019 : W := mkw 0x7b8c4e639e664689 0x9ee31398e79991a2 0x01084c639c66cc02 0x00421318e719b300

def z1020 : W := mkw 0x4bb80356835e01c1 0x12ee00d5a0d78070 0xcbf8039f83fe00e0 0x72fe00e7e0ff8038

def z1021 : W := mkw 0x60fa3d1fa91e3d45 0x183e8f47ea478f51 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z1022 : W := mkw 0x37cf7c8978000000 0x8df3df225e000000 0xf7fffc7ffc000000 0x7dffff1fff000000

def z1023 : W := mkw 0x33deea4013d5a800 0x0cf7ba9004f56a00 0xeffffc601ffffc02 0x7bffff1807ffff00

def z1024 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xfffffc0063ffff1f 0xffffff0018ffffc7

def z1025 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0x65fffc7ffc000000 0x197fff1fff000000

def z1026 : W := mkw 0xa443bc8968813034 0xa910ef225a204c0d 0x2407bc006001301c 0x8901ef0018004c07

def z1027 : W := mkw 0x8473b59d69993574 0x211ced675a664d5d 0xfef7bf9c63993fff 0xffbdefe718e64fff

def z1028 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xf6f7b3fffc000000 0x7dbdecffff000000

def z1029 : W := mkw 0xb447fc8978812030 0xad11ff225e20480c 0x2407fc007c000000 0x0901ff001f000000

def z1030 : W := mkw 0x0463359968000000 0x0118cd665a000000 0xf6f7b3fffc000000 0x7dbdecffff000000

def z1031 : W := mkw 0x8473a19041912070 0x211ce8641064481c 0x8ef78380038103fd 0xa3bde0e000e040ff

def z1032 : W := mkw 0x77ef7fdb7a408000 0x9dfbdff6de902000 0xf7fffffffc60c000 0x7dffffffff183000

def z1033 : W := mkw 0x5bb80376977e43c9 0x56ee00dda5df90f2 0xdbf803ff9ffe03e1 0x76fe00ffe7ff80f8

def z1034 : W := mkw 0x100182c050810030 0x040060b01420400c 0xbe0783e07f8103fd 0xef81e0f81fe040ff

def z1035 : W := mkw 0x8473b19ce19b3174 0x211cec673866cc5d 0xfeffb39fe39f33fd 0xffbfece7f8e7ccff

def z1036 : W := mkw 0x43b80116835e0141 0x10ee0045a0d78050 0xdbf8039f83fe03e1 0x76fe00e7e0ff80f8

def z1037 : W := mkw 0x0053a08041912030 0x0014e8201064480c 0xbef78380638103fd 0xefbde0e018e040ff

def z1038 : W := mkw 0x1b05c2e056e1c2b8 0x46c170b815b870ae 0xbe0783e07f8103fd 0xef81e0f81fe040ff

def z1039 : W := mkw 0x00300134813a0340 0x000c004d204e80d0 0xdaf003ff839803e1 0x76bc00ffe0e600f8

def z1040 : W := mkw 0x080180a046e1c2b8 0x4200602811b870ae 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z1041 : W := mkw 0x7b8c4e631e64ca88 0xdee31398c79932a2 0x01084c639c66cc02 0x00421318e719b300

def z1042 : W := mkw 0x2056e8000191a800 0x0815ba0000646a00 0xeffffc0003fffc02 0x7bffff0000ffff00

def z1043 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xfef7b39c63ffffff 0xffbdece718ffffff

def z1044 : W := mkw 0x23de68000354a800 0x08f79a0000d52a00 0xe7fffc00007efc02 0x79ffff00001fbf00

def z1045 : W := mkw 0x0001808044814038 0x000060201120500e 0xbe07c3807f81c3fd 0xef81f0e01fe070ff

def z1046 : W := mkw 0x576777db78000000 0x95d9ddf6de000000 0xf7f7f3fffc000000 0x7dfdfcffff000000

def z1047 : W := mkw 0x1b05c2e0d6e7c2b9 0x46c170b835b9f0ae 0xbf07c3e07fe7c3fd 0xefc1f0f81ff9f0ff

def z1048 : W := mkw 0x4bbc4376837e03c1 0x12ef10dda0df80f0 0xffffc3ff83fe03e1 0x7ffff0ffe0ff80f8

def z1049 : W := mkw 0x4bb80376877ec3c9 0x52ee00dda1dfb0f2 0xdbf803ff83fec3e1 0x76fe00ffe0ffb0f8

def z1050 : W := mkw 0x1b05c2e056e1eab8 0x46c170b815b87aae 0xbf07c3e07fe1ffff 0xefc1f0f81ff87fff

def z1051 : W := mkw 0x3b8dcae056e1c2b8 0x4ee372b815b870ae 0xbf0fcfe07fe1c3fd 0xefc3f3f81ff870ff

def z1052 : W := mkw 0x77ef6fd358000000 0x9dfbdbf4d6000000 0xd7ffcfff9c000000 0x75fff3ffe7000000

def z1053 : W := mkw 0x77ef7fdb78040800 0x9dfbdff6de010200 0xf7fffffffc060c02 0x7dffffffff018300

def z1054 : W := mkw 0x0305c0a046e1c238 0x00c1702811b8708e 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z1055 : W := mkw 0x1805c2e054a1c2b8 0x460170b8152870ae 0xbe07c3e07f81c3fd 0xef81f0f81fe070ff

def z1056 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xf7fffffffc66cc02 0x7dffffffff19b300

def z1057 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xffffb39c63ff33fd 0xffffece718ffccff

def z1058 : W := mkw 0x27ef7d9968000000 0x09fbdf665a000000 0xf7fffffffc000000 0x7dffffffff000000

def z1059 : W := mkw 0xd42117fffc2a577c 0xb50845ffff0a95df 0x100003fffc0003fd 0x840000ffff0000ff

def z1060 : W := mkw 0x1b0182e056e142b8 0x46c060b815b850ae 0xbf0783e07fe103fd 0xefc1e0f81ff840ff

def z1061 : W := mkw 0x0463b19c60891134 0x0118ec671822444d 0xfef7b39c639933fd 0xffbdece718e64cff

def z1062 : W := mkw 0x48300376813a03c1 0x120c00dda04e80f0 0x92f003ff838003e1 0x24bc00ffe0e000f8

def z1063 : W := mkw 0x77ef7fdb78002800 0x9dfbdff6de000a00 0xf7fffffffc003c02 0x7dffffffff000f00

def z1064 : W := mkw 0x33cf7ec978000000 0x0cf3dfb25e000000 0xf7fffffffc000000 0x7dffffffff000000

def z1065 : W := mkw 0x34677d9978000000 0x8d19df665e000000 0xf7fffffffc000000 0x7dffffffff000000

def z1066 : W := mkw 0x5b8dc2e256e1c2b8 0x56e370b895b870ae 0xbf0fc3e3ffe1c3fd 0xefc3f0f8fff870ff

def z1067 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xdef7839c639803fd 0xf7bde0e718e600ff

def z1068 : W := mkw 0x0031819041910070 0x000c60641064401c 0xbef78380638103fd 0xefbde0e018e040ff

def z1069 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xfef7ff9c6399ffff 0xffbdffe718e67fff

def z1070 : W := mkw 0x1305c08056c1c038 0x44c1702015b0700e 0xbf07c3807fe1c3fd 0xefc1f0e01ff870ff

def z1071 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xb7f7c3fffc000000 0x6dfdf0ffff000000

def z1072 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0x93f803ff83e603e1 0x24fe00ffe0f980f8

def z1073 : W := mkw 0x23dee80003d5a800 0x08f7ba0000f56a00 0xfffffc7f83fffc02 0x7fffff1fe0ffff00

def z1074 : W := mkw 0x77ef7fdb7a400000 0x9dfbdff6de900000 0xffffffffffe00000 0x7ffffffffff80000

def z1075 : W := mkw 0x1305c2c052c18030 0x04c170b014b0600c 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z1076 : W := mkw 0x77ef7fdb78000000 0x9dfbdff6de000000 0xfffffffffc61c000 0x7fffffffff187000

def z1077 : W := mkw 0x8473b59de99b3574 0x211ced677a66cd5d 0xfef7b39fe39933fd 0xffbdece7f8e64cff

def z1078 : W := mkw 0x74677fdb78000000 0x9d19dff6de000000 0xf6f7fffffc000000 0x7dbdffffff000000

def z1079 : W := mkw 0x0356e00003d1a000 0x00d5b80000f46800 0xeffffc0003fffc02 0x7bffff0000ffff00

def z1080 : W := mkw 0xc4fa351fa91e3545 0x313e8d47ea478d51 0x40f83c1f801e3c02 0x103e0f07e0078f00

def z1081 : W := mkw 0x8473b19c6199b974 0x211cec6718666e5d 0xfef7b39c6399ffff 0xffbdece718e67fff

def z1082 : W := mkw 0x74ef7d9b78000000 0x9d3bdf66de000000 0x75fffc7ffc000000 0x5d7fff1fff000000

def z1083 : W := mkw 0x180182e054a142b8 0x460060b8152850ae 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z1084 : W := mkw 0x48b80376837e03c1 0x122e00dda0df80f0 0x58f803ff83fe03e1 0x163e00ffe0ff80f8

def z1085 : W := mkw 0x8072a11401993174 0x201ca84500664c5d 0xfef7b39c039933fd 0xffbdece700e64cff

def z1086 : W := mkw 0xf7ef7fdb78000070 0xbdfbdff6de00001c 0xf7fffffffc0000e0 0x7dffffffff000038

def z1087 : W := mkw 0x43b80376813a0340 0x10ee00dda04e80d0 0xdbf803ff83fe03e1 0x76fe00ffe0ff80f8

def z1088 : W := mkw 0x4ba80376826a03c1 0x12ea00dda09a80f0 0xdbf803ff83e003e1 0x76fe00ffe0f800f8

def z1089 : W := mkw 0x5bbc4376937e03c1 0x16ef10dda4df80f0 0xdbf843ff9ffe03e1 0x76fe10ffe7ff80f8

def z1090 : W := mkw 0x57eb37db78000000 0x95facdf6de000000 0xf7ffb3fffc000000 0x7dffecffff000000

def z1091 : W := mkw 0x1b0542e056604288 0x06c150b8159810a2 0xbf07c3e07fe1c3fd 0xefc1f0f81ff870ff

def z1092 : W := mkw 0x6bbc4b76837e03c1 0x1aef12dda0df80f0 0xdbf84fff83fe03e1 0x76fe13ffe0ff80f8

def z1093 : W := mkw 0xa4723d1d29183144 0xa91c8f474a460c51 0x40f03c1c00183000 0x103c0f0700060c00

def z1094 : W := mkw 0x7bffebd253d5a8f1 0x5efffaf494f56a3c 0x86f78380038000e0 0x21bde0e000e00038

def z1095 : W := mkw 0x2bdeea4003d5a880 0x0af7ba9000f56a20 0xefffff8003fffce2 0x7bffffe000ffff38

def z1096 : W := mkw 0x1b05c2e0d6e3c2b8 0x46c170b835b8f0ae 0xbf0fc3e3ffe7c3fd 0xefc3f0f8fff9f0ff

def z1097 : W := mkw 0x4bb80376037803c0 0x12ee00dd80de00f0 0xdbf803ff83f803e1 0x76fe00ffe0fe00f8

def z1098 : W := mkw 0x4bb80376837e03c1 0x12ee00dda0df80f0 0xdbf84fff83fecfe3 0x76fe13ffe0ffb3f8

def z1099 : W := mkw 0x8473b19861913074 0x211cec6618644c1d 0xbef7b380638133fd 0xefbdece018e04cff

def z1100 : W := mkw 0x8473b19c61993174 0x211cec6718664c5d 0xffffff9c639933fd 0xffffffe718e64cff

def z1101 : W := mkw 0x63ee7f5b28000000 0x18fb9fd6ca000000 0xf7fffffffc000000 0x7dffffffff000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(0,[z7,z0,z2,z3,z4,z5,z6]),(0,[z0,z8,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z9,z6]),(0,[z0,z2,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z11,z4,z5,z6]),(0,[z0,z2,z12,z3,z4,z5,z6]),(0,[z0,z13,z2,z3,z4,z5,z14]),(0,[z0,z15,z3,z16,z4,z5,z6])],[(0,[z0,z2,z17,z3,z18,z4,z6]),(0,[z0,z2,z3,z4,z5,z19,z6]),(0,[z0,z2,z3,z20,z5,z21,z6])],[(0,[z0,z22,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z23,z6]),(0,[z0,z24,z2,z3,z4,z5,z6]),(0,[z0,z25,z2,z3,z4,z5,z6]),(0,[z0,z26,z2,z3,z4,z5,z6])],[(0,[z27,z2,z3,z4,z28,z5,z6]),(0,[z0,z2,z29,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z30]),(0,[z31,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z32,z6]),(0,[z0,z33,z2,z3,z4,z5,z6]),(0,[z0,z34,z2,z3,z4,z5,z6]),(0,[z0,z35,z2,z3,z4,z5,z6])],[(0,[z36,z37,z2,z3,z4,z5,z6]),(1,[z37,z38,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z39,z6]),(0,[z0,z40,z2,z41,z4,z5,z6]),(0,[z0,z42,z2,z3,z43,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z44]),(0,[z0,z2,z3,z4,z5,z21,z6])]],
   [[(0,[z0,z2,z45,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z46]),(0,[z47,z0,z2,z3,z4,z5,z32]),(0,[z0,z48,z3,z4,z49,z5,z6])],[(0,[z0,z50,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z51,z6]),(0,[z0,z2,z3,z4,z52,z5,z6]),(0,[z0,z2,z3,z53,z5,z14,z6]),(0,[z0,z3,z4,z5,z6,z54,z55])],[(0,[z37,z0,z38,z3,z4,z5,z6]),(0,[z0,z56,z2,z3,z4,z5,z6])],[(0,[z57,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z17,z3,z4,z6]),(0,[z0,z3,z4,z49,z5,z58,z6]),(0,[z0,z2,z3,z4,z53,z5,z6]),(0,[z0,z2,z3,z59,z4,z5,z6])],[(0,[z0,z2,z60,z3,z4,z5,z6]),(0,[z37,z0,z2,z3,z4,z5,z61]),(0,[z62,z0,z2,z3,z5,z14,z6]),(0,[z0,z63,z2,z3,z4,z5,z6]),(0,[z0,z64,z2,z3,z4,z5,z6]),(0,[z0,z42,z2,z3,z65,z5,z6]),(0,[z0,z2,z3,z4,z49,z5,z6]),(0,[z0,z66,z2,z3,z4,z5,z6])],[(0,[z0,z67,z2,z3,z4,z5,z6]),(0,[z0,z68,z2,z3,z4,z49,z6]),(0,[z0,z48,z3,z4,z69,z5,z6]),(0,[z0,z2,z3,z4,z70,z6,z55])]],
   [[(0,[z0,z40,z3,z4,z5,z58,z6])],[(0,[z0,z2,z3,z4,z71,z5,z6])],[(0,[z0,z2,z3,z72,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z73,z6])],[(0,[z37,z0,z48,z3,z4,z5,z6]),(0,[z0,z74,z40,z3,z4,z5,z6]),(0,[z0,z2,z3,z75,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z76,z6]),(0,[z0,z2,z3,z77,z4,z5,z6]),(0,[z0,z78,z2,z3,z4,z49,z5]),(0,[z0,z79,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z80,z5,z6]),(0,[z0,z81,z2,z3,z41,z4,z5]),(0,[z0,z2,z82,z3,z4,z5,z6]),(0,[z0,z83,z2,z84,z4,z5,z6]),(0,[z0,z2,z3,z85,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z86,z6]),(0,[z0,z2,z3,z4,z87,z5,z6])],[(0,[z0,z88,z2,z3,z20,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z89]),(0,[z0,z90,z2,z3,z4,z5,z6])],[(0,[z91,z0,z2,z3,z4,z5,z6]),(0,[z62,z2,z3,z92,z4,z5,z6]),(1,[z0,z2,z4,z93,z5,z6]),(0,[z0,z2,z94,z3,z4,z5,z6]),(0,[z0,z2,z84,z3,z95,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z96]),(0,[z0,z2,z3,z4,z5,z6,z97])]],
   [[(0,[z0,z2,z3,z98,z4,z5,z6]),(0,[z0,z2,z99,z3,z4,z5,z6]),(0,[z0,z48,z2,z3,z4,z5,z58]),(0,[z0,z100,z2,z3,z4,z5,z6]),(0,[z0,z101,z2,z3,z4,z5,z6]),(0,[z0,z2,z102,z3,z4,z5,z103]),(0,[z0,z2,z3,z16,z4,z5,z104]),(0,[z0,z105,z2,z3,z4,z6,z55])],[(0,[z0,z38,z3,z41,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z106]),(0,[z0,z2,z3,z4,z5,z103,z32]),(0,[z0,z2,z107,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z54])],[(0,[z0,z108,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z109,z5,z6]),(0,[z0,z2,z3,z4,z5,z110,z6]),(0,[z0,z2,z3,z4,z5,z111,z6]),(1,[z0,z66,z2,z4,z112,z6]),(0,[z0,z2,z3,z5,z14,z6,z104])],[(0,[z113,z0,z2,z3,z4,z5,z114]),(0,[z115,z0,z2,z3,z4,z5,z6]),(0,[z0,z116,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z117,z5,z6]),(0,[z0,z118,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z119,z5,z6]),(1,[z47,z2,z3,z4,z5,z120])],[(0,[z0,z2,z121,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z122]),(1,[z0,z3,z4,z5,z51,z6]),(0,[z0,z2,z3,z4,z123,z5,z6]),(0,[z0,z124,z2,z3,z4,z5,z6]),(0,[z0,z125,z3,z4,z5,z58,z6])],[(1,[z0,z2,z3,z4,z5,z126]),(0,[z113,z0,z2,z3,z127,z5,z6]),(0,[z0,z2,z3,z128,z4,z5,z6]),(0,[z0,z129,z3,z41,z4,z5,z6]),(0,[z130,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z131])]],
   [[(0,[z0,z2,z3,z4,z132,z5,z6]),(0,[z0,z2,z3,z4,z5,z32,z133])],[(0,[z0,z2,z3,z4,z5,z134,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z135]),(0,[z0,z125,z2,z3,z136,z5,z6]),(0,[z0,z137,z2,z3,z4,z5,z133]),(0,[z138,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z139,z4,z5,z6])],[(0,[z37,z0,z3,z4,z5,z58,z6]),(0,[z0,z125,z2,z3,z4,z140,z5]),(0,[z0,z2,z3,z141,z4,z5,z6]),(0,[z0,z142,z2,z3,z20,z4,z6]),(0,[z143,z0,z2,z3,z4,z5,z6])],[(0,[z144,z0,z2,z4,z112,z5,z6]),(0,[z0,z74,z2,z3,z4,z5,z6]),(1,[z0,z74,z41,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z145,z6]),(0,[z146,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z147,z4,z5,z6]),(0,[z0,z2,z3,z20,z4,z5,z6]),(1,[z0,z105,z2,z3,z4,z55])],[(0,[z148,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z149,z4,z5,z150,z6]),(0,[z0,z151,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z152,z5,z6])],[(0,[z0,z153,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z103,z6,z133]),(0,[z0,z2,z3,z4,z5,z154,z6]),(0,[z0,z155,z2,z3,z4,z5,z6])],[(0,[z0,z156,z2,z3,z4,z5,z6]),(0,[z157,z0,z2,z3,z4,z5,z6]),(0,[z0,z158,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z159,z5,z6]),(0,[z0,z2,z3,z4,z5,z160,z6])]],
   [[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z161,z3,z4,z5,z6]),(0,[z0,z42,z88,z3,z4,z5,z6]),(0,[z0,z2,z162,z3,z4,z112,z6])],[(0,[z163,z0,z2,z3,z4,z5,z6]),(0,[z164,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z20,z43,z4,z6])],[(1,[z165,z2,z3,z4,z166,z6]),(0,[z0,z83,z2,z4,z53,z5,z6]),(0,[z0,z2,z167,z3,z4,z5,z6])],[(1,[z0,z168,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z169,z5,z6]),(0,[z0,z2,z3,z4,z170,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z171]),(0,[z0,z142,z2,z3,z43,z5,z6])],[(0,[z172,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z173,z174]),(0,[z0,z2,z3,z4,z5,z6,z175])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z27,z62,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z43,z92,z5,z6]),(1,[z0,z3,z4,z5,z6,z54])],[(0,[z0,z176,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z65,z4,z5,z6]),(0,[z0,z177,z2,z3,z4,z5,z6]),(0,[z0,z13,z2,z3,z20,z5,z6])],[(0,[z0,z2,z3,z4,z5,z178,z6])]],
   [[(0,[z0,z2,z17,z3,z4,z5,z6]),(0,[z62,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z179,z6])],[(0,[z0,z2,z3,z180,z4,z5,z6]),(1,[z0,z2,z3,z181,z5,z6]),(1,[z0,z2,z3,z4,z182,z6]),(0,[z0,z2,z183,z3,z4,z5,z6])],[(0,[z37,z0,z184,z3,z4,z5,z6]),(0,[z0,z2,z3,z185,z4,z5,z6]),(0,[z0,z2,z3,z186,z4,z5,z6])],[(0,[z113,z0,z2,z187,z4,z5,z6]),(0,[z0,z188,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z166,z5,z6]),(0,[z0,z2,z3,z189,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z190]),(0,[z0,z2,z3,z191,z4,z5,z6]),(0,[z0,z88,z2,z3,z49,z5,z6]),(1,[z0,z2,z3,z4,z160,z6])],[(0,[z0,z192,z2,z3,z4,z5,z6]),(0,[z113,z0,z2,z18,z4,z5,z6]),(0,[z0,z2,z193,z3,z4,z5,z6]),(0,[z0,z83,z2,z3,z53,z5,z6]),(0,[z0,z2,z3,z4,z194,z5,z6])],[(0,[z0,z2,z3,z4,z195,z5,z6])],[(0,[z196,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z197,z5,z6]),(0,[z0,z2,z3,z4,z198,z5,z6])],[(0,[z0,z2,z3,z4,z199,z5,z6]),(0,[z0,z2,z3,z4,z200,z5,z6]),(0,[z0,z2,z3,z201,z4,z5,z6]),(0,[z202,z0,z2,z3,z4,z5,z6]),(0,[z0,z125,z2,z3,z4,z5,z32]),(0,[z0,z203,z2,z3,z4,z5,z6]),(0,[z0,z204,z124,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z205,z5,z6]),(0,[z0,z2,z3,z4,z206,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z207,z5,z6])],[(0,[z0,z208,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z43,z28,z5,z6]),(0,[z0,z209,z2,z3,z4,z5,z6]),(0,[z0,z210,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z211,z6])],[(0,[z212,z0,z2,z3,z4,z5,z32]),(0,[z0,z2,z3,z213,z4,z5,z6]),(1,[z0,z204,z3,z4,z69,z6])],[(0,[z0,z214,z2,z3,z4,z5,z6]),(0,[z0,z215,z2,z3,z4,z5,z6]),(0,[z0,z204,z2,z3,z4,z69,z6])],[(1,[z0,z2,z3,z199,z5,z6]),(0,[z0,z2,z3,z4,z216,z5,z6])],[(0,[z0,z217,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z218])],[(0,[z0,z2,z3,z4,z5,z6,z106]),(0,[z0,z2,z3,z4,z5,z70,z120]),(0,[z0,z2,z3,z219,z4,z5,z6]),(0,[z0,z220,z2,z3,z4,z5,z6]),(0,[z0,z221,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z222,z4,z5,z6]),(0,[z0,z2,z3,z4,z140,z5,z70])],[(0,[z0,z223,z2,z3,z4,z5,z6]),(0,[z0,z2,z224,z3,z4,z5,z6]),(0,[z0,z225,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z226,z2,z3,z4,z5,z6])],[(0,[z0,z227,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z228,z5,z6]),(0,[z0,z2,z3,z4,z229,z5,z6]),(0,[z0,z137,z2,z4,z5,z6,z133]),(0,[z0,z2,z3,z4,z5,z70,z6])],[(0,[z0,z2,z3,z4,z230,z5,z6]),(0,[z0,z2,z3,z231,z4,z5,z6]),(0,[z0,z2,z3,z232,z4,z5,z6]),(0,[z0,z124,z3,z4,z5,z174,z6]),(0,[z0,z3,z4,z5,z58,z6,z233]),(0,[z0,z105,z125,z2,z3,z4,z5]),(0,[z0,z2,z3,z234,z4,z5,z6]),(1,[z0,z2,z3,z5,z6,z218])],[(0,[z0,z2,z3,z235,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z236]),(0,[z0,z74,z2,z41,z4,z5,z6]),(0,[z0,z142,z124,z2,z3,z4,z6]),(0,[z0,z66,z2,z3,z4,z112,z6])],[(0,[z0,z2,z3,z4,z5,z237,z6]),(0,[z0,z238,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z239,z4,z5,z6]),(0,[z0,z240,z2,z3,z4,z5,z6])],[(0,[z0,z2,z241,z3,z4,z5,z6]),(0,[z0,z48,z2,z3,z4,z5,z233]),(0,[z0,z2,z84,z95,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z242,z6]),(0,[z0,z243,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z20,z5,z14,z6]),(0,[z244,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z245]),(0,[z246,z0,z2,z3,z4,z5,z6]),(0,[z0,z247,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z173]),(0,[z0,z2,z3,z248,z4,z5,z6]),(0,[z0,z2,z249,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z250,z6]),(0,[z113,z0,z2,z3,z4,z251,z6]),(0,[z0,z2,z252,z3,z4,z5,z6]),(0,[z0,z124,z3,z4,z5,z58,z6]),(0,[z0,z2,z3,z4,z5,z253,z6]),(0,[z0,z105,z2,z3,z4,z5,z70]),(0,[z0,z155,z3,z4,z5,z6,z55]),(0,[z0,z2,z3,z5,z6,z218,z55])]],
   [[(0,[z0,z48,z40,z3,z4,z5,z6]),(0,[z0,z254,z2,z3,z4,z5,z6])],[(0,[z0,z255,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z14,z6])],[(0,[z0,z2,z3,z256,z4,z5,z6]),(0,[z0,z13,z2,z3,z53,z5,z6])],[(0,[z165,z0,z2,z162,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z257,z6]),(0,[z0,z258,z2,z3,z4,z5,z6]),(0,[z0,z13,z2,z3,z49,z5,z6]),(0,[z0,z137,z125,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z259,z6]),(0,[z27,z0,z2,z3,z4,z5,z6]),(0,[z0,z260,z2,z3,z4,z5,z6]),(0,[z0,z204,z2,z3,z4,z174,z6]),(0,[z0,z125,z2,z3,z16,z4,z5]),(0,[z0,z2,z3,z4,z261,z5,z6])],[(0,[z0,z262,z2,z3,z4,z5,z6]),(0,[z0,z48,z3,z41,z4,z5,z6]),(0,[z0,z2,z3,z4,z263,z5,z6]),(0,[z0,z88,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z264,z6]),(0,[z0,z2,z265,z3,z4,z5,z6]),(1,[z0,z266,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z4,z5,z14])],[(0,[z0,z2,z3,z4,z267,z5,z6]),(0,[z0,z2,z3,z4,z112,z5,z6]),(0,[z0,z2,z3,z4,z5,z268,z6]),(0,[z0,z2,z269,z3,z4,z5,z6])],[(0,[z36,z0,z2,z3,z199,z5,z6]),(0,[z0,z270,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z65,z5,z14,z6]),(0,[z0,z2,z3,z271,z4,z5,z6]),(0,[z0,z2,z102,z3,z159,z5,z6])]],
   [[(0,[z272,z0,z2,z3,z4,z5,z273]),(0,[z165,z0,z2,z3,z4,z150,z6]),(0,[z0,z2,z3,z4,z5,z274,z6]),(0,[z0,z275,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z276,z4,z5,z6]),(0,[z0,z184,z3,z41,z4,z5,z6]),(0,[z0,z277,z2,z3,z4,z5,z6]),(0,[z113,z0,z2,z4,z5,z103,z6]),(0,[z278,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z222,z5,z6,z55])],[(0,[z0,z279,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z92,z4,z5,z6]),(0,[z0,z280,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z281,z6,z120])],[(0,[z0,z2,z3,z4,z282,z5,z6]),(0,[z283,z0,z2,z3,z4,z5,z6]),(0,[z284,z0,z2,z3,z4,z5,z6])],[(0,[z285,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z136,z5,z6]),(0,[z0,z286,z2,z3,z4,z5,z6])],[(0,[z287,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z288,z3,z4,z5,z6]),(0,[z272,z0,z2,z162,z3,z4,z6]),(0,[z0,z48,z2,z3,z4,z5,z120]),(0,[z0,z2,z289,z3,z4,z5,z6]),(1,[z0,z81,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z182,z5,z6]),(0,[z0,z2,z3,z290,z4,z5,z6]),(0,[z0,z2,z102,z3,z4,z5,z6]),(1,[z0,z15,z3,z4,z5,z6]),(0,[z0,z291,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z292,z6]),(1,[z0,z2,z3,z128,z5,z6]),(0,[z0,z293,z2,z3,z4,z5,z6]),(0,[z0,z2,z294,z3,z4,z5,z6]),(0,[z0,z2,z162,z4,z5,z111,z6])],[(0,[z113,z0,z295,z3,z4,z5,z6]),(0,[z296,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z69,z5,z6]),(0,[z0,z297,z2,z3,z4,z5,z6])]],
   [[(0,[z298,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z127,z5,z6]),(0,[z0,z2,z3,z95,z92,z5,z6]),(0,[z299,z0,z2,z3,z4,z5,z6]),(0,[z0,z48,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z300,z4,z5,z6])],[(0,[z0,z2,z3,z301,z4,z5,z6]),(0,[z0,z302,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z136,z5,z6])],[(1,[z0,z2,z3,z4,z5,z114]),(0,[z303,z0,z2,z3,z4,z5,z6]),(0,[z272,z0,z2,z3,z4,z150,z6]),(0,[z0,z2,z3,z4,z5,z304,z6]),(0,[z0,z2,z3,z305,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z306,z6]),(0,[z307,z0,z2,z3,z4,z5,z6]),(0,[z165,z0,z66,z2,z3,z4,z6]),(1,[z0,z153,z3,z4,z5,z6]),(0,[z0,z168,z2,z3,z4,z6,z120]),(0,[z0,z74,z3,z41,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z308,z6]),(1,[z0,z137,z2,z4,z5,z133]),(0,[z0,z2,z102,z3,z4,z160,z6])],[(0,[z0,z2,z3,z4,z5,z6,z309])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z127,z5,z6]),(0,[z310,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z311,z6]),(0,[z0,z312,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z43,z21,z6])],[(0,[z144,z0,z137,z2,z4,z5,z6]),(0,[z0,z313,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z314,z6])],[(0,[z0,z2,z3,z4,z93,z5,z6]),(0,[z0,z2,z3,z4,z5,z315,z6]),(0,[z0,z2,z3,z43,z5,z21,z6]),(0,[z0,z2,z3,z4,z5,z316,z6]),(1,[z0,z3,z4,z261,z5,z6])]],
   [[(0,[z0,z317,z2,z3,z4,z5,z6]),(0,[z0,z48,z124,z3,z4,z5,z6]),(0,[z318,z0,z2,z3,z4,z5,z6])],[(0,[z0,z88,z3,z65,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z319,z6])],[(0,[z0,z2,z3,z4,z5,z6,z320]),(0,[z0,z2,z3,z4,z321,z5,z6])],[(0,[z0,z40,z184,z3,z4,z5,z6]),(0,[z0,z125,z2,z102,z3,z4,z5])],[(0,[z0,z2,z3,z95,z28,z5,z6]),(1,[z0,z2,z149,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z120,z55])],[(0,[z0,z2,z3,z4,z5,z6,z322]),(0,[z0,z2,z323,z3,z4,z5,z6]),(0,[z272,z0,z66,z2,z3,z4,z6]),(0,[z0,z2,z129,z3,z4,z5,z6]),(0,[z0,z324,z2,z3,z4,z5,z6]),(0,[z325,z0,z2,z3,z4,z5,z6]),(0,[z0,z326,z2,z3,z4,z5,z6]),(0,[z0,z327,z2,z3,z4,z5,z6]),(0,[z0,z13,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z140,z70])],[(0,[z0,z328,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z281,z6]),(0,[z0,z2,z3,z329,z4,z5,z6]),(0,[z0,z2,z330,z3,z4,z5,z6]),(0,[z0,z2,z3,z43,z4,z21,z6])],[(0,[z0,z2,z3,z4,z331,z5,z6]),(0,[z0,z2,z162,z3,z4,z111,z6])]],
   [[(0,[z0,z2,z3,z332,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z333])],[(0,[z334,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z335,z6]),(0,[z0,z125,z2,z3,z336,z5,z6])],[(0,[z0,z2,z3,z337,z4,z5,z6]),(0,[z0,z338,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z339])],[(0,[z0,z2,z3,z4,z4,z5,z6]),(1,[z0,z2,z3,z5,z281,z6]),(0,[z0,z33,z2,z3,z4,z5,z174]),(0,[z0,z340,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z341,z6]),(0,[z62,z0,z13,z2,z3,z5,z6]),(0,[z272,z0,z2,z3,z4,z5,z106]),(0,[z0,z2,z342,z3,z4,z5,z6]),(1,[z0,z83,z2,z53,z5,z6]),(0,[z0,z15,z2,z3,z4,z5,z6])],[(0,[z27,z0,z2,z3,z5,z14,z6]),(0,[z0,z343,z2,z3,z4,z5,z6]),(0,[z0,z68,z2,z3,z4,z5,z6]),(0,[z0,z124,z2,z3,z4,z69,z6])],[(1,[z0,z344,z2,z4,z5,z6]),(1,[z0,z42,z3,z49,z5,z6]),(0,[z0,z2,z3,z4,z112,z70,z6]),(1,[z0,z2,z102,z4,z5,z103]),(0,[z0,z2,z3,z345,z4,z5,z6])],[(0,[z0,z2,z3,z4,z181,z5,z6]),(1,[z0,z2,z3,z4,z346,z5]),(0,[z0,z2,z3,z347,z4,z5,z6])]],
   [[(0,[z0,z348,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z112,z166,z6]),(0,[z0,z204,z142,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z349,z6])],[(0,[z0,z2,z3,z350,z4,z5,z6]),(0,[z0,z351,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z352])],[(0,[z0,z2,z3,z4,z5,z6,z353]),(0,[z0,z66,z2,z162,z4,z5,z6])],[(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z354,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z311,z6,z120]),(0,[z0,z2,z355,z3,z4,z5,z6]),(0,[z0,z2,z3,z356,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z357,z6])],[(0,[z0,z88,z3,z4,z5,z58,z6]),(0,[z0,z2,z3,z4,z5,z6,z358]),(0,[z0,z359,z2,z3,z4,z5,z6]),(0,[z0,z105,z2,z3,z4,z112,z6]),(0,[z0,z2,z360,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z361])],[(0,[z0,z2,z3,z4,z5,z6,z362]),(0,[z363,z0,z2,z3,z4,z5,z6]),(0,[z0,z364,z2,z3,z4,z5,z6]),(0,[z0,z365,z2,z3,z4,z5,z6]),(1,[z0,z48,z3,z4,z5,z233]),(0,[z0,z366,z2,z3,z4,z5,z6]),(0,[z0,z2,z367,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z368,z6]),(0,[z0,z369,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z370,z6]),(0,[z0,z2,z3,z371,z4,z5,z6])],[(0,[z0,z2,z372,z3,z4,z5,z6]),(0,[z0,z373,z2,z3,z4,z5,z6])],[(0,[z0,z2,z374,z3,z4,z5,z6]),(0,[z0,z2,z3,z375,z4,z5,z6]),(0,[z0,z2,z3,z376,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z377])],[(0,[z378,z0,z2,z3,z4,z5,z6]),(0,[z0,z295,z2,z3,z4,z5,z6]),(0,[z0,z379,z2,z3,z4,z5,z6])],[(0,[z0,z2,z380,z3,z4,z5,z6]),(0,[z0,z2,z3,z381,z4,z5,z6]),(0,[z0,z2,z382,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z383,z5,z6]),(0,[z0,z48,z3,z4,z5,z6,z233]),(0,[z0,z2,z3,z4,z384,z5,z6])],[(0,[z385,z0,z2,z3,z4,z5,z6]),(0,[z0,z124,z2,z3,z4,z174,z6]),(0,[z0,z2,z3,z4,z5,z6,z55])],[(0,[z386,z0,z2,z3,z4,z5,z6]),(0,[z0,z387,z2,z3,z4,z5,z6]),(0,[z0,z344,z2,z3,z4,z5,z6]),(1,[z0,z78,z2,z3,z4,z5]),(0,[z0,z2,z3,z388,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z389,z4,z5,z6]),(0,[z0,z48,z88,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z390,z6]),(0,[z0,z2,z3,z43,z4,z5,z6]),(0,[z0,z13,z2,z3,z16,z5,z6])],[(0,[z113,z2,z3,z18,z4,z5,z6]),(0,[z47,z0,z2,z3,z4,z5,z120]),(0,[z0,z2,z3,z4,z391,z5,z6]),(0,[z0,z2,z3,z4,z5,z174,z6]),(0,[z0,z2,z3,z392,z4,z5,z6]),(0,[z0,z2,z393,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z394,z5,z6])],[(0,[z395,z0,z2,z3,z4,z5,z6]),(0,[z113,z0,z2,z3,z4,z5,z396]),(0,[z0,z2,z3,z4,z397,z5,z6]),(0,[z0,z2,z3,z4,z398,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z233])],[(0,[z36,z0,z2,z3,z4,z5,z6]),(0,[z399,z0,z2,z3,z4,z5,z6]),(1,[z0,z142,z2,z3,z20,z6])],[(0,[z400,z0,z2,z3,z4,z5,z6]),(0,[z47,z0,z2,z3,z4,z5,z6]),(1,[z0,z33,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z401,z6])],[(1,[z0,z2,z3,z4,z5,z61]),(1,[z0,z2,z3,z4,z251,z6]),(0,[z0,z402,z2,z3,z4,z5,z6]),(0,[z0,z48,z2,z3,z4,z140,z5]),(0,[z0,z2,z403,z3,z4,z5,z6]),(0,[z0,z137,z2,z102,z4,z5,z6])],[(0,[z0,z2,z187,z3,z4,z5,z6]),(1,[z113,z2,z18,z4,z5,z6]),(0,[z0,z2,z3,z404,z4,z5,z6]),(0,[z0,z2,z405,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z406,z6]),(0,[z0,z42,z2,z3,z20,z5,z6]),(0,[z0,z2,z3,z4,z5,z58,z6])],[(0,[z0,z2,z3,z4,z5,z6,z126]),(0,[z407,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z61,z6]),(0,[z0,z2,z3,z4,z408,z5,z6]),(0,[z0,z2,z3,z4,z5,z409,z6]),(0,[z0,z2,z3,z4,z5,z410,z6]),(0,[z0,z137,z2,z3,z4,z5,z103]),(0,[z0,z2,z3,z4,z5,z6,z411])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z412]),(0,[z0,z2,z3,z4,z413,z5,z6])],[(0,[z113,z0,z414,z3,z4,z5,z6]),(0,[z0,z415,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z416,z4,z5,z6]),(0,[z0,z417,z2,z3,z4,z5,z6]),(0,[z0,z3,z16,z4,z261,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z418]),(0,[z0,z13,z2,z3,z4,z5,z104])],[(0,[z0,z2,z3,z4,z419,z5,z6]),(0,[z0,z2,z3,z4,z5,z420,z6]),(0,[z0,z2,z3,z356,z5,z174,z6]),(0,[z421,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z422,z6,z120]),(0,[z0,z2,z3,z4,z5,z6,z423]),(0,[z424,z0,z2,z3,z4,z5,z6])],[(0,[z0,z425,z2,z3,z4,z5,z6]),(0,[z144,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z65,z4,z49,z5,z6]),(1,[z0,z2,z162,z4,z111,z6])],[(0,[z0,z2,z3,z4,z5,z426,z6]),(0,[z0,z2,z3,z4,z427,z5,z6]),(0,[z0,z2,z3,z4,z5,z428,z6]),(0,[z429,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z430]),(0,[z0,z2,z3,z4,z5,z6,z431])],[(0,[z144,z0,z2,z18,z4,z5,z6]),(0,[z432,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z433,z6]),(0,[z0,z2,z3,z4,z5,z6,z434]),(0,[z0,z2,z3,z435,z4,z5,z6]),(0,[z0,z436,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z437,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z438,z4,z5,z6])],[(0,[z0,z439,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z440,z4,z5,z6])],[(0,[z0,z441,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z120]),(0,[z0,z83,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z166,z5,z150,z6]),(0,[z0,z442,z2,z3,z4,z5,z6])],[(0,[z0,z443,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z2,z3,z41,z4,z5,z6]),(1,[z0,z124,z3,z4,z174,z6]),(0,[z0,z2,z444,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z445])],[(0,[z36,z0,z38,z3,z4,z5,z6]),(0,[z0,z2,z184,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z446,z5,z6]),(0,[z0,z2,z447,z3,z4,z5,z6]),(0,[z272,z2,z3,z4,z5,z150,z6]),(0,[z0,z2,z3,z4,z5,z6,z448])],[(0,[z0,z88,z2,z3,z43,z5,z6]),(0,[z0,z266,z102,z3,z4,z5,z6]),(0,[z0,z449,z2,z3,z4,z5,z6]),(0,[z0,z2,z450,z3,z4,z5,z6])]],
   [[(0,[z451,z0,z2,z3,z4,z5,z6]),(0,[z113,z0,z2,z162,z4,z5,z6]),(0,[z0,z452,z2,z3,z4,z5,z6]),(0,[z453,z0,z2,z3,z4,z5,z6]),(0,[z454,z0,z2,z3,z4,z5,z6])],[(0,[z0,z455,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z396,z6]),(0,[z0,z2,z3,z4,z5,z6,z456]),(0,[z0,z2,z3,z4,z457,z5,z6]),(1,[z0,z125,z3,z4,z5,z58]),(0,[z0,z2,z3,z4,z5,z458,z6]),(0,[z0,z2,z459,z3,z4,z5,z6])],[(0,[z0,z48,z2,z3,z4,z5,z32]),(0,[z0,z40,z2,z129,z4,z5,z6])],[(0,[z38,z2,z184,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z460,z6]),(1,[z0,z2,z3,z461,z5,z6]),(0,[z0,z2,z3,z4,z462,z5,z6]),(0,[z0,z2,z3,z4,z140,z5,z55])],[(0,[z0,z344,z2,z4,z5,z6,z120])],[(0,[z36,z0,z48,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z463,z6]),(0,[z0,z2,z3,z4,z5,z6,z464]),(0,[z0,z2,z3,z4,z5,z465,z6])],[(0,[z113,z0,z2,z3,z4,z466,z6]),(0,[z0,z2,z3,z467,z4,z5,z6]),(0,[z0,z2,z468,z3,z4,z5,z6]),(0,[z0,z153,z3,z4,z5,z6,z120]),(0,[z0,z469,z2,z3,z4,z5,z6]),(0,[z0,z88,z2,z3,z65,z5,z6]),(0,[z0,z470,z2,z3,z4,z5,z6]),(0,[z0,z471,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z472,z5,z6])],[(0,[z0,z2,z149,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z473,z5,z6]),(0,[z0,z266,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z474]),(0,[z475,z0,z2,z3,z4,z5,z6]),(0,[z476,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z477,z4,z5,z6]),(0,[z0,z2,z3,z231,z41,z4,z5]),(0,[z0,z478,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z479])],[(0,[z480,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z481]),(0,[z0,z2,z3,z4,z5,z6,z482]),(0,[z0,z2,z3,z4,z5,z6,z483]),(0,[z0,z2,z3,z4,z5,z484,z6]),(0,[z0,z2,z3,z43,z5,z14,z6])],[(0,[z2,z187,z3,z18,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z485,z6]),(0,[z0,z2,z3,z4,z5,z486,z6]),(0,[z0,z2,z3,z4,z5,z487,z6]),(0,[z0,z2,z3,z4,z488,z5,z6]),(0,[z0,z489,z2,z3,z4,z5,z6])],[(0,[z113,z144,z2,z3,z4,z5,z6]),(0,[z0,z490,z2,z3,z4,z5,z6]),(0,[z0,z42,z2,z3,z49,z5,z6]),(0,[z0,z491,z2,z3,z4,z5,z6]),(0,[z0,z492,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z493,z6]),(0,[z0,z494,z2,z3,z4,z5,z6]),(0,[z0,z66,z2,z4,z112,z5,z6]),(0,[z0,z105,z2,z3,z4,z5,z55])],[(0,[z0,z2,z3,z4,z495,z5,z6]),(0,[z0,z2,z3,z4,z5,z311,z6]),(0,[z0,z214,z2,z3,z5,z6,z120]),(0,[z0,z496,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z497,z4,z5,z6])],[(0,[z0,z2,z3,z4,z498,z5,z6]),(0,[z62,z0,z2,z3,z28,z5,z6]),(0,[z165,z272,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z499])],[(1,[z0,z2,z3,z332,z5,z6]),(0,[z0,z2,z3,z500,z4,z5,z6])]],
   [[(0,[z0,z501,z2,z3,z18,z4,z6]),(0,[z212,z47,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z502,z4,z5,z6]),(0,[z0,z2,z3,z503,z4,z5,z6]),(0,[z0,z504,z2,z3,z4,z5,z6])],[(1,[z36,z184,z3,z4,z5,z6]),(0,[z505,z0,z2,z3,z4,z5,z6]),(0,[z0,z506,z2,z3,z4,z5,z6]),(0,[z0,z142,z2,z3,z20,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z507]),(0,[z0,z105,z2,z3,z4,z140,z6])],[(0,[z0,z2,z508,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z509,z5,z6]),(0,[z0,z2,z3,z4,z5,z510,z6])],[(0,[z36,z0,z3,z4,z5,z58,z6]),(0,[z144,z0,z2,z4,z5,z103,z6]),(0,[z0,z2,z3,z4,z5,z32,z55])],[(0,[z0,z511,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z512,z4,z5,z6])],[(0,[z0,z513,z2,z3,z4,z5,z6]),(0,[z0,z78,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z514,z5,z6]),(0,[z0,z2,z3,z515,z4,z5,z6]),(0,[z0,z48,z2,z3,z16,z4,z5]),(0,[z0,z2,z3,z4,z516,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z133]),(0,[z0,z13,z2,z3,z43,z5,z6]),(0,[z0,z2,z3,z517,z4,z5,z6]),(0,[z0,z2,z3,z518,z4,z5,z6])]],
   [[(0,[z519,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z520,z3,z4,z5,z6]),(0,[z0,z13,z2,z3,z95,z5,z6]),(0,[z0,z2,z162,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z4,z5,z6])],[(1,[z272,z2,z3,z4,z150,z6]),(0,[z0,z42,z3,z4,z49,z5,z6]),(0,[z0,z521,z2,z3,z4,z5,z6]),(0,[z0,z2,z84,z3,z53,z5,z6]),(0,[z0,z522,z2,z3,z4,z5,z6])],[(0,[z523,z0,z2,z3,z4,z5,z6]),(0,[z37,z38,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z28,z53,z5,z6]),(0,[z524,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z346,z5,z6]),(0,[z525,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z526,z5,z6]),(0,[z0,z2,z102,z3,z4,z5,z133]),(1,[z0,z2,z3,z4,z206,z6]),(0,[z0,z2,z3,z4,z140,z5,z6])],[(0,[z0,z2,z3,z527,z4,z5,z6]),(0,[z0,z528,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z529,z6])],[(0,[z0,z2,z414,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z530]),(0,[z0,z2,z3,z531,z4,z5,z6])],[(0,[z532,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z533,z4,z5,z6]),(0,[z0,z125,z2,z3,z4,z5,z58]),(0,[z0,z105,z2,z3,z4,z111,z6])],[(0,[z0,z13,z2,z3,z65,z5,z6]),(0,[z534,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z535,z4,z5,z6])],[(0,[z0,z536,z2,z3,z4,z5,z6]),(0,[z0,z81,z2,z3,z4,z5,z6]),(0,[z0,z2,z537,z3,z4,z5,z6]),(0,[z538,z0,z2,z3,z4,z5,z6]),(0,[z539,z0,z2,z3,z4,z5,z6]),(0,[z0,z540,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z541]),(0,[z0,z2,z102,z4,z5,z103,z6])]],
   [[(0,[z0,z2,z3,z4,z542,z5,z6]),(0,[z0,z2,z3,z4,z543,z5,z6]),(0,[z0,z2,z3,z4,z5,z150,z6]),(0,[z0,z544,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z545,z4,z5,z6]),(0,[z0,z546,z2,z3,z4,z5,z6]),(0,[z165,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z547]),(0,[z0,z548,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z549,z6]),(0,[z0,z2,z3,z550,z4,z5,z6])],[(0,[z113,z0,z2,z3,z235,z5,z6]),(0,[z0,z2,z3,z18,z4,z5,z6]),(0,[z0,z2,z3,z551,z4,z5,z6]),(0,[z0,z552,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z104])],[(0,[z0,z2,z3,z553,z4,z5,z6]),(1,[z62,z2,z3,z92,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z554]),(0,[z0,z2,z95,z4,z53,z5,z6]),(0,[z0,z2,z3,z4,z555,z5,z6])],[(0,[z36,z0,z184,z3,z4,z5,z6]),(0,[z0,z2,z556,z3,z4,z5,z6]),(0,[z0,z2,z3,z557,z4,z5,z6]),(0,[z0,z3,z4,z5,z51,z6,z120]),(0,[z0,z2,z3,z49,z5,z14,z6])],[(0,[z0,z558,z2,z3,z4,z5,z6]),(0,[z559,z0,z2,z3,z4,z5,z6]),(0,[z165,z0,z2,z3,z181,z5,z6]),(0,[z0,z42,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z560,z6]),(0,[z0,z2,z3,z500,z5,z174,z6]),(0,[z561,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z562,z5,z6]),(0,[z0,z563,z2,z3,z4,z5,z6])],[(1,[z0,z68,z2,z3,z4,z6]),(0,[z0,z564,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z565,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z566])],[(0,[z567,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z568]),(0,[z569,z0,z2,z3,z4,z5,z6])]],
   [[(1,[z0,z2,z3,z4,z5,z396]),(0,[z113,z0,z137,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z570,z6]),(0,[z0,z2,z3,z4,z5,z571,z6]),(0,[z0,z48,z125,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z572,z6])],[(0,[z0,z2,z3,z4,z5,z6,z114]),(0,[z0,z2,z3,z4,z5,z6,z573]),(0,[z27,z0,z2,z3,z28,z5,z6]),(0,[z0,z2,z3,z4,z574,z5,z6])],[(0,[z0,z575,z2,z3,z4,z5,z6]),(0,[z272,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z32,z6,z120]),(0,[z0,z2,z102,z3,z461,z5,z6])],[(0,[z165,z2,z3,z4,z166,z5,z6]),(0,[z0,z137,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z576])],[(0,[z577,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z578]),(0,[z0,z579,z2,z3,z4,z5,z6]),(0,[z0,z580,z2,z3,z4,z5,z6]),(0,[z0,z66,z2,z3,z4,z111,z6]),(0,[z0,z2,z3,z4,z111,z70,z6]),(0,[z0,z2,z3,z4,z5,z6,z581]),(0,[z0,z2,z3,z4,z5,z582,z6])],[(0,[z0,z2,z3,z4,z5,z70,z32]),(0,[z0,z48,z2,z102,z3,z4,z5]),(0,[z0,z2,z3,z583,z4,z5,z6])],[(1,[z0,z414,z3,z4,z5,z6]),(0,[z165,z0,z105,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z584,z6]),(0,[z0,z2,z3,z4,z5,z6,z585]),(0,[z586,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z173,z6]),(0,[z0,z587,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z588,z6]),(0,[z589,z0,z2,z3,z4,z5,z6]),(0,[z0,z142,z2,z3,z4,z21,z6])]],
   [[(0,[z113,z0,z2,z4,z112,z5,z6]),(0,[z0,z590,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z591,z5,z6])],[(0,[z0,z2,z3,z4,z251,z5,z6]),(1,[z0,z501,z2,z3,z4,z6]),(1,[z0,z3,z535,z4,z5,z6])],[(0,[z592,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z593,z5,z6]),(1,[z212,z2,z3,z4,z5,z32]),(0,[z594,z0,z2,z3,z4,z5,z6]),(0,[z0,z595,z2,z3,z4,z5,z6])],[(0,[z27,z0,z13,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z596,z6]),(0,[z0,z2,z3,z4,z5,z6,z597]),(0,[z0,z2,z3,z4,z5,z598,z6])],[(0,[z0,z2,z3,z599,z4,z5,z6]),(0,[z0,z2,z3,z600,z4,z5,z6]),(0,[z0,z601,z2,z3,z4,z5,z6]),(0,[z0,z2,z84,z3,z4,z5,z6]),(0,[z0,z2,z3,z95,z5,z14,z6]),(0,[z602,z0,z2,z3,z4,z5,z6]),(0,[z0,z603,z2,z3,z4,z5,z6])],[(1,[z27,z2,z3,z28,z5,z6]),(0,[z0,z604,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z605,z5,z6]),(0,[z0,z2,z606,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z607,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z608])],[(0,[z0,z2,z3,z4,z5,z609,z6]),(0,[z0,z610,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z466,z6]),(0,[z0,z48,z13,z2,z3,z4,z5]),(0,[z0,z2,z4,z112,z5,z111,z6]),(0,[z0,z2,z611,z3,z4,z5,z6]),(0,[z612,z0,z2,z3,z4,z5,z6])],[(0,[z144,z0,z2,z187,z4,z5,z6]),(0,[z0,z2,z3,z20,z92,z5,z6]),(0,[z0,z613,z2,z3,z4,z5,z6]),(0,[z272,z0,z105,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z614]),(0,[z0,z615,z2,z3,z4,z5,z6]),(1,[z0,z13,z2,z3,z5,z104]),(0,[z0,z2,z3,z16,z5,z14,z6])],[(0,[z616,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z617]),(0,[z0,z2,z3,z4,z140,z70,z6])],[(0,[z0,z2,z3,z618,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z619,z6]),(0,[z0,z2,z3,z4,z5,z620,z6])],[(0,[z0,z2,z3,z4,z5,z103,z120]),(0,[z0,z2,z621,z3,z4,z5,z6])],[(0,[z0,z622,z2,z3,z4,z5,z6]),(0,[z0,z501,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z623]),(0,[z0,z2,z3,z4,z346,z49,z5])],[(0,[z212,z2,z3,z4,z5,z32,z6]),(0,[z0,z74,z2,z129,z4,z5,z6]),(0,[z0,z2,z3,z624,z4,z5,z6]),(0,[z0,z48,z137,z2,z3,z4,z5]),(0,[z0,z2,z625,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z626,z6])],[(0,[z0,z2,z3,z4,z5,z103,z6]),(0,[z0,z2,z3,z4,z627,z5,z6])]],
   [[(1,[z0,z295,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z120,z133])],[(0,[z165,z0,z2,z3,z4,z70,z6]),(0,[z0,z2,z3,z4,z628,z5,z6]),(0,[z0,z2,z3,z4,z461,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z629]),(0,[z0,z2,z3,z4,z630,z5,z6]),(0,[z0,z2,z102,z3,z4,z206,z6])],[(0,[z0,z2,z3,z65,z92,z5,z6]),(0,[z0,z2,z631,z3,z4,z5,z6]),(0,[z165,z0,z2,z3,z4,z166,z6]),(0,[z0,z2,z3,z4,z5,z632,z6]),(0,[z0,z2,z3,z4,z5,z633,z6])],[(1,[z0,z2,z3,z4,z466,z6]),(0,[z0,z634,z2,z3,z4,z5,z6]),(0,[z635,z0,z2,z3,z4,z5,z6]),(0,[z636,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z637,z3,z4,z5,z6]),(0,[z0,z2,z3,z20,z28,z5,z6]),(0,[z62,z0,z2,z3,z92,z5,z6]),(0,[z0,z2,z3,z4,z638,z5,z6]),(0,[z0,z83,z2,z3,z95,z5,z6]),(0,[z0,z2,z3,z4,z639,z5,z6])],[(0,[z0,z2,z3,z640,z4,z5,z6]),(0,[z0,z2,z3,z4,z641,z5,z6])],[(0,[z2,z3,z92,z4,z28,z5,z6]),(0,[z0,z2,z3,z4,z5,z642,z6]),(0,[z0,z2,z3,z643,z4,z5,z6]),(0,[z0,z2,z3,z644,z4,z5,z6]),(0,[z0,z645,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z646,z5,z6]),(0,[z0,z124,z2,z3,z43,z4,z6])],[(0,[z0,z38,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z28,z5,z6]),(0,[z0,z2,z3,z4,z5,z647,z6]),(0,[z0,z2,z3,z4,z648,z5,z6]),(0,[z0,z142,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z649,z4,z5,z6]),(0,[z165,z0,z2,z3,z128,z5,z6]),(0,[z0,z2,z3,z4,z650,z5,z6]),(0,[z0,z125,z2,z3,z4,z5,z233]),(0,[z0,z2,z651,z3,z4,z5,z6]),(0,[z0,z102,z3,z535,z4,z5,z6])],[(0,[z272,z0,z2,z3,z4,z70,z6]),(0,[z0,z2,z3,z652,z4,z5,z6])],[(0,[z0,z653,z2,z3,z4,z5,z6]),(0,[z654,z0,z2,z3,z4,z5,z6]),(0,[z655,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z336,z5,z6])],[(0,[z0,z2,z3,z4,z5,z656,z6]),(0,[z272,z0,z2,z3,z4,z166,z6]),(0,[z0,z2,z3,z4,z112,z150,z6]),(1,[z0,z2,z3,z16,z5,z14])],[(0,[z0,z3,z4,z69,z5,z174,z6]),(0,[z0,z204,z3,z4,z69,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z657])],[(0,[z0,z2,z3,z65,z28,z5,z6]),(0,[z0,z2,z3,z4,z5,z422,z6]),(0,[z0,z40,z2,z3,z4,z5,z6]),(0,[z0,z48,z105,z2,z3,z4,z5]),(0,[z0,z2,z3,z658,z4,z5,z6])]],
   [[(0,[z659,z0,z2,z3,z4,z5,z6]),(0,[z0,z660,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z661]),(0,[z0,z2,z3,z662,z4,z5,z6]),(1,[z0,z88,z3,z65,z5,z6])],[(0,[z0,z2,z4,z93,z5,z150,z6]),(0,[z0,z2,z3,z4,z166,z111,z6]),(0,[z0,z168,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z663,z6]),(0,[z0,z2,z3,z4,z5,z6,z664])],[(0,[z37,z0,z2,z3,z4,z5,z126]),(0,[z144,z2,z187,z3,z4,z5,z6]),(0,[z0,z3,z4,z69,z5,z58,z6])],[(0,[z0,z2,z3,z665,z4,z5,z6]),(0,[z0,z204,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z666,z6]),(0,[z0,z13,z125,z2,z3,z4,z5])],[(0,[z0,z667,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z668,z6]),(0,[z0,z2,z669,z3,z4,z5,z6]),(0,[z670,z0,z2,z3,z4,z5,z6])],[(0,[z671,z0,z2,z3,z4,z5,z6]),(0,[z47,z2,z3,z4,z5,z6,z120]),(0,[z0,z2,z3,z95,z4,z5,z6])],[(0,[z113,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z672,z5,z6]),(0,[z0,z40,z129,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z673,z5,z6])]],
   [[(0,[z674,z0,z2,z3,z4,z5,z6])],[(0,[z36,z2,z184,z3,z4,z5,z6]),(0,[z0,z2,z675,z3,z4,z5,z6]),(0,[z676,z0,z2,z3,z4,z5,z6]),(0,[z0,z677,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z678,z4,z5,z6]),(0,[z0,z204,z2,z3,z43,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z679])],[(0,[z0,z2,z3,z4,z680,z5,z6]),(0,[z0,z681,z2,z3,z4,z5,z6]),(0,[z0,z125,z2,z3,z4,z5,z120]),(0,[z0,z2,z682,z3,z4,z5,z6])],[(0,[z144,z0,z2,z162,z4,z5,z6]),(1,[z0,z2,z3,z4,z422,z6]),(0,[z0,z3,z41,z4,z5,z58,z6])],[(0,[z0,z2,z3,z4,z683,z5,z6]),(0,[z0,z2,z3,z92,z53,z5,z6]),(0,[z0,z2,z3,z4,z684,z5,z6]),(0,[z0,z2,z3,z159,z4,z5,z6]),(0,[z0,z2,z685,z3,z4,z5,z6])],[(0,[z0,z686,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z92,z49,z5,z6]),(0,[z212,z0,z2,z3,z4,z5,z120]),(1,[z0,z2,z3,z231,z4,z5]),(0,[z0,z125,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z28,z49,z5,z6]),(0,[z0,z2,z3,z4,z150,z111,z6]),(0,[z0,z2,z687,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z273,z6]),(0,[z0,z2,z3,z4,z688,z5,z6]),(0,[z0,z2,z3,z4,z182,z49,z6]),(0,[z0,z13,z2,z3,z5,z6,z104])]],
   [[(1,[z0,z2,z3,z235,z5,z6]),(0,[z0,z2,z3,z4,z5,z689,z6]),(0,[z212,z0,z2,z3,z4,z5,z6]),(0,[z0,z690,z2,z3,z4,z5,z6]),(0,[z691,z0,z2,z3,z4,z5,z6])],[(0,[z37,z0,z2,z3,z4,z5,z6]),(0,[z27,z0,z2,z3,z92,z5,z6]),(0,[z0,z2,z3,z4,z5,z692,z6]),(1,[z0,z2,z3,z356,z5,z6]),(0,[z0,z2,z3,z693,z4,z5,z6]),(1,[z0,z2,z3,z222,z5,z6])],[(0,[z0,z40,z38,z3,z4,z5,z6])],[(0,[z0,z2,z3,z694,z4,z5,z6]),(0,[z0,z2,z3,z4,z695,z5,z6]),(0,[z0,z696,z2,z3,z4,z5,z6]),(1,[z0,z2,z84,z95,z5,z6]),(0,[z0,z2,z697,z3,z4,z5,z6])],[(0,[z0,z2,z3,z698,z4,z5,z6]),(1,[z0,z2,z3,z500,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z699]),(0,[z0,z2,z3,z4,z5,z6,z700])],[(0,[z36,z0,z2,z3,z332,z5,z6]),(0,[z0,z2,z701,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z273]),(0,[z0,z2,z3,z702,z4,z5,z6]),(0,[z703,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z336,z4,z5,z6]),(0,[z0,z704,z2,z3,z4,z5,z6]),(0,[z0,z705,z2,z3,z4,z5,z6]),(1,[z0,z155,z3,z4,z5,z6])],[(1,[z0,z214,z2,z3,z5,z6]),(0,[z0,z105,z2,z3,z4,z5,z6]),(0,[z706,z0,z2,z3,z4,z5,z6])],[]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z37,z38,z3,z4,z5,z61]),(0,[z0,z2,z4,z707,z5,z6])],[(0,[z0,z708,z3,z4,z5,z6]),(0,[z47,z2,z3,z4,z5,z120]),(0,[z0,z2,z3,z4,z5,z709]),(0,[z0,z2,z3,z4,z5,z710]),(0,[z0,z2,z3,z4,z5,z711]),(0,[z0,z2,z3,z4,z5,z712])],[(0,[z0,z3,z4,z5,z51,z6]),(0,[z0,z2,z3,z4,z5,z713]),(0,[z0,z2,z3,z43,z52,z6]),(0,[z0,z137,z2,z4,z5,z714])],[(0,[z0,z2,z3,z4,z466,z6]),(0,[z0,z414,z3,z4,z251,z6]),(0,[z0,z2,z3,z4,z715,z6]),(0,[z0,z2,z3,z4,z5,z716]),(0,[z0,z3,z717,z4,z5,z6]),(0,[z0,z2,z102,z461,z5,z103])],[(0,[z113,z414,z18,z4,z5,z6]),(0,[z0,z2,z3,z718,z5,z6])],[(0,[z113,z2,z18,z4,z251,z6]),(0,[z0,z13,z2,z3,z5,z585]),(0,[z0,z2,z3,z5,z6,z719])],[(0,[z0,z2,z720,z4,z5,z6]),(0,[z0,z2,z3,z721,z5,z6]),(0,[z0,z2,z3,z722,z5,z6]),(0,[z0,z2,z3,z4,z5,z723])],[(0,[z0,z2,z3,z5,z724,z126]),(0,[z0,z2,z508,z95,z5,z6]),(0,[z0,z66,z2,z515,z4,z6]),(0,[z0,z74,z41,z4,z5,z6])]],
   [[(0,[z165,z540,z2,z3,z4,z6]),(0,[z0,z725,z3,z4,z5,z6]),(0,[z0,z105,z2,z3,z4,z55])],[(0,[z0,z2,z3,z4,z5,z726]),(0,[z0,z2,z3,z727,z5,z6]),(0,[z0,z2,z3,z728,z4,z5]),(0,[z0,z2,z3,z5,z6,z729])],[(0,[z0,z2,z3,z730,z5,z6])],[(0,[z0,z731,z2,z3,z4,z6]),(0,[z0,z2,z3,z732,z5,z6]),(0,[z0,z105,z2,z3,z4,z106]),(0,[z0,z3,z4,z5,z733,z6])],[(0,[z602,z0,z2,z162,z4,z6]),(0,[z0,z2,z3,z16,z5,z14])],[(0,[z0,z2,z3,z4,z734,z6]),(0,[z0,z81,z74,z41,z4,z5])],[(0,[z0,z2,z4,z735,z5,z6]),(0,[z0,z736,z2,z4,z5,z6]),(0,[z318,z2,z3,z92,z5,z6]),(0,[z0,z125,z3,z4,z261,z5])],[(0,[z0,z168,z2,z3,z4,z6]),(0,[z0,z42,z2,z3,z182,z6]),(0,[z0,z737,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z738,z6]),(0,[z0,z2,z3,z739,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z740,z6]),(0,[z0,z2,z3,z4,z741,z6]),(0,[z0,z2,z3,z742,z5,z6])],[(0,[z0,z2,z3,z4,z743,z6]),(0,[z0,z3,z4,z5,z6,z54]),(0,[z0,z2,z3,z159,z160,z6])],[(0,[z0,z744,z2,z3,z4,z5]),(0,[z0,z604,z3,z49,z5,z6]),(0,[z0,z2,z3,z4,z745,z6]),(0,[z0,z48,z214,z2,z3,z5]),(0,[z0,z74,z231,z41,z4,z5]),(0,[z0,z746,z2,z3,z4,z6])],[],[(0,[z0,z295,z3,z4,z251,z6]),(0,[z539,z2,z3,z28,z5,z6]),(0,[z0,z2,z3,z4,z747,z6]),(0,[z0,z125,z2,z3,z4,z206])],[(0,[z0,z2,z3,z5,z724,z6]),(0,[z113,z295,z18,z4,z5,z6]),(0,[z0,z2,z4,z112,z259,z6]),(0,[z2,z3,z4,z5,z748,z120]),(0,[z0,z344,z2,z4,z5,z103]),(0,[z0,z2,z3,z4,z182,z6]),(0,[z0,z13,z3,z261,z5,z6])],[(0,[z0,z2,z3,z749,z5,z6]),(0,[z0,z2,z3,z750,z5,z6]),(0,[z0,z2,z3,z4,z751,z6]),(0,[z0,z2,z3,z4,z752,z6]),(0,[z0,z125,z3,z4,z5,z626]),(0,[z0,z2,z3,z4,z5,z753])],[(0,[z0,z2,z3,z4,z160,z6]),(0,[z0,z754,z2,z3,z4,z6])]],
   [[(0,[z2,z3,z4,z166,z734,z6]),(0,[z2,z3,z4,z5,z748,z6]),(0,[z0,z2,z3,z20,z315,z6])],[(0,[z113,z2,z18,z4,z466,z6]),(0,[z0,z2,z3,z755,z5,z6]),(0,[z0,z3,z388,z49,z5,z6]),(0,[z0,z2,z3,z4,z5,z756])],[(0,[z0,z2,z3,z4,z757,z6]),(0,[z0,z2,z3,z4,z422,z6]),(0,[z0,z2,z3,z758,z5,z6])],[(0,[z0,z2,z759,z4,z5,z6]),(0,[z0,z48,z3,z4,z5,z712]),(1,[z0,z2,z4,z5,z714]),(0,[z0,z3,z535,z461,z5,z6])],[(0,[z0,z48,z382,z3,z4,z5])],[(0,[z144,z0,z2,z17,z4,z6]),(0,[z0,z3,z4,z5,z760,z6]),(0,[z0,z2,z3,z4,z70,z106]),(0,[z0,z2,z3,z761,z5,z6]),(0,[z0,z3,z5,z6,z218,z54])],[(0,[z0,z204,z3,z4,z69,z6]),(0,[z0,z13,z2,z3,z136,z5])],[(0,[z0,z2,z3,z235,z5,z6]),(0,[z0,z2,z3,z762,z5,z6]),(0,[z0,z125,z3,z535,z4,z5])]],
   [[(0,[z0,z2,z3,z199,z5,z6]),(0,[z0,z2,z763,z4,z5,z6]),(0,[z0,z2,z3,z4,z764,z6]),(0,[z0,z2,z765,z4,z5,z6]),(0,[z0,z766,z2,z3,z5,z106]),(0,[z0,z48,z3,z4,z5,z51]),(0,[z0,z2,z3,z767,z5,z6]),(0,[z0,z2,z3,z4,z5,z768]),(0,[z0,z2,z3,z222,z5,z6])],[(0,[z0,z2,z3,z4,z769,z6]),(0,[z0,z155,z3,z4,z5,z120]),(0,[z0,z2,z3,z4,z6,z770])],[(0,[z635,z2,z3,z28,z5,z6]),(0,[z0,z2,z84,z95,z5,z6]),(1,[z0,z2,z3,z771,z6])],[(0,[z0,z2,z3,z772,z5,z6]),(0,[z0,z2,z773,z4,z5,z6]),(0,[z0,z2,z3,z500,z5,z6]),(0,[z0,z2,z3,z20,z6,z339])],[(0,[z37,z774,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z775]),(0,[z602,z2,z3,z4,z150,z6]),(0,[z0,z155,z3,z4,z5,z6])],[],[(0,[z0,z776,z3,z4,z5,z6]),(0,[z0,z777,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z778,z106]),(0,[z0,z214,z3,z5,z51,z6]),(0,[z0,z3,z4,z346,z5,z58]),(0,[z0,z2,z3,z5,z6,z218])],[(0,[z0,z2,z3,z4,z5,z779])]],
   [[(0,[z0,z780,z2,z3,z4,z6]),(0,[z0,z68,z2,z3,z4,z346])],[],[(0,[z0,z2,z3,z4,z5,z781]),(0,[z0,z782,z2,z3,z5,z126]),(0,[z2,z3,z783,z4,z5,z6]),(0,[z0,z48,z601,z3,z4,z5]),(0,[z0,z3,z4,z5,z58,z712])],[(0,[z0,z784,z2,z4,z5,z6]),(0,[z157,z2,z3,z4,z5,z32]),(0,[z0,z2,z3,z4,z785,z6]),(1,[z0,z2,z786,z5,z6]),(0,[z0,z3,z4,z5,z6,z787])],[],[(0,[z0,z2,z3,z4,z5,z788]),(0,[z0,z3,z4,z5,z6,z789]),(0,[z0,z790,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z791]),(0,[z2,z783,z18,z4,z5,z6]),(0,[z792,z2,z3,z4,z5,z6])],[(0,[z0,z793,z2,z3,z4,z5]),(0,[z47,z153,z3,z4,z5,z120]),(0,[z794,z2,z3,z4,z5,z6]),(0,[z0,z48,z3,z4,z182,z6]),(0,[z0,z125,z2,z3,z159,z5])]],
   [[],[(0,[z47,z2,z4,z5,z311,z120]),(0,[z0,z2,z786,z53,z5,z6]),(0,[z0,z2,z3,z4,z5,z714]),(0,[z0,z795,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z753])],[(0,[z0,z2,z3,z796,z5,z6]),(0,[z0,z2,z3,z4,z5,z797]),(0,[z0,z2,z3,z4,z798,z6]),(0,[z0,z2,z3,z799,z4,z6]),(0,[z0,z2,z800,z4,z5,z6]),(0,[z0,z3,z535,z4,z206,z6]),(0,[z0,z2,z3,z4,z140,z801])],[(0,[z0,z2,z802,z4,z5,z6]),(0,[z0,z2,z3,z231,z5,z803])],[(0,[z0,z2,z804,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z805]),(0,[z0,z15,z3,z16,z5,z14])],[(0,[z0,z2,z3,z4,z806,z6]),(0,[z0,z2,z3,z807,z5,z6]),(0,[z0,z48,z367,z3,z4,z5])],[(0,[z0,z2,z3,z4,z808,z5]),(0,[z0,z2,z3,z4,z809,z6]),(0,[z0,z810,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z6,z811]),(0,[z0,z2,z4,z786,z5,z6]),(0,[z0,z266,z3,z4,z160,z6]),(0,[z0,z2,z3,z5,z14,z753])]],
   [[(0,[z0,z782,z2,z3,z5,z6]),(0,[z0,z2,z812,z4,z5,z6]),(0,[z0,z2,z3,z4,z813,z6]),(0,[z0,z2,z3,z346,z5,z14])],[(0,[z0,z2,z3,z814,z5,z6]),(0,[z0,z2,z3,z4,z6,z815]),(0,[z0,z81,z2,z3,z4,z5]),(0,[z0,z3,z4,z5,z6,z712])],[(0,[z0,z48,z3,z199,z5,z6]),(0,[z0,z2,z816,z4,z5,z6]),(0,[z2,z3,z4,z734,z5,z6]),(0,[z0,z2,z3,z5,z803,z6])],[(0,[z0,z2,z3,z817,z5,z6]),(0,[z325,z184,z3,z4,z5,z6]),(0,[z0,z2,z4,z422,z311,z6]),(0,[z0,z3,z818,z49,z5,z6])],[(0,[z0,z344,z168,z2,z4,z6])],[(0,[z0,z819,z3,z4,z5,z6]),(0,[z0,z546,z3,z65,z5,z6]),(0,[z0,z2,z3,z4,z5,z820])],[(0,[z0,z414,z3,z4,z5,z396]),(0,[z0,z821,z2,z3,z4,z5]),(0,[z0,z2,z4,z93,z5,z6]),(0,[z0,z2,z3,z43,z23,z6])],[(0,[z0,z2,z3,z4,z251,z396]),(0,[z0,z3,z822,z4,z5,z6]),(0,[z0,z137,z2,z4,z5,z133])]],
   [[(0,[z0,z2,z3,z4,z5,z823]),(0,[z113,z2,z18,z4,z5,z396]),(0,[z538,z2,z3,z4,z5,z120]),(0,[z0,z2,z3,z5,z6,z753])],[(0,[z0,z2,z3,z127,z5,z6]),(0,[z0,z2,z3,z824,z5,z6]),(0,[z0,z2,z4,z5,z311,z6]),(0,[z0,z214,z168,z2,z3,z6]),(0,[z0,z2,z3,z786,z5,z6]),(0,[z0,z2,z3,z4,z825,z6]),(0,[z0,z826,z3,z4,z5,z6]),(0,[z0,z2,z3,z43,z21,z6])],[(0,[z0,z2,z149,z4,z111,z6]),(0,[z0,z2,z3,z5,z6,z827]),(0,[z0,z64,z2,z4,z112,z6]),(0,[z47,z344,z2,z4,z5,z120]),(0,[z0,z3,z4,z5,z58,z464]),(0,[z0,z66,z2,z4,z112,z6])],[(0,[z0,z828,z3,z4,z5,z6]),(0,[z0,z3,z4,z261,z5,z6])],[],[(0,[z774,z184,z3,z4,z5,z6]),(0,[z0,z124,z3,z356,z174,z6]),(0,[z0,z2,z3,z5,z6,z829])],[(0,[z0,z2,z3,z4,z5,z126]),(0,[z0,z2,z3,z4,z5,z830]),(0,[z0,z2,z3,z4,z831,z6]),(0,[z0,z2,z3,z231,z832,z5])],[(0,[z0,z2,z3,z5,z833,z6]),(0,[z0,z13,z2,z3,z5,z46]),(1,[z2,z3,z834,z5,z6]),(1,[z0,z3,z818,z5,z6]),(0,[z0,z835,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z149,z4,z5,z6]),(0,[z0,z153,z3,z4,z422,z6]),(0,[z0,z2,z3,z818,z5,z6])],[(0,[z0,z3,z199,z5,z58,z6]),(0,[z0,z2,z3,z4,z836,z6]),(0,[z0,z2,z4,z5,z6,z837]),(0,[z0,z2,z3,z422,z281,z6]),(0,[z0,z2,z3,z4,z140,z70])],[(0,[z0,z2,z3,z4,z838,z6]),(0,[z0,z2,z3,z839,z4,z5]),(0,[z0,z2,z3,z840,z5,z6])],[(0,[z36,z184,z3,z332,z5,z6]),(0,[z0,z2,z3,z4,z841,z6])],[(0,[z0,z2,z3,z235,z5,z114]),(0,[z144,z2,z4,z5,z549,z6]),(0,[z0,z2,z3,z842,z5,z6])],[(0,[z0,z142,z2,z3,z771,z6]),(0,[z0,z2,z3,z20,z771,z6])],[(0,[z7,z2,z3,z92,z5,z6]),(0,[z0,z843,z3,z4,z5,z106]),(0,[z844,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z159,z5,z6])],[(0,[z0,z2,z3,z4,z845,z6]),(0,[z0,z295,z3,z4,z5,z396]),(0,[z0,z2,z3,z4,z5,z846]),(0,[z0,z2,z3,z4,z847,z6]),(0,[z0,z2,z3,z5,z281,z6]),(0,[z0,z48,z3,z4,z5,z358]),(0,[z0,z2,z3,z4,z216,z70]),(0,[z0,z2,z848,z4,z5,z6])]],
   [[(0,[z0,z78,z2,z3,z4,z182]),(0,[z0,z83,z2,z53,z5,z6]),(0,[z0,z102,z535,z4,z5,z103])],[(0,[z0,z3,z4,z849,z5,z6]),(0,[z165,z2,z3,z4,z166,z6]),(0,[z429,z2,z3,z4,z166,z6]),(0,[z0,z3,z4,z5,z850,z6]),(0,[z0,z851,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z714,z133]),(0,[z0,z2,z4,z5,z6,z714]),(0,[z0,z105,z2,z3,z4,z801]),(0,[z0,z155,z3,z4,z140,z5])],[(0,[z0,z137,z2,z4,z5,z114])],[(0,[z0,z852,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z466,z396]),(0,[z0,z2,z3,z4,z5,z853]),(0,[z0,z2,z3,z4,z854,z6]),(0,[z0,z2,z3,z4,z855,z6])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z856,z5,z6]),(0,[z0,z2,z3,z857,z5,z6])],[(0,[z165,z2,z3,z181,z166,z6]),(0,[z0,z2,z3,z4,z858,z6]),(0,[z0,z859,z2,z4,z5,z6]),(0,[z0,z105,z3,z4,z54,z55])],[(0,[z0,z2,z3,z860,z5,z6]),(0,[z0,z3,z4,z818,z5,z6]),(0,[z0,z2,z450,z95,z5,z6]),(0,[z2,z3,z4,z5,z6,z861])],[]],
   [[(0,[z0,z2,z3,z4,z862,z6]),(0,[z0,z2,z3,z181,z5,z6]),(0,[z62,z2,z3,z834,z5,z6]),(0,[z0,z2,z102,z4,z160,z103])],[(0,[z38,z774,z3,z4,z5,z6]),(0,[z0,z863,z3,z4,z5,z6]),(0,[z0,z864,z3,z4,z5,z6]),(0,[z0,z403,z41,z4,z5,z6]),(0,[z0,z88,z3,z643,z5,z6]),(1,[z0,z2,z3,z4,z801]),(0,[z0,z105,z155,z3,z4,z5])],[(0,[z0,z414,z3,z4,z466,z6]),(0,[z0,z865,z3,z4,z5,z6]),(0,[z0,z33,z124,z3,z4,z174])],[(0,[z0,z48,z344,z2,z4,z5]),(0,[z0,z48,z168,z2,z3,z4]),(0,[z0,z344,z2,z4,z422,z6]),(0,[z0,z48,z3,z4,z5,z233]),(0,[z0,z2,z3,z866,z5,z6])],[(0,[z0,z153,z168,z3,z4,z6]),(0,[z0,z3,z867,z4,z5,z6]),(0,[z0,z42,z3,z346,z49,z5]),(0,[z0,z3,z65,z818,z5,z6]),(0,[z0,z2,z3,z4,z868,z6]),(0,[z0,z2,z4,z112,z869,z6])],[(0,[z0,z2,z3,z870,z5,z6]),(0,[z0,z871,z3,z4,z5,z6]),(0,[z0,z78,z42,z3,z49,z5])],[(0,[z0,z425,z41,z4,z5,z6]),(0,[z0,z2,z3,z872,z5,z6]),(0,[z27,z2,z3,z834,z5,z6])],[(0,[z0,z280,z2,z3,z20,z6])]],
   [[(0,[z0,z48,z3,z4,z5,z126])],[],[(0,[z0,z2,z3,z873,z5,z6]),(0,[z519,z0,z2,z162,z4,z6]),(0,[z27,z286,z2,z3,z5,z6])],[],[(0,[z0,z2,z874,z4,z5,z6]),(0,[z0,z875,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z876]),(0,[z0,z42,z3,z639,z5,z6]),(0,[z0,z2,z3,z4,z801,z55])],[(0,[z0,z2,z3,z4,z877,z6]),(0,[z0,z2,z3,z5,z6,z878]),(0,[z272,z2,z3,z4,z150,z273]),(0,[z0,z2,z3,z879,z5,z6]),(0,[z0,z2,z880,z3,z4,z5]),(0,[z0,z881,z3,z4,z5,z6])],[(0,[z0,z2,z3,z882,z5,z6]),(0,[z0,z155,z3,z4,z5,z32]),(0,[z0,z2,z3,z182,z14,z6])],[(0,[z0,z168,z2,z4,z311,z6]),(0,[z0,z124,z3,z4,z173,z174])]],
   [[(0,[z0,z2,z3,z4,z5,z883]),(0,[z0,z2,z884,z4,z5,z6]),(0,[z37,z3,z4,z5,z668,z6]),(0,[z0,z885,z3,z4,z5,z6]),(0,[z0,z48,z3,z4,z5,z434]),(0,[z0,z2,z4,z869,z111,z6]),(0,[z0,z3,z16,z261,z5,z14])],[(0,[z0,z2,z3,z4,z5,z61]),(0,[z0,z2,z162,z4,z466,z6]),(0,[z0,z886,z3,z4,z5,z6])],[(0,[z0,z2,z3,z887,z5,z6]),(0,[z0,z2,z888,z4,z5,z6]),(0,[z0,z889,z2,z3,z4,z5]),(0,[z0,z125,z3,z4,z5,z712])],[(0,[z0,z295,z3,z4,z466,z6]),(0,[z0,z168,z125,z2,z3,z4])],[(0,[z0,z3,z4,z5,z712,z233])],[(0,[z0,z2,z3,z4,z5,z173]),(1,[z0,z2,z4,z869,z6])],[(0,[z0,z2,z3,z4,z890,z6]),(0,[z0,z2,z3,z127,z5,z114]),(0,[z0,z2,z3,z4,z5,z891]),(0,[z0,z266,z3,z159,z5,z6]),(0,[z0,z13,z2,z3,z5,z352])],[(0,[z0,z3,z4,z5,z58,z126]),(0,[z0,z125,z3,z4,z5,z51]),(0,[z0,z153,z4,z5,z311,z6]),(0,[z0,z892,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z893,z6]),(1,[z774,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z894]),(0,[z0,z895,z2,z3,z4,z6]),(0,[z0,z2,z3,z896,z5,z6])],[(0,[z0,z2,z3,z4,z897,z5]),(0,[z0,z2,z183,z4,z111,z6]),(0,[z0,z898,z2,z3,z4,z5]),(1,[z0,z2,z3,z5,z753])],[],[],[(0,[z0,z2,z3,z899,z5,z6]),(0,[z0,z900,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z6,z901]),(0,[z0,z266,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z902,z6])],[(0,[z0,z903,z2,z4,z5,z6])],[(0,[z0,z414,z3,z235,z5,z6]),(0,[z0,z904,z2,z3,z4,z6]),(0,[z0,z33,z124,z3,z4,z5]),(0,[z0,z105,z2,z3,z222,z55])],[(0,[z0,z2,z3,z235,z251,z6]),(0,[z0,z2,z3,z834,z5,z6]),(0,[z0,z766,z2,z3,z5,z6]),(0,[z0,z905,z3,z4,z5,z6])]],
   [[(0,[z113,z2,z18,z235,z5,z6]),(0,[z165,z0,z2,z149,z4,z6]),(0,[z0,z2,z3,z4,z906,z6]),(0,[z0,z2,z3,z4,z5,z907]),(0,[z0,z33,z2,z3,z356,z5]),(0,[z0,z105,z2,z3,z4,z409]),(0,[z0,z615,z2,z3,z43,z6])],[(0,[z0,z48,z3,z4,z5,z474]),(0,[z0,z3,z4,z5,z6,z908])],[(0,[z165,z2,z3,z128,z166,z6]),(0,[z0,z48,z3,z4,z5,z482]),(0,[z0,z2,z3,z684,z5,z14]),(0,[z0,z909,z2,z3,z4,z5])],[(0,[z0,z2,z3,z910,z5,z6])],[(0,[z0,z2,z3,z911,z5,z6]),(0,[z0,z2,z912,z4,z5,z6]),(0,[z0,z15,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z913,z5]),(0,[z0,z914,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z915]),(0,[z0,z2,z3,z916,z5,z6]),(0,[z0,z2,z3,z128,z5,z6]),(0,[z0,z2,z3,z5,z778,z6]),(0,[z0,z2,z3,z917,z5,z6]),(0,[z0,z153,z3,z5,z281,z6]),(0,[z0,z124,z3,z4,z639,z6]),(0,[z0,z125,z3,z4,z5,z58]),(0,[z0,z2,z102,z392,z4,z5]),(0,[z0,z2,z3,z4,z6,z918])],[(0,[z0,z2,z3,z919,z5,z6]),(0,[z0,z42,z3,z182,z49,z6]),(0,[z0,z48,z13,z3,z49,z5]),(0,[z0,z204,z3,z4,z920,z6]),(0,[z0,z105,z155,z3,z4,z55])],[(0,[z0,z344,z2,z4,z5,z114]),(0,[z272,z2,z4,z93,z150,z6])]],
   [[(0,[z0,z2,z3,z921,z5,z6]),(0,[z0,z2,z3,z136,z5,z6]),(0,[z0,z2,z3,z4,z5,z922]),(0,[z0,z2,z3,z5,z14,z479])],[(0,[z0,z2,z3,z4,z5,z114]),(0,[z272,z2,z3,z4,z150,z106]),(0,[z0,z78,z68,z2,z3,z4])],[(0,[z0,z153,z3,z4,z5,z6]),(0,[z424,z2,z3,z4,z5,z32]),(0,[z0,z2,z923,z4,z5,z6]),(0,[z0,z48,z2,z3,z4,z206])],[(0,[z0,z2,z3,z924,z5,z6]),(0,[z925,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z869,z6]),(0,[z0,z3,z4,z5,z6,z926])],[(0,[z31,z2,z3,z92,z5,z6]),(0,[z0,z153,z344,z4,z5,z6]),(0,[z0,z105,z2,z3,z4,z541]),(0,[z0,z3,z261,z5,z14,z6])],[(0,[z0,z3,z49,z5,z314,z6]),(0,[z0,z2,z3,z461,z160,z6])],[(0,[z0,z2,z4,z5,z103,z322]),(0,[z47,z2,z3,z4,z5,z748]),(0,[z0,z344,z125,z2,z4,z5]),(0,[z0,z2,z3,z4,z5,z801])],[(0,[z0,z295,z3,z235,z5,z6]),(0,[z0,z927,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z928]),(0,[z0,z2,z3,z4,z5,z929]),(0,[z0,z930,z3,z4,z5,z6]),(0,[z0,z105,z2,z3,z218,z55])]],
   [[(0,[z0,z2,z3,z4,z931,z6]),(0,[z0,z3,z4,z932,z5,z6])],[(0,[z0,z2,z3,z4,z933,z6])],[(0,[z0,z2,z3,z934,z5,z6]),(0,[z272,z0,z2,z149,z4,z6])],[(0,[z0,z2,z3,z5,z6,z935]),(0,[z0,z2,z3,z936,z5,z6]),(0,[z0,z2,z3,z28,z182,z6]),(0,[z0,z2,z3,z4,z5,z937]),(0,[z0,z124,z3,z500,z174,z6])],[(0,[z0,z2,z3,z5,z938,z6])],[(0,[z0,z2,z3,z4,z140,z110])],[(0,[z0,z939,z2,z3,z4,z6]),(0,[z0,z2,z3,z940,z5,z6]),(0,[z0,z2,z3,z771,z4,z6])],[(0,[z0,z2,z3,z4,z5,z941]),(0,[z47,z214,z2,z3,z5,z120]),(0,[z0,z2,z102,z159,z5,z103])]],
   [[(0,[z0,z2,z3,z4,z5,z942]),(0,[z0,z2,z3,z943,z5,z6]),(0,[z0,z2,z3,z4,z5,z944]),(0,[z0,z344,z2,z5,z281,z6]),(0,[z0,z2,z3,z945,z5,z6]),(0,[z0,z2,z946,z4,z5,z6]),(0,[z0,z2,z3,z159,z206,z6])],[],[(0,[z0,z2,z947,z4,z5,z6]),(0,[z0,z2,z94,z4,z5,z103])],[(0,[z0,z3,z948,z4,z5,z6]),(0,[z0,z949,z3,z4,z5,z6]),(0,[z0,z48,z3,z4,z488,z5]),(0,[z0,z2,z3,z950,z5,z6]),(0,[z0,z2,z4,z5,z103,z714])],[(0,[z0,z13,z2,z3,z182,z6])],[(0,[z0,z344,z2,z4,z5,z6]),(0,[z0,z42,z3,z49,z5,z6]),(0,[z0,z2,z102,z4,z5,z103]),(0,[z0,z13,z2,z3,z5,z753])],[(0,[z0,z2,z3,z951,z5,z6]),(0,[z0,z2,z3,z4,z346,z5]),(0,[z0,z2,z3,z4,z206,z6]),(0,[z0,z2,z3,z4,z5,z952])],[(0,[z0,z2,z3,z4,z5,z953]),(0,[z0,z2,z3,z954,z5,z6])]],
   [[(0,[z0,z2,z3,z955,z5,z6]),(0,[z0,z2,z3,z956,z5,z6])],[(0,[z0,z2,z3,z957,z5,z6]),(0,[z0,z2,z3,z127,z251,z6]),(0,[z0,z2,z4,z112,z466,z6]),(0,[z2,z3,z834,z28,z5,z6]),(0,[z0,z2,z4,z958,z5,z6]),(0,[z0,z168,z2,z3,z281,z6]),(0,[z0,z2,z959,z4,z5,z6])],[(0,[z113,z2,z18,z127,z5,z6]),(0,[z0,z2,z3,z960,z5,z6]),(0,[z0,z48,z3,z136,z5,z6])],[(0,[z0,z168,z2,z3,z4,z70]),(0,[z0,z3,z231,z535,z4,z5]),(0,[z0,z2,z3,z4,z182,z346]),(0,[z0,z209,z2,z3,z43,z6]),(0,[z0,z83,z2,z786,z5,z6])],[(0,[z0,z68,z42,z3,z49,z6]),(0,[z0,z2,z3,z4,z5,z961])],[(0,[z36,z184,z3,z199,z5,z6]),(0,[z0,z2,z4,z5,z6,z962]),(0,[z0,z963,z2,z3,z4,z5]),(0,[z0,z2,z3,z964,z5,z6])],[(0,[z0,z965,z2,z3,z5,z6]),(0,[z0,z2,z3,z966,z5,z6])],[(0,[z0,z2,z4,z5,z6,z967]),(0,[z0,z3,z4,z5,z968,z6]),(0,[z0,z969,z3,z4,z5,z6])]],
   [[(0,[z0,z774,z3,z4,z5,z6]),(0,[z0,z2,z3,z970,z5,z6]),(0,[z0,z2,z4,z5,z103,z114]),(0,[z0,z33,z3,z4,z69,z5])],[(0,[z0,z2,z3,z971,z5,z6]),(0,[z113,z2,z625,z4,z5,z6]),(0,[z0,z2,z3,z972,z5,z6]),(0,[z0,z973,z2,z3,z4,z5]),(0,[z2,z3,z92,z834,z5,z6])],[(0,[z0,z3,z4,z5,z974,z106])],[(0,[z0,z686,z2,z53,z5,z6]),(0,[z0,z2,z3,z975,z5,z6]),(0,[z0,z79,z3,z49,z5,z6]),(0,[z0,z2,z3,z4,z5,z976])],[(0,[z0,z2,z3,z977,z5,z6])],[(0,[z0,z978,z2,z3,z4,z6]),(0,[z0,z843,z3,z4,z5,z6]),(0,[z0,z221,z3,z65,z5,z6]),(0,[z0,z2,z3,z979,z5,z6])],[(0,[z0,z2,z3,z980,z5,z6]),(0,[z0,z981,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z982]),(0,[z272,z2,z625,z3,z4,z6]),(1,[z2,z3,z4,z5,z748]),(0,[z0,z822,z41,z4,z5,z6]),(0,[z0,z2,z983,z4,z5,z6]),(0,[z0,z2,z984,z4,z5,z6]),(0,[z0,z78,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z70,z801])],[(0,[z0,z2,z3,z4,z5,z985]),(0,[z0,z2,z3,z5,z753,z104])]],
   [[(0,[z0,z2,z4,z986,z5,z6]),(0,[z0,z987,z3,z4,z5,z6]),(0,[z0,z214,z2,z3,z422,z6]),(0,[z0,z204,z2,z3,z500,z6]),(0,[z0,z2,z3,z771,z43,z6])],[(0,[z0,z295,z3,z127,z5,z6]),(0,[z0,z988,z2,z3,z4,z5]),(0,[z0,z125,z3,z136,z5,z58])],[(0,[z0,z989,z3,z4,z5,z6]),(0,[z0,z142,z2,z3,z20,z6])],[(0,[z0,z414,z3,z4,z5,z6]),(0,[z113,z501,z2,z18,z4,z6]),(0,[z0,z214,z2,z5,z311,z6]),(0,[z212,z2,z3,z4,z5,z748]),(0,[z0,z2,z3,z4,z5,z990]),(0,[z0,z33,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z251,z6]),(0,[z113,z2,z17,z18,z4,z6]),(0,[z991,z2,z3,z4,z5,z6])],[(0,[z113,z2,z18,z4,z5,z6]),(0,[z0,z501,z2,z3,z4,z6]),(0,[z0,z2,z3,z5,z6,z992]),(0,[z0,z155,z3,z222,z5,z6])],[(0,[z0,z2,z3,z993,z5,z6]),(0,[z0,z2,z3,z4,z994,z6]),(0,[z0,z2,z4,z995,z5,z6]),(0,[z0,z2,z996,z3,z4,z6]),(0,[z212,z2,z3,z4,z5,z32])],[(0,[z47,z3,z4,z5,z51,z120]),(0,[z0,z344,z2,z4,z5,z133]),(0,[z0,z2,z102,z4,z5,z714]),(0,[z0,z2,z3,z43,z357,z6])]],
   [[(0,[z0,z997,z3,z4,z5,z6]),(0,[z0,z48,z3,z4,z346,z5])],[(0,[z27,z2,z3,z28,z5,z6]),(0,[z0,z2,z3,z4,z998,z5]),(0,[z999,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z182,z58,z6]),(0,[z0,z2,z4,z869,z5,z6])],[(0,[z0,z2,z3,z235,z5,z396]),(0,[z0,z1000,z2,z3,z4,z5])],[(0,[z0,z1001,z3,z4,z5,z6]),(0,[z0,z48,z3,z4,z5,z629]),(0,[z0,z88,z3,z818,z5,z6]),(0,[z0,z3,z535,z4,z160,z6])],[(0,[z0,z2,z3,z1002,z4,z5]),(0,[z0,z2,z3,z4,z1003,z6]),(0,[z2,z3,z4,z5,z32,z748]),(0,[z0,z2,z162,z4,z111,z6])],[(0,[z0,z2,z3,z4,z1004,z6]),(0,[z0,z266,z102,z4,z5,z103])],[(0,[z0,z266,z3,z4,z206,z6])],[(0,[z0,z1005,z3,z4,z5,z6]),(0,[z0,z3,z4,z346,z261,z5])]],
   [[(0,[z0,z2,z3,z4,z5,z1006]),(0,[z0,z168,z2,z3,z4,z106])],[(0,[z0,z2,z3,z771,z21,z6])],[(0,[z2,z3,z4,z834,z5,z6]),(0,[z0,z74,z822,z4,z5,z6]),(0,[z0,z3,z4,z69,z920,z6]),(0,[z0,z2,z3,z16,z136,z5]),(0,[z0,z2,z95,z786,z5,z6]),(0,[z1007,z2,z3,z4,z5,z6])],[(0,[z0,z1008,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1009,z6])],[(0,[z0,z295,z3,z4,z5,z6]),(0,[z0,z1010,z3,z4,z5,z6]),(0,[z421,z2,z3,z4,z5,z120]),(0,[z0,z2,z3,z4,z5,z1011]),(0,[z0,z124,z3,z4,z174,z6])],[(0,[z0,z2,z4,z1012,z5,z6]),(1,[z0,z3,z4,z5,z712]),(0,[z0,z2,z360,z53,z5,z6])],[(0,[z0,z1013,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1014,z6])],[(0,[z0,z2,z162,z389,z4,z6]),(1,[z0,z3,z4,z920,z6]),(0,[z0,z48,z3,z4,z261,z5])]],
   [[(0,[z113,z0,z2,z17,z4,z6]),(0,[z0,z2,z149,z4,z112,z6]),(0,[z0,z2,z3,z4,z5,z1015]),(0,[z0,z2,z3,z43,z406,z6]),(0,[z0,z2,z3,z4,z920,z6])],[(0,[z505,z2,z3,z28,z5,z6]),(0,[z0,z3,z4,z1016,z5,z6]),(0,[z0,z2,z3,z4,z5,z1017])],[(0,[z0,z2,z1018,z4,z5,z6]),(0,[z0,z2,z3,z92,z182,z6]),(0,[z0,z3,z5,z281,z51,z6]),(0,[z0,z124,z3,z4,z409,z6]),(0,[z0,z2,z3,z461,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z1019]),(0,[z0,z2,z84,z786,z5,z6])],[(0,[z0,z2,z3,z1020,z5,z6]),(0,[z0,z3,z4,z1021,z5,z6]),(0,[z0,z2,z3,z1022,z4,z6]),(0,[z0,z2,z1023,z4,z5,z6]),(0,[z0,z3,z136,z5,z58,z6])],[(0,[z0,z153,z214,z3,z5,z6])],[(0,[z0,z2,z1024,z4,z5,z6]),(0,[z47,z2,z3,z4,z422,z120]),(0,[z0,z2,z3,z4,z1025,z6])]],
   [[(0,[z0,z2,z3,z4,z70,z661]),(0,[z0,z2,z3,z336,z5,z6]),(0,[z0,z124,z3,z4,z920,z6]),(0,[z0,z2,z3,z5,z6,z1026]),(0,[z0,z137,z2,z248,z4,z5])],[],[(0,[z0,z2,z3,z4,z5,z1027]),(0,[z0,z2,z3,z4,z1028,z6]),(0,[z0,z2,z3,z5,z6,z1029]),(0,[z0,z2,z3,z832,z5,z6]),(0,[z299,z0,z3,z49,z5,z6])],[],[(0,[z272,z2,z149,z4,z150,z6])],[(0,[z524,z38,z3,z4,z5,z6]),(0,[z0,z1030,z2,z3,z4,z6]),(0,[z0,z88,z3,z65,z5,z6]),(0,[z0,z2,z3,z4,z5,z1031])],[(0,[z0,z2,z3,z332,z5,z6]),(0,[z0,z2,z3,z235,z466,z6]),(0,[z0,z214,z125,z2,z3,z5]),(0,[z0,z2,z3,z4,z1032,z6]),(0,[z0,z2,z3,z1033,z5,z6]),(0,[z0,z1034,z3,z4,z5,z6])],[]],
   [[(0,[z0,z2,z3,z4,z5,z1035]),(0,[z0,z2,z3,z1036,z5,z6]),(0,[z0,z48,z3,z535,z4,z5])],[(0,[z36,z184,z3,z4,z5,z6]),(0,[z144,z2,z4,z394,z5,z6]),(0,[z0,z1037,z2,z3,z4,z5]),(0,[z2,z3,z4,z734,z150,z6]),(0,[z0,z2,z5,z311,z281,z6])],[(0,[z0,z13,z2,z3,z346,z5])],[(0,[z0,z1038,z3,z4,z5,z6]),(0,[z0,z1039,z2,z3,z5,z6]),(0,[z165,z2,z3,z4,z582,z6]),(0,[z0,z142,z2,z3,z170,z6]),(0,[z0,z3,z4,z69,z6,z499]),(0,[z0,z2,z3,z771,z5,z6])],[(0,[z0,z2,z3,z127,z5,z396])],[(0,[z2,z774,z3,z4,z5,z6]),(0,[z0,z1040,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1041])],[(0,[z0,z2,z1042,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z748]),(0,[z0,z3,z4,z920,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1043]),(0,[z0,z2,z1044,z4,z5,z6]),(0,[z0,z2,z102,z4,z206,z103])]],
   [[(0,[z0,z414,z3,z4,z5,z114]),(0,[z0,z1045,z3,z4,z5,z6]),(0,[z62,z2,z3,z5,z598,z6]),(0,[z272,z2,z3,z4,z150,z6])],[(0,[z0,z2,z3,z4,z251,z114]),(0,[z0,z2,z3,z231,z4,z5])],[(0,[z113,z2,z18,z4,z5,z114]),(0,[z0,z2,z3,z4,z1046,z6])],[(0,[z0,z414,z3,z127,z5,z6]),(0,[z0,z1047,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1048,z5,z6]),(0,[z0,z88,z2,z3,z182,z6])],[(0,[z37,z38,z3,z4,z5,z126]),(0,[z0,z2,z783,z4,z5,z6]),(1,[z2,z3,z4,z734,z6]),(0,[z0,z2,z3,z356,z5,z6]),(0,[z0,z2,z3,z1049,z5,z6])],[],[(0,[z0,z1050,z3,z4,z5,z6]),(0,[z0,z3,z1051,z4,z5,z6])]],
   [[(0,[z113,z340,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z1052,z6]),(0,[z0,z2,z3,z4,z1053,z6]),(0,[z0,z48,z2,z3,z159,z5])],[(0,[z0,z1054,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z273]),(0,[z0,z1055,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1056,z6]),(0,[z62,z2,z3,z92,z5,z6]),(0,[z0,z214,z2,z3,z5,z6]),(0,[z0,z168,z3,z4,z51,z6]),(0,[z0,z266,z3,z461,z5,z6])],[],[(0,[z36,z774,z3,z4,z5,z6]),(0,[z0,z2,z822,z4,z5,z6]),(0,[z0,z2,z459,z4,z112,z6]),(0,[z0,z3,z222,z5,z6,z54])],[(0,[z272,z704,z2,z3,z4,z6]),(0,[z0,z4,z5,z311,z51,z6]),(0,[z0,z68,z2,z3,z4,z6]),(0,[z0,z48,z265,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1057]),(0,[z0,z42,z3,z818,z5,z6]),(0,[z0,z2,z3,z346,z136,z5])],[(0,[z0,z2,z3,z4,z5,z396]),(0,[z0,z2,z3,z1058,z4,z6]),(0,[z0,z2,z4,z5,z6,z1059]),(0,[z0,z2,z3,z4,z646,z70]),(0,[z706,z2,z3,z4,z5,z32]),(0,[z0,z33,z2,z3,z500,z5]),(0,[z0,z13,z2,z3,z650,z5]),(0,[z0,z1060,z3,z4,z5,z6])]],
   [[(0,[z165,z2,z3,z4,z734,z6])],[(0,[z0,z295,z3,z4,z5,z114]),(0,[z0,z2,z162,z4,z869,z6])],[(0,[z0,z1061,z2,z3,z4,z5]),(0,[z0,z2,z3,z1062,z5,z6]),(0,[z0,z2,z3,z4,z1063,z6]),(0,[z0,z3,z535,z159,z5,z6])],[(0,[z37,z38,z3,z4,z5,z6]),(0,[z0,z2,z3,z1064,z4,z6]),(0,[z0,z2,z3,z1065,z4,z6]),(0,[z0,z3,z4,z1066,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1067])],[(0,[z0,z2,z3,z4,z466,z114]),(0,[z670,z2,z3,z4,z5,z120]),(0,[z0,z204,z107,z3,z4,z6])],[(0,[z0,z1068,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1069]),(0,[z0,z1070,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z1071,z6]),(0,[z0,z2,z3,z127,z466,z6]),(0,[z0,z2,z3,z1072,z5,z6]),(0,[z0,z2,z1073,z4,z5,z6]),(0,[z0,z2,z3,z4,z1074,z6]),(0,[z0,z3,z535,z4,z5,z6])],[(0,[z113,z2,z783,z4,z5,z6]),(0,[z0,z2,z17,z3,z4,z6]),(0,[z0,z125,z3,z336,z5,z58]),(0,[z0,z1075,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1076,z6]),(0,[z0,z124,z2,z3,z500,z6])],[(0,[z0,z2,z3,z4,z5,z1077]),(0,[z0,z48,z3,z231,z4,z5]),(0,[z0,z3,z4,z920,z174,z6]),(0,[z0,z2,z3,z4,z1078,z6]),(0,[z0,z2,z3,z206,z461,z6])],[(0,[z0,z1079,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z51,z126]),(0,[z0,z3,z4,z5,z6,z1080]),(0,[z0,z214,z344,z2,z5,z6]),(0,[z0,z2,z3,z4,z5,z1081])],[(0,[z0,z2,z3,z4,z1082,z6]),(0,[z0,z1083,z3,z4,z5,z6]),(0,[z0,z2,z3,z1084,z5,z6]),(0,[z0,z2,z3,z4,z5,z1085])],[(0,[z0,z2,z3,z356,z5,z173]),(0,[z0,z155,z3,z5,z6,z218])],[(0,[z0,z2,z149,z4,z466,z6]),(0,[z0,z2,z3,z4,z6,z1086]),(0,[z0,z2,z3,z1087,z5,z6]),(0,[z0,z2,z3,z1088,z5,z6]),(0,[z0,z88,z3,z347,z5,z6]),(0,[z0,z2,z3,z1089,z5,z6]),(0,[z0,z2,z3,z4,z1090,z6]),(0,[z0,z13,z2,z3,z5,z700])]],
   [[(0,[z0,z168,z2,z3,z4,z55]),(0,[z0,z13,z2,z3,z5,z104])],[(0,[z0,z1091,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z974,z6]),(0,[z0,z3,z231,z4,z5,z58]),(0,[z0,z2,z3,z500,z5,z173]),(0,[z0,z2,z3,z1092,z5,z6]),(0,[z0,z66,z2,z4,z869,z6]),(0,[z0,z3,z4,z5,z6,z1093])],[(0,[z272,z2,z3,z4,z734,z6]),(0,[z2,z3,z4,z5,z1094,z6]),(0,[z0,z2,z3,z4,z6,z801])],[],[(0,[z0,z2,z1095,z4,z5,z6]),(0,[z0,z1096,z3,z4,z5,z6]),(0,[z47,z2,z3,z5,z281,z120]),(0,[z0,z3,z4,z422,z51,z6]),(0,[z0,z2,z3,z1097,z5,z6])],[(0,[z0,z2,z3,z1098,z5,z6]),(0,[z0,z2,z3,z4,z5,z106]),(0,[z0,z344,z4,z5,z51,z6])],[(0,[z0,z2,z3,z4,z5,z1099]),(0,[z0,z2,z3,z4,z5,z1100]),(0,[z0,z2,z3,z5,z14,z122])],[(0,[z36,z151,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1101,z6]),(0,[z47,z168,z2,z3,z4,z120])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 550) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 550).take 514) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1064)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [550, 514] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 166).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 166).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [166, 90] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_39669

theorem PEqualNP.Outside.L_meta_39669 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372896 * 2 ^ 32 + 3937058944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372896 * 2 ^ 32 + 3937058944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39669.solve