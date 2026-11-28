import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38239

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
  Nat.testBit (4008241856 * 2 ^ 32 + 4007700992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00046e15e04386aa#64 ++ 0x0002370af021c355#64 ++ 0xee8cfe3fe0c78fff#64 ++ 0xf7467f1ff063c7ff#64 : BitVec 256),
   (0x223116cc6d59b198#64 ++ 0x11188b6636acd8cc#64 ++ 0x7f731fccff79f199#64 ++ 0xbfb98fe67fbcf8cc#64 : BitVec 256),
   (0x4582a170b780dbe0#64 ++ 0x22c150b85bc06df0#64 ++ 0x7783e1f0ff81ffe1#64 ++ 0x3bc1f0f87fc0fff0#64 : BitVec 256),
   (0x09d801ea03ac0154#64 ++ 0x04ec00f501d600aa#64 ++ 0xfbfc01ff03fe01ff#64 ++ 0xfdfe00ff81ff00ff#64 : BitVec 256),
   (0x11efda0002f76c00#64 ++ 0x88f7ed00017bb600#64 ++ 0x7dfffe0003fffe00#64 ++ 0x3effff0001ffff00#64 : BitVec 256),
   (0x9ffffdbfd8000000#64 ++ 0x4ffffedfec000000#64 ++ 0x5ffffffffc000000#64 ++ 0x2ffffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [8, 5]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [9, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0xee8cfe3fe0c78fff 0xf7467f1ff063c7ff

def z1 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z2 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x7dfffe0003fffe00 0x3effff0001ffff00

def z3 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z4 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z5 : W := mkw 0x55cee93092a64e60 0xaae7749849532730 0x008ce03000860e60 0x0046701800430730

def z6 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x5ffffffffc000000 0x2ffffffffe000000

def z7 : W := mkw 0x00044a0000430400 0x0002250000218200 0x0400fe0000018e00 0x02007f000000c700

def z8 : W := mkw 0x00002415e00082aa 0x0000120af0004155 0x8200003fe00001ff 0xc100001ff00000ff

def z9 : W := mkw 0x0231148c48000000 0x01188a4624000000 0x5f731fccfc000000 0x2fb98fe67e000000

def z10 : W := mkw 0x4402a010b400daa0 0x220150085a006d50 0x0403e000fc01fe00 0x0201f0007e00ff00

def z11 : W := mkw 0x4582816017805940 0x22c140b00bc02ca0 0x110301c01f007000 0x088180e00f803800

def z12 : W := mkw 0x8e1025bfd8000000 0x470812dfec000000 0x020001fffc000000 0x010000fffe000000

def z13 : W := mkw 0x11efd80002a64c00 0x88f7ec0001532600 0x5dfffe0000860e00 0x2effff0000430700

def z14 : W := mkw 0x200002402559b198 0x1000012012acd8cc 0x200000000379f199 0x9000000001bcf8cc

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0xea8c003f00c601ff 0xf546001f806300ff

def z16 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0xfffffe3f03ffffff 0xffffff1f81ffffff

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0x880c000f0046001e 0xc40600078023000f

def z18 : W := mkw 0x0004681180020622 0x00023408c0010311 0x0000e00000000e00 0x0000700000000700

def z19 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x0400fe00e0018e00 0x02007f007000c700

def z20 : W := mkw 0x0858008a002c0014 0x042c00450016000a 0x887c000f007e001e 0xc43e0007803f000f

def z21 : W := mkw 0x4586ef75f7c3dfea 0x22c377bafbe1eff5 0xff8fffffffc7ffff 0xffc7ffffffe3ffff

def z22 : W := mkw 0x9ffffdbfd82c0014 0x4ffffedfec16000a 0xdffffffffc7e001e 0xeffffffffe3f000f

def z23 : W := mkw 0x6792a5fcff88dbf8 0x33c952fe7fc46dfc 0x7783e1fcff81fff9 0xbbc1f0fe7fc0fffc

def z24 : W := mkw 0x9a7d5c8f48000000 0x4d3eae47a4000000 0x087c1e0f00000000 0x043e0f0780000000

def z25 : W := mkw 0x6000024027d9fbf8 0x3000012013ecfdfc 0x2000000003f9fff9 0x9000000001fcfffc

def z26 : W := mkw 0x085800ca03ac0154 0x042c006501d600aa 0xa87c000f03fe01ff 0xd43e000781ff00ff

def z27 : W := mkw 0x00000200204386aa 0x000001001021c355 0x0000000000018e00 0x000000000000c700

def z28 : W := mkw 0x223110c80d183110 0x11188864068c1888 0x117301c01f387000 0x08b980e00f9c3800

def z29 : W := mkw 0x09dc4fef43ef055e 0x04ee27f7a1f782af 0xfbfc1fff03fe01ff 0xfdfe0fff81ff00ff

def z30 : W := mkw 0x081001aa00000000 0x040800d500000000 0x020001ff00000000 0x010000ff80000000

def z31 : W := mkw 0x0000000002804800 0x0000000001402400 0x200000000381fe00 0x1000000001c0ff00

def z32 : W := mkw 0x00046e15e0418088 0x0002370af020c044 0x6e8cfe3fe0418199 0xb7467f1ff020c0cc

def z33 : W := mkw 0x9deffb3392f76c00 0xcef7fd99c97bb600 0x7dfffe3303fffe00 0x3effff1981ffff00

def z34 : W := mkw 0x11eb920002f56800 0x88f5c900017ab400 0x7d731e000379f000 0x3eb98f0001bcf800

def z35 : W := mkw 0x0000004025009180 0x00000020128048c0 0x770301c0ff01f181 0x3b8180e07f80f8c0

def z36 : W := mkw 0x11cec80002a64c00 0x88e7640001532600 0x008ce00000860e00 0x0046700000430700

def z37 : W := mkw 0x44002170b50093e0 0x220010b85a8049f0 0x020001f0fc0001e1 0x010000f87e0000f0

def z38 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x117001c003380000 0x08b800e0019c0000

def z39 : W := mkw 0x221000c80d081110 0x1108006406840888 0x000001c01c000000 0x000000e00e000000

def z40 : W := mkw 0x11eb900002b46800 0x88f5c800015a3400 0x1173000003387000 0x08b98000019c3800

def z41 : W := mkw 0x9ffffdbfdab46800 0xcffffedfed5a3400 0x5fffffffff387000 0x2fffffffff9c3800

def z42 : W := mkw 0x11efde0462f7ec88 0x88f7ef02317bf644 0x7ffffe0ce3ffff99 0xbfffff0671ffffcc

def z43 : W := mkw 0x4000024027c3dfea 0x2000012013e1eff5 0xa000000003c7ffff 0xd000000001e3ffff

def z44 : W := mkw 0x00046c15c0000000 0x0002360ae0000000 0x4e8cfe3fe0000000 0x27467f1ff0000000

def z45 : W := mkw 0x0582a13090000000 0x02c1509848000000 0x5783e1f0fc000000 0x2bc1f0f87e000000

def z46 : W := mkw 0x1027da0000536c00 0x8813ed000029b600 0x0403fe000001fe00 0x0201ff000000ff00

def z47 : W := mkw 0x201002c82559b198 0x1008016412acd8cc 0x7b7001cc0379f199 0xbdb800e601bcf8cc

def z48 : W := mkw 0x106d5a0000772400 0x8836ad00003b9200 0x087c1e00007e0000 0x043e0f00003f0000

def z49 : W := mkw 0x400000402780dbe0 0x2000002013c06df0 0x200000000381ffe1 0x1000000001c0fff0

def z50 : W := mkw 0xdffffdffff80dbe0 0x6ffffeffffc06df0 0x7fffffffff81ffe1 0x3fffffffffc0fff0

def z51 : W := mkw 0x4582a17097805b60 0x22c150b84bc02db0 0x1183e1f01f807e60 0x08c1f0f80fc03f30

def z52 : W := mkw 0x9ffb91aa18000000 0x4ffdc8d50c000000 0x117301c01c000000 0x08b980e00e000000

def z53 : W := mkw 0x0000020000512000 0x0000010000289000 0x200000000379f000 0x1000000001bcf800

def z54 : W := mkw 0x22357edded5bb7ba 0x111abf6ef6addbdd 0x7f73ffccff79ff99 0xbfb9ffe67fbcffcc

def z55 : W := mkw 0x9fffffbfdaf76c00 0xcfffffdfed7bb600 0x7ffffffffffffe00 0x3fffffffffffff00

def z56 : W := mkw 0x11ceca0002f76c00 0x88e76500017bb600 0x208ce00003fffe00 0x1046700001ffff00

def z57 : W := mkw 0x09d825ffe3ac83fe 0x04ec12fff1d641ff 0xfbfc01ffe3fe01ff 0xfdfe00fff1ff00ff

def z58 : W := mkw 0x0180016003800140 0x00c000b001c000a0 0xfb8c01ff03c601ff 0xfdc600ff81e300ff

def z59 : W := mkw 0x00044a0000430400 0x0002250000218200 0xee8cfe3f00c78fff 0xf7467f1f8063c7ff

def z60 : W := mkw 0x19ffdbea03ff6d54 0x8cffedf501ffb6aa 0xffffffff03ffffff 0xffffffff81ffffff

def z61 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x6c8cfe00e0c78e00 0x36467f007063c700

def z62 : W := mkw 0x4ddaa1fab7acdbf4 0x26ed50fd5bd66dfa 0xffffe1ffffffffff 0xfffff0ffffffffff

def z63 : W := mkw 0xbffffffffd59b198 0x5ffffffffeacd8cc 0x7fffffffff79f199 0xbfffffffffbcf8cc

def z64 : W := mkw 0x9ffffdbfdaa40000 0x4ffffedfed520000 0x7ffffffffffe0000 0x3fffffffffff0000

def z65 : W := mkw 0x001000c801080110 0x0008006400840088 0x7b7001cc03780199 0xbdb800e601bc00cc

def z66 : W := mkw 0x2bf917ee6ffdb1dc 0x15fc8bf737fed8ee 0xffff1ffffffff1ff 0xffff8ffffffff8ff

def z67 : W := mkw 0x0bf915ae48000000 0x05fc8ad724000000 0x5fff1ffffc000000 0x2fff8ffffe000000

def z68 : W := mkw 0x00046c15c0000000 0x0002360ae0000000 0xee8cfe3fe0c601ff 0xf7467f1ff06300ff

def z69 : W := mkw 0x9627fc15d8000000 0x4b13fe0aec000000 0x0403fe00fc000000 0x0201ff007e000000

def z70 : W := mkw 0x0000060460418088 0x000003023020c044 0x6e001e0ce0418199 0xb7000f067020c0cc

def z71 : W := mkw 0x22357edded5bb7ba 0x111abf6ef6addbdd 0xffffffffffffffff 0xffffffffffffffff

def z72 : W := mkw 0x9ffb95ae58000000 0x4ffdcad72c000000 0x5f731fccfc000000 0x2fb98fe67e000000

def z73 : W := mkw 0x09d803ea23ef87fe 0x04ec01f511f7c3ff 0xfbfc01ff03ff8fff 0xfdfe00ff81ffc7ff

def z74 : W := mkw 0x00044a0002f76c00 0x80022500017bb600 0x6c8cfe0003fffe00 0x36467f0001ffff00

def z75 : W := mkw 0x4582a130b680dae0 0x22c150985b406d70 0x0483e030fc81fe60 0x0241f0187e40ff30

def z76 : W := mkw 0x0000060460418088 0x000003023020c044 0xee8c1e3fe0c781ff 0xf7460f1ff063c0ff

def z77 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x6680fe30e0818fe1 0x33407f187040c7f0

def z78 : W := mkw 0x0021120000512000 0x0010890000289000 0x7d731e000379f000 0x3eb98f0001bcf800

def z79 : W := mkw 0x4582a13092804a60 0x22c1509849402530 0x0080e03000800e60 0x0040701800400730

def z80 : W := mkw 0xbfffffbfd8592018 0x5fffffdfec2c900c 0x5ffffffffc780018 0xaffffffffe3c000c

def z81 : W := mkw 0x00046a11a04386aa 0x00023508d021c355 0xa08ce03300c78fff 0xd04670198063c7ff

def z82 : W := mkw 0x4582a13092804a60 0x22c1509849402530 0x5783e1f0fc800e60 0x2bc1f0f87e400730

def z83 : W := mkw 0x00044a0000430400 0x0002250000218200 0x6c8cfe0000c78e00 0x36467f000063c700

def z84 : W := mkw 0x00002415e00082aa 0x0000120af0004155 0xea8c003fe0c601ff 0xf546001ff06300ff

def z85 : W := mkw 0x221004cc6d089198 0x11080266368448cc 0x7b7001ccff780199 0xbdb800e67fbc00cc

def z86 : W := mkw 0x09c8012202a40044 0x04e4009101520022 0x808c003300860066 0x4046001980430033

def z87 : W := mkw 0x19efdb2202f76c44 0x8cf7ed91017bb622 0xfdfffe3303fffe66 0x7effff1981ffff33

def z88 : W := mkw 0x002112402551b180 0x0010892012a8d8c0 0x7f731fc0ff79f181 0x3fb98fe07fbcf8c0

def z89 : W := mkw 0x2231168c48592018 0x11188b46242c900c 0x08701e0c00780018 0x84380f06003c000c

def z90 : W := mkw 0xba7d5e8f48592018 0x5d3eaf47a42c900c 0x087c1e0f00780018 0x843e0f07803c000c

def z91 : W := mkw 0x1027fe15e053eeaa 0x8813ff0af029f755 0x0403fe00e001fe00 0x0201ff007000ff00

def z92 : W := mkw 0x222116046c51b088 0x11108b023628d844 0x7d731e00ff79f000 0x3eb98f007fbcf800

def z93 : W := mkw 0x1006c80000024c00 0x8803640000012600 0x0000e00000000e00 0x0000700000000700

def z94 : W := mkw 0x15eff93090000000 0x0af7fc9848000000 0x5ffffff0fc000000 0x2ffffff87e000000

def z95 : W := mkw 0x0000004003ac0154 0x0000002001d600aa 0xa000000003fe01ff 0xd000000001ff00ff

def z96 : W := mkw 0x9ffffdffdbac0154 0x4ffffeffedd600aa 0xfffffffffffe01ff 0xffffffffffff00ff

def z97 : W := mkw 0x099001ea03880154 0x04c800f501c400aa 0xf38001ff038001ff 0xf9c000ff81c000ff

def z98 : W := mkw 0x11effe15e04386aa 0x08f7ff0af021c355 0xfffffe3fe0c78fff 0xffffff1ff063c7ff

def z99 : W := mkw 0x0800012200000044 0x0400009100000022 0x8000003300000066 0x4000001980000033

def z100 : W := mkw 0x4582a17093804b60 0x22c150b849c025b0 0x7380e1f003800fe1 0x39c070f801c007f0

def z101 : W := mkw 0x19ffd9ea03ac0154 0x0cffecf501d600aa 0xffffffff03fe01ff 0xffffffff81ff00ff

def z102 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x2080e0300381ffe1 0x1040701801c0fff0

def z103 : W := mkw 0x6582a370b7d9fbf8 0x32c151b85becfdfc 0x7783e1f0fff9fff9 0xbbc1f0f87ffcfffc

def z104 : W := mkw 0x4582a774f7c1dbe8 0x22c153ba7be0edf4 0x7f83fffcffc1fff9 0xbfc1fffe7fe0fffc

def z105 : W := mkw 0x11efda0000430400 0x08f7ed0000218200 0x7dfffe0000c78e00 0x3effff000063c700

def z106 : W := mkw 0x3237decc6d5bfd98 0x991bef6636adfecc 0x7f73ffccff79ff99 0xbfb9ffe67fbcffcc

def z107 : W := mkw 0x0021100000000000 0x0010880000000000 0x5d731e0000000000 0x2eb98f0000000000

def z108 : W := mkw 0xbffb91ea1d183110 0x5ffdc8f50e8c1888 0x117301c01f387000 0x08b980e00f9c3800

def z109 : W := mkw 0x4dcaa172b7a4dbe4 0x26e550b95bd26df2 0xf78fe1f3ff87ffe7 0x7bc7f0f9ffc3fff3

def z110 : W := mkw 0x9ffffdbfdaa40044 0x4ffffedfed520022 0xdffffffffc860066 0x6ffffffffe430033

def z111 : W := mkw 0x0180016003800140 0x00c000b001c000a0 0x738001f0038001e1 0x39c000f801c000f0

def z112 : W := mkw 0x0182800002804800 0x00c1400001402400 0x7583e0000381fe00 0x3ac1f00001c0ff00

def z113 : W := mkw 0x221004cc6d089198 0x11080266368448cc 0x020001ccfc000199 0x810000e67e0000cc

def z114 : W := mkw 0x19ffdbea03ff6d54 0x8cffedf501ffb6aa 0x7dffffc003fffe00 0x3effffe001ffff00

def z115 : W := mkw 0x1027da0000536c00 0x8813ed000029b600 0x7d73fe000379fe00 0x3eb9ff0001bcff00

def z116 : W := mkw 0x00002010a00082a0 0x0000100850004150 0xee8ce03fe0c78fff 0xf746701ff063c7ff

def z117 : W := mkw 0x4582a130b280cae0 0x22c1509859406570 0x6680e030e0818fe1 0x334070187040c7f0

def z118 : W := mkw 0x23f916cc6ffdb198 0x11fc8b6637fed8cc 0x7fff1fccfffff199 0xbfff8fe67ffff8cc

def z119 : W := mkw 0x9627fe15d8536c00 0xcb13ff0aec29b600 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z120 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x15731fc0ff39f000 0x0ab98fe07f9cf800

def z121 : W := mkw 0xbfffffbffc51b088 0x5fffffdffe28d844 0x5ffffffffc01f000 0x2ffffffffe00f800

def z122 : W := mkw 0x9dcee93390000000 0x4ee77499c8000000 0x008ce03300000000 0x0046701980000000

def z123 : W := mkw 0x9ffff9bb98000000 0x4ffffcddcc000000 0x11ffe1f31c000000 0x08fff0f98e000000

def z124 : W := mkw 0x22257e15ec53b6aa 0x1112bf0af629db55 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z125 : W := mkw 0x02357e9de84386aa 0x011abf4ef421c355 0xfffffffffcc78fff 0xfffffffffe63c7ff

def z126 : W := mkw 0x19ffda8a02ff6c14 0x8cffed45017fb60a 0xfdfffe0f03fffe1e 0xfeffff0781ffff0f

def z127 : W := mkw 0x19ffdbaa02f76c00 0x8cffedd5017bb600 0x7fffffff03fffe00 0x3fffffff81ffff00

def z128 : W := mkw 0x00046c15e00286aa 0x0002360af0014355 0x828ce03fe0860fff 0xc146701ff04307ff

def z129 : W := mkw 0xae1025fffd089198 0x570812fffe8448cc 0x020001fffc000199 0x810000fffe0000cc

def z130 : W := mkw 0x09cc693382a60666 0x04e63499c1530333 0x808ce03300860e66 0x4046701980430733

def z131 : W := mkw 0x0000201080000220 0x0000100840000110 0x0080e03000800e60 0x0040701800400730

def z132 : W := mkw 0x67b3b7fcffd9fbf8 0x33d9dbfe7fecfdfc 0x7ff3fffcfff9fff9 0xbff9fffe7ffcfffc

def z133 : W := mkw 0x9ffb91ea1bac0154 0x4ffdc8f50dd600aa 0xfbff01ff1ffe01ff 0xfdff80ff8fff00ff

def z134 : W := mkw 0x8e1001aa18000000 0x470800d50c000000 0x000001c01c000000 0x000000e00e000000

def z135 : W := mkw 0x0231168c68418088 0x01188b463420c044 0x7f731fccfc418199 0xbfb98fe67e20c0cc

def z136 : W := mkw 0x4582a17097805940 0x22c150b84bc02ca0 0x5783e1f0ff007000 0x2bc1f0f87f803800

def z137 : W := mkw 0x9fffffbfd8512000 0x4fffffdfec289000 0x7fffffffff79f000 0x3fffffffffbcf800

def z138 : W := mkw 0x9623900018000000 0x4b11c8000c000000 0x000300001c000000 0x000180000e000000

def z139 : W := mkw 0x11ffdac803ff6d10 0x88ffed6401ffb688 0x7fffffcc03ffff99 0xbfffffe601ffffcc

def z140 : W := mkw 0x0000004001080110 0x0000002000840088 0x2000000003780199 0x9000000001bc00cc

def z141 : W := mkw 0x11efd80000000000 0x08f7ec0000000000 0x5dfffe0000000000 0x2effff0000000000

def z142 : W := mkw 0x4586ef35f2c3ceea 0x22c3779af961e775 0xee8cfe3fe0c78fff 0xf7467f1ff063c7ff

def z143 : W := mkw 0x0000020020418088 0x000001001020c044 0x2000000000418199 0x900000000020c0cc

def z144 : W := mkw 0x00046c15e00082aa 0x0002360af0004155 0xce8cfe3fe00001ff 0xe7467f1ff00000ff

def z145 : W := mkw 0x00046c15c0000000 0x0002360ae0000000 0x0400fe00e0000000 0x02007f0070000000

def z146 : W := mkw 0x00255a0000532400 0x0012ad0000299200 0x7dfffe0003fffe00 0x3effff0001ffff00

def z147 : W := mkw 0x00000200204386aa 0x000001001021c355 0xa000000000c78fff 0xd00000000063c7ff

def z148 : W := mkw 0x45caa170b7a4dbe0 0x22e550b85bd26df0 0x7fffe1f0ffffffe1 0x3ffff0f87ffffff0

def z149 : W := mkw 0x92255c0548000000 0x4912ae02a4000000 0x00001e0000000000 0x00000f0000000000

def z150 : W := mkw 0x11efda0000536c00 0x88f7ed000029b600 0x5dfffe000001fe00 0x2effff000000ff00

def z151 : W := mkw 0x0000060460418088 0x000003023020c044 0x04001e00e0018000 0x02000f007000c000

def z152 : W := mkw 0x00044e054043040a 0x00022702a0218205 0x880c1e0f0046001e 0xc4060f078023000f

def z153 : W := mkw 0x9637fc9dd8000000 0x4b1bfe4eec000000 0x5f73ffccfc000000 0x2fb9ffe67e000000

def z154 : W := mkw 0x00002415e00082aa 0x0000120af0004155 0x00000000e0000000 0x0000000070000000

def z155 : W := mkw 0x40002050a780dbe0 0x2000102853c06df0 0x6680e030e381ffe1 0x3340701871c0fff0

def z156 : W := mkw 0x984c480300000000 0x4c26240180000000 0x000c000300000000 0x0006000180000000

def z157 : W := mkw 0xce1025fffd0093e0 0x670812fffe8049f0 0x020001fffc0001e1 0x010000fffe0000f0

def z158 : W := mkw 0x0000020022f7eeaa 0x80000100117bf755 0xa000000003ffffff 0xd000000001ffffff

def z159 : W := mkw 0x0004681180020622 0x00023408c0010311 0x808ce03300860e66 0x4046701980430733

def z160 : W := mkw 0x19fb91ea03bc6954 0x8cfdc8f501de34aa 0x117301c003387000 0x08b980e0019c3800

def z161 : W := mkw 0x085801ea012c0154 0x042c00f5009600aa 0x8a7c01ff007e01ff 0xc53e00ff803f00ff

def z162 : W := mkw 0x20046e55e55bb7ba 0x1002372af2addbdd 0xee8cfe3fe3ffffff 0xf7467f1ff1ffffff

def z163 : W := mkw 0xd627fc15fc00daa0 0x6b13fe0afe006d50 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000000c601ff 0xd0000000006300ff

def z165 : W := mkw 0x223112c80d593110 0x1118896406ac9888 0x7d731fc01f79f000 0x3eb98fe00fbcf800

def z166 : W := mkw 0x0186ca0002c34c00 0x00c365000161a600 0x7d8ffe0003c7fe00 0x3ec7ff0001e3ff00

def z167 : W := mkw 0x09d801ea27ac91d4 0x04ec00f513d648ea 0xffff01fffffff1ff 0xffff80fffffff8ff

def z168 : W := mkw 0x0000000000000000 0x0000000000000000 0x570301c0fc000000 0x2b8180e07e000000

def z169 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x130301f0ff0071e1 0x098180f87f8038f0

def z170 : W := mkw 0x55effb70b7f7ffe0 0xaaf7fdb85bfbfff0 0x7ffffff0ffffffe1 0x3ffffff87ffffff0

def z171 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z172 : W := mkw 0x11eb900002b46800 0x88f5c800015a3400 0x75f3e00003b9fe00 0x3af9f00001dcff00

def z173 : W := mkw 0x9fffffbfd843040a 0x4fffffdfec218205 0xdffffffffc46001e 0xeffffffffe23000f

def z174 : W := mkw 0x2000024027fdb1dc 0x1000012013fed8ee 0xa000000003fff1ff 0xd000000001fff8ff

def z175 : W := mkw 0x106d7e15e077a6aa 0x8836bf0af03bd355 0xeefcfe3fe0ff8fff 0xf77e7f1ff07fc7ff

def z176 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x08fcfe3f00000000 0x047e7f1f80000000

def z177 : W := mkw 0x00002010a00082a0 0x0000100850004150 0x0400e000e0018e00 0x020070007000c700

def z178 : W := mkw 0x20000240255bb7ba 0x1000012012addbdd 0xa000000003ffffff 0xd000000001ffffff

def z179 : W := mkw 0x00002010a00082a0 0x0000100850004150 0x6680e030e0818fe1 0x334070187040c7f0

def z180 : W := mkw 0xbffb97ee7d59b198 0x5ffdcbf73eacd8cc 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z181 : W := mkw 0x33ffdecc6ffffd98 0x99ffef6637fffecc 0x7fffffccffffff99 0xbfffffe67fffffcc

def z182 : W := mkw 0x9a7d5c8f48000000 0x4d3eae47a4000000 0x5f7f1fcffc000000 0x2fbf8fe7fe000000

def z183 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x197f1e00037e7000 0x0cbf8f0001bf3800

def z184 : W := mkw 0x9ffbb5bfd8000000 0x4ffddadfec000000 0x137301fffc000000 0x09b980fffe000000

def z185 : W := mkw 0x01c8000002a40000 0x00e4000001520000 0xfbfc003f03fe01ff 0xfdfe001f81ff00ff

def z186 : W := mkw 0x11effe15e2f7eeaa 0x88f7ff0af17bf755 0xfffffe3fe3ffffff 0xffffff1ff1ffffff

def z187 : W := mkw 0x19fb91ea03bc6954 0x8cfdc8f501de34aa 0xfbff01ff03fe71ff 0xfdff80ff81ff38ff

def z188 : W := mkw 0x9fffffbff84386aa 0x4fffffdffc21c355 0xfffffffffcc78fff 0xfffffffffe63c7ff

def z189 : W := mkw 0x081001ea01080154 0x040800f5008400aa 0x820001ff000001ff 0xc10000ff800000ff

def z190 : W := mkw 0x2231168c6c51b088 0x11188b463628d844 0x5f731fccfc01f000 0x2fb98fe67e00f800

def z191 : W := mkw 0x2000024027fffd98 0x9000012013fffecc 0x2000000003ffff99 0x9000000001ffffcc

def z192 : W := mkw 0x0000020002f76c00 0x80000100017bb600 0x2000000003fffe00 0x1000000001ffff00

def z193 : W := mkw 0x01a3920002d16800 0x00d1c9000168b400 0x7df3fe0003f9fe00 0x3ef9ff0001fcff00

def z194 : W := mkw 0x9fffdbaa1af76c00 0xcfffedd50d7bb600 0x7dffffc01ffffe00 0x3effffe00fffff00

def z195 : W := mkw 0x97effc15d8000000 0x4bf7fe0aec000000 0x5dfffe00fc000000 0x2effff007e000000

def z196 : W := mkw 0x97a7fd35d8000000 0x4bd3fe9aec000000 0x5783fff0fc000000 0x2bc1fff87e000000

def z197 : W := mkw 0x09d801ea03800140 0x04ec00f501c000a0 0x7bfc01ff038001e1 0x3dfe00ff81c000f0

def z198 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x1573fe000339fe00 0x0ab9ff00019cff00

def z199 : W := mkw 0x09d801aa00000000 0x04ec00d500000000 0x117001c000000000 0x08b800e000000000

def z200 : W := mkw 0x4592a1f8b788dbf0 0x22c950fc5bc46df8 0x7ff3e1fcfff9fff9 0xbff9f0fe7ffcfffc

def z201 : W := mkw 0x0000004003800140 0x0000002001c000a0 0x20000000038001e1 0x1000000001c000f0

def z202 : W := mkw 0x0231108808000000 0x0118884404000000 0x117301c01c000000 0x08b980e00e000000

def z203 : W := mkw 0x9dcee93390000000 0x4ee77499c8000000 0x578fe1f3fc000000 0x2bc7f0f9fe000000

def z204 : W := mkw 0x200002002451b088 0x100001001228d844 0x000000000001f000 0x000000000000f800

def z205 : W := mkw 0x4582a170b50093e0 0x22c150b85a8049f0 0x5783e1f0fc0001e1 0x2bc1f0f87e0000f0

def z206 : W := mkw 0x0bf915ee4bac0154 0x05fc8af725d600aa 0xffff1ffffffe01ff 0xffff8fffffff00ff

def z207 : W := mkw 0x9fffffbff8418088 0x4fffffdffc20c044 0x7ffffffffc418199 0xbffffffffe20c0cc

def z208 : W := mkw 0x0180016003800140 0x00c000b001c000a0 0x110001c003000000 0x088000e001800000

def z209 : W := mkw 0x55efdb6017f77d40 0xaaf7edb00bfbbea0 0x7dffffc01ffffe00 0x3effffe00fffff00

def z210 : W := mkw 0x223114cc4d183110 0x11188a66268c1888 0x5f731fccff387000 0x2fb98fe67f9c3800

def z211 : W := mkw 0x01c8000000000000 0x00e4000000000000 0x59fc000000000000 0x2cfe000000000000

def z212 : W := mkw 0x5dfffbfab7fffff4 0xaefffdfd5bfffffa 0xffffffffffffffff 0xffffffffffffffff

def z213 : W := mkw 0x47b3b5fcff80dbe0 0x23d9dafe7fc06df0 0x7ff3fffcff81ffe1 0x3ff9fffe7fc0fff0

def z214 : W := mkw 0x11eb900000000000 0x08f5c80000000000 0x1173000000000000 0x08b9800000000000

def z215 : W := mkw 0x09d801aa00000000 0x04ec00d500000000 0x5bfc01ff00000000 0x2dfe00ff80000000

def z216 : W := mkw 0x8e146dbfd8000000 0x470a36dfec000000 0x4e8cfffffc000000 0x27467ffffe000000

def z217 : W := mkw 0x67b7fffdffdbfffa 0x33dbfffeffedfffd 0xffffffffffffffff 0xffffffffffffffff

def z218 : W := mkw 0x4ddaa1fab780dbe0 0x26ed50fd5bc06df0 0x7fffe1ffff81ffe1 0x3ffff0ffffc0fff0

def z219 : W := mkw 0x327d5e8c487f2418 0x993eaf46243f920c 0x087c1e0c007e0018 0x843e0f06003f000c

def z220 : W := mkw 0x00046e15c043062a 0x0002370ae0218315 0x888cfe3f00c60e7e 0xc4467f1f8063073f

def z221 : W := mkw 0x9e7ffc9fd8000000 0x4f3ffe4fec000000 0x0c7ffe0ffc000000 0x063fff07fe000000

def z222 : W := mkw 0xdffffdffffacdbf4 0x6ffffeffffd66dfa 0xffffffffffffffff 0xffffffffffffffff

def z223 : W := mkw 0x2bd805ee6fac91dc 0x15ec02f737d648ee 0xfbfc01fffffe01ff 0xfdfe00ffffff00ff

def z224 : W := mkw 0x2000020000592018 0x10000100002c900c 0x0000000000780018 0x80000000003c000c

def z225 : W := mkw 0x001000c803ac0154 0x0008006401d600aa 0xfb7001cc03fe01ff 0xfdb800e601ff00ff

def z226 : W := mkw 0x5427fa10b453fea0 0xaa13fd085a29ff50 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z227 : W := mkw 0xdffb91ea1f805940 0x6ffdc8f50fc02ca0 0x117301c01f007000 0x08b980e00f803800

def z228 : W := mkw 0x44002010b40092a0 0x220010085a004950 0x00000000fc000000 0x000000007e000000

def z229 : W := mkw 0x10255a0000532400 0x8812ad0000299200 0x00001e0000000000 0x00000f0000000000

def z230 : W := mkw 0x0000000000000000 0x0000000000000000 0x750300000301f000 0x3a8180000180f800

def z231 : W := mkw 0x33fffeddefffffba 0x99ffff6ef7ffffdd 0xffffffffffffffff 0xffffffffffffffff

def z232 : W := mkw 0x00000000200082aa 0x0000000010004155 0x80000000000001ff 0xc0000000000000ff

def z233 : W := mkw 0x0000201080000000 0x0000100840000000 0x4680e030e0000000 0x2340701870000000

def z234 : W := mkw 0x8c00213390000000 0x46001099c8000000 0x0000003300000000 0x0000001980000000

def z235 : W := mkw 0x09d8008a02ac0014 0x04ec00450156000a 0xf9fc000f03fe001e 0xfcfe000781ff000f

def z236 : W := mkw 0x02357c9dc8000000 0x011abe4ee4000000 0x5ffffffffc000000 0x2ffffffffe000000

def z237 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x5bfc01ff03380000 0x2dfe00ff819c0000

def z238 : W := mkw 0x001000c825089190 0x00080064128448c8 0x7f7301ccff79f199 0xbfb980e67fbcf8cc

def z239 : W := mkw 0x223136dded59b3ba 0x11189b6ef6acd9dd 0xff731fffff79f1ff 0xffb98fffffbcf8ff

def z240 : W := mkw 0x11ed5a0002f72400 0x88f6ad00017b9200 0x79fc1e0003fe0000 0x3cfe0f0001ff0000

def z241 : W := mkw 0x01c8000002a40000 0x00e4000001520000 0x79fc000003fe0000 0x3cfe000001ff0000

def z242 : W := mkw 0x222116046c51b088 0x11108b023628d844 0x04031e00fc01f000 0x02018f007e00f800

def z243 : W := mkw 0x0000004025009180 0x00000020128048c0 0x020001c0fc000181 0x010000e07e0000c0

def z244 : W := mkw 0xffffffffffd9fbf8 0x7fffffffffecfdfc 0x7ffffffffff9fff9 0xbffffffffffcfffc

def z245 : W := mkw 0x09dc6fffe3ef87fe 0x04ee37fff1f7c3ff 0xfffcffffe3ff8fff 0xfffe7ffff1ffc7ff

def z246 : W := mkw 0x51efda4027f7ffe0 0xa8f7ed2013fbfff0 0x7dfffe0003ffffe1 0x3effff0001fffff0

def z247 : W := mkw 0x223116cc6d5bb7ba 0x11188b6636addbdd 0xff731fccffffffff 0xffb98fe67fffffff

def z248 : W := mkw 0x01800160278091c0 0x00c000b013c048e0 0x778301f0ff81f1e1 0x3bc180f87fc0f8f0

def z249 : W := mkw 0x6ffbb7fefffdfbfc 0x37fddbff7ffefdfe 0xffffffffffffffff 0xffffffffffffffff

def z250 : W := mkw 0x4402a050b500dba0 0x220150285a806dd0 0x7703e1c0ff01ff81 0x3b81f0e07f80ffc0

def z251 : W := mkw 0x0182800002804800 0x00c1400001402400 0x0080e00000800e00 0x0040700000400700

def z252 : W := mkw 0x9ffffdbfdaa64c00 0xcffffedfed532600 0x5ffffffffc860e00 0x2ffffffffe430700

def z253 : W := mkw 0x9dcee93392a64c00 0xcee77499c9532600 0x008ce03300860e00 0x0046701980430700

def z254 : W := mkw 0x33ffde8c4aff6c18 0x99ffef46257fb60c 0x7dfffe0c03fffe18 0xbeffff0601ffff0c

def z255 : W := mkw 0x9a7d5e8f48772400 0xcd3eaf47a43b9200 0x087c1e0f007e0000 0x043e0f07803f0000

def z256 : W := mkw 0x2000004025089198 0x10000020128448cc 0x0000000000000199 0x80000000000000cc

def z257 : W := mkw 0x418280402780dbe0 0x20c1402013c06df0 0x7583e0000381ffe1 0x3ac1f00001c0fff0

def z258 : W := mkw 0x0586ed35d0000000 0x02c3769ae8000000 0x5f8ffffffc000000 0x2fc7fffffe000000

def z259 : W := mkw 0x4582a010b680daa0 0x22c150085b406d50 0x7583e000ff81fe00 0x3ac1f0007fc0ff00

def z260 : W := mkw 0x106d5a0000772400 0x8836ad00003b9200 0x7d7f1e00037ff000 0x3ebf8f0001bff800

def z261 : W := mkw 0x2000004005183110 0x10000020028c1888 0x0000000003387000 0x00000000019c3800

def z262 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x8c0cfe0fe0478e1e 0xc6067f07f023c70f

def z263 : W := mkw 0x9ffffdbfda804800 0x4ffffedfed402400 0x7fffffffff81fe00 0x3fffffffffc0ff00

def z264 : W := mkw 0x6623b614fc51faa8 0x3311db0a7e28fd54 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z265 : W := mkw 0x2bf917ee6d59b198 0x15fc8bf736acd8cc 0x7fff1fffff79f199 0xbfff8fffffbcf8cc

def z266 : W := mkw 0x33fb90c80fbc7910 0x99fdc86407de3c88 0x117301c01f387000 0x08b980e00f9c3800

def z267 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x8600fe3fe0018fff 0xc3007f1ff000c7ff

def z268 : W := mkw 0x018280402780d980 0x00c1402013c06cc0 0x7783e1c0ff81ff81 0x3bc1f0e07fc0ffc0

def z269 : W := mkw 0x0000064465419188 0x0000032232a0c8c4 0x7f031fccff41f199 0xbf818fe67fa0f8cc

def z270 : W := mkw 0x01c8000002a40000 0x00e4000001520000 0x008c000000860000 0x0046000000430000

def z271 : W := mkw 0x0182816003804940 0x00c140b001c024a0 0x7783e1f00381ffe1 0x3bc1f0f801c0fff0

def z272 : W := mkw 0x19ffd9aa00000000 0x0cffecd500000000 0x5fffffff00000000 0x2fffffff80000000

def z273 : W := mkw 0x9e7d7dbfd8000000 0x4f3ebedfec000000 0x0a7c1ffffc000000 0x053e0ffffe000000

def z274 : W := mkw 0x00046c15c0020622 0x0002360ae0010311 0xce8cfe3fe0860e66 0x67467f1ff0430733

def z275 : W := mkw 0x29d803ea27fdb1dc 0x14ec01f513fed8ee 0xfbfc01ff03fff1ff 0xfdfe00ff81fff8ff

def z276 : W := mkw 0x09d801aa02a40044 0x04ec00d501520022 0xdbfc01ff00860066 0x6dfe00ff80430033

def z277 : W := mkw 0x081025ffe10883fe 0x040812fff08441ff 0x820001ffe00001ff 0xc10000fff00000ff

def z278 : W := mkw 0x0004480100020402 0x0002240080010201 0x800c000300060006 0x4006000180030003

def z279 : W := mkw 0x01e9120002f52000 0x00f48900017a9000 0x7dff1e0003fff000 0x3eff8f0001fff800

def z280 : W := mkw 0x19ffffffe3ffeffe 0x8cfffffff1fff7ff 0xffffffffe3ffffff 0xfffffffff1ffffff

def z281 : W := mkw 0x4586ef75f7c3dfea 0x22c377bafbe1eff5 0x7783fff0ff81ffe1 0x3bc1fff87fc0fff0

def z282 : W := mkw 0x081001ea01080154 0x040800f5008400aa 0xfb7001ff037801ff 0xfdb800ff81bc00ff

def z283 : W := mkw 0x11efda0000512000 0x08f7ed0000289000 0x7dfffe000379f000 0x3effff0001bcf800

def z284 : W := mkw 0x221006cc6d499198 0x1108036636a4c8cc 0x6e001fccfc418199 0xb7000fe67e20c0cc

def z285 : W := mkw 0x11efd80002b66c00 0x88f7ec00015b3600 0x11ffe00003be7e00 0x08fff00001df3f00

def z286 : W := mkw 0x09d801aa00000000 0x04ec00d500000000 0xfbfc01ff00c601ff 0xfdfe00ff806300ff

def z287 : W := mkw 0x023114cc6d009180 0x01188a66368048c0 0x7f731fccff01f181 0x3fb98fe67f80f8c0

def z288 : W := mkw 0x09d807ee63ed81dc 0x04ec03f731f6c0ee 0xfffc1fffe3ff81ff 0xfffe0ffff1ffc0ff

def z289 : W := mkw 0x4402a01090004a20 0x2201500848002510 0x0000e00000000e00 0x0000700000000700

def z290 : W := mkw 0x09da81ea03ac4954 0x04ed40f501d624aa 0xffffe1ff03ffffff 0xfffff0ff81ffffff

def z291 : W := mkw 0x9ffffdbff80082aa 0x4ffffedffc004155 0xdffffffffc0001ff 0xeffffffffe0000ff

def z292 : W := mkw 0x1027da0002f76c00 0x8813ed00017bb600 0x2403fe0003fffe00 0x1201ff0001ffff00

def z293 : W := mkw 0x09d803ea03ff6d54 0x84ec01f501ffb6aa 0xfbfc01ff03ffffff 0xfdfe00ff81ffffff

def z294 : W := mkw 0x4000024027f7ffe0 0xa000012013fbfff0 0x2000000003ffffe1 0x1000000001fffff0

def z295 : W := mkw 0x327d5ecc6d7fb598 0x993eaf6636bfdacc 0x7f7f1fccff7ff199 0xbfbf8fe67fbff8cc

def z296 : W := mkw 0x11efda0000772400 0x88f7ed00003b9200 0x5dfffe00007e0000 0x2effff00003f0000

def z297 : W := mkw 0x4dda81ea17ac5954 0x26ed40f50bd62caa 0xfbff01ff1ffe71ff 0xfdff80ff8fff38ff

def z298 : W := mkw 0x00046e15c043040a 0x0002370ae0218205 0xce8cfe3fe046001e 0xe7467f1ff023000f

def z299 : W := mkw 0x4000004027acdbf4 0x2000002013d66dfa 0xa000000003ffffff 0xd000000001ffffff

def z300 : W := mkw 0xb627fe15fc51b088 0x5b13ff0afe28d844 0x0403fe00fc01f000 0x0201ff007e00f800

def z301 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x1503e1c0ff01fe00 0x0a81f0e07f80ff00

def z302 : W := mkw 0x00002050a50093a0 0x00001028528049d0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z303 : W := mkw 0x00044c0540000000 0x00022602a0000000 0x080c1e0f00000000 0x04060f0780000000

def z304 : W := mkw 0x0582a13092804800 0x02c1509849402400 0x7783e1f0ff81fe00 0x3bc1f0f87fc0ff00

def z305 : W := mkw 0x0000000000000000 0x0000000000000000 0x6480e00000818e00 0x324070000040c700

def z306 : W := mkw 0xdfffffffffc3dfea 0x6fffffffffe1eff5 0xffffffffffc7ffff 0xffffffffffe3ffff

def z307 : W := mkw 0x8e146fbff84386aa 0x470a37dffc21c355 0xee8cfffffcc78fff 0xf7467ffffe63c7ff

def z308 : W := mkw 0x00046811a00286a2 0x00023408d0014351 0xe68ce033e0878fe7 0x73467019f043c7f3

def z309 : W := mkw 0x4000000002804a60 0x2000000001402530 0x0000000000800e60 0x0000000000400730

def z310 : W := mkw 0x4582812012804840 0x22c1409009402420 0x0000000000000000 0x0000000000000000

def z311 : W := mkw 0x11cec80002a64c00 0x88e7640001532600 0x79fce00003fe0e00 0x3cfe700001ff0700

def z312 : W := mkw 0x22355ecd6d5bb59a 0x111aaf66b6addacd 0xff7f1fcfff7ff19f 0xffbf8fe7ffbff8cf

def z313 : W := mkw 0x4406ee15f443deaa 0x2203770afa21ef55 0xee8ffe3ffcc7ffff 0xf747ff1ffe63ffff

def z314 : W := mkw 0x13ffde8c4af76c00 0x89ffef46257bb600 0x7fffffccfffffe00 0x3fffffe67fffff00

def z315 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x28701e0c0379f199 0x94380f0601bcf8cc

def z316 : W := mkw 0x09d801aa002c0014 0x04ec00d50016000a 0xdbfc01ff007e001e 0xedfe00ff803f000f

def z317 : W := mkw 0x9627fe15f84386aa 0x4b13ff0afc21c355 0xee8ffe3ffcc78fff 0xf747ff1ffe63c7ff

def z318 : W := mkw 0x40046e55e7c3dfea 0x2002372af3e1eff5 0xee8cfe3fe3c7ffff 0xf7467f1ff1e3ffff

def z319 : W := mkw 0x09c8012200000000 0x04e4009100000000 0x008c003300000000 0x0046001980000000

def z320 : W := mkw 0x00046e15e2f7eeaa 0x8002370af17bf755 0xee8cfe3fe3ffffff 0xf7467f1ff1ffffff

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x808c003300860066 0x4046001980430033

def z322 : W := mkw 0x0ddaa1fa93ac0154 0x06ed50fd49d600aa 0xffffe1fffffe01ff 0xfffff0ffffff00ff

def z323 : W := mkw 0x11effa1182f76e22 0x88f7fd08c17bb711 0xfdfffe3303fffe66 0x7effff1981ffff33

def z324 : W := mkw 0x0858008a002c0014 0x042c00450016000a 0xeafc003f00fe01ff 0xf57e001f807f00ff

def z325 : W := mkw 0x0000004003ac0154 0x0000002001d600aa 0xea8c003f03fe01ff 0xf546001f81ff00ff

def z326 : W := mkw 0x0402a01090000000 0x0201500848000000 0x0403e000fc000000 0x0201f0007e000000

def z327 : W := mkw 0x9dceef37f04386aa 0x4ee7779bf821c355 0xee8cfe3fe0c78fff 0xf7467f1ff063c7ff

def z328 : W := mkw 0x0000040460008088 0x0000020230004044 0x0200000ce0000199 0x81000006700000cc

def z329 : W := mkw 0x97effe15daf76c00 0xcbf7ff0aed7bb600 0x7dfffe00fffffe00 0x3effff007fffff00

def z330 : W := mkw 0x00002010a00082a0 0x0000100850004150 0x02000030e00001e1 0x01000018700000f0

def z331 : W := mkw 0xbffffdffdd183110 0x5ffffeffee8c1888 0x5fffffffff387000 0x2fffffffff9c3800

def z332 : W := mkw 0x4400213090000260 0x2200109848000130 0x0000003000000060 0x0000001800000030

def z333 : W := mkw 0x1023900000106800 0x8811c80000083400 0x0003000000007000 0x0001800000003800

def z334 : W := mkw 0x4586eb70b7c3dfe0 0x22c375b85be1eff0 0x7f8ffff0ffc7ffe1 0x3fc7fff87fe3fff0

def z335 : W := mkw 0x019001e803880150 0x00c800f401c400a8 0x7bf001fc03f801f9 0xbdf800fe01fc00fc

def z336 : W := mkw 0x9fffffbff84386aa 0x4fffffdffc21c355 0x5ffffffffc018e00 0x2ffffffffe00c700

def z337 : W := mkw 0x3bffdfee6ffffddc 0x9dffeff737fffeee 0xffffffffffffffff 0xffffffffffffffff

def z338 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0xa400fe00e0c78fff 0xd2007f007063c7ff

def z339 : W := mkw 0x11efda4027f7fd80 0x88f7ed2013fbfec0 0x7fffffc0ffffff81 0x3fffffe07fffffc0

def z340 : W := mkw 0x0582a170b5009180 0x02c150b85a8048c0 0x7783e1f0ff01f181 0x3bc1f0f87f80f8c0

def z341 : W := mkw 0x4582a575f780dbea 0x22c152bafbc06df5 0xf783e1ffff81ffff 0xfbc1f0ffffc0ffff

def z342 : W := mkw 0xbffffffffffdb1dc 0x5ffffffffffed8ee 0xfffffffffffff1ff 0xfffffffffffff8ff

def z343 : W := mkw 0x4c1021fab50893f4 0x260810fd5a8449fa 0x820001fffc0001ff 0xc10000fffe0000ff

def z344 : W := mkw 0x4402a010b400daa0 0x220150085a006d50 0x6683e030fc81ffe1 0x3341f0187e40fff0

def z345 : W := mkw 0x001000c801080110 0x0008006400840088 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z346 : W := mkw 0x2bf911ea0fbc3154 0x15fc88f507de18aa 0xfbff01ff1ffe71ff 0xfdff80ff8fff38ff

def z347 : W := mkw 0x4000004007805940 0x2000002003c02ca0 0x0000000003007000 0x0000000001803800

def z348 : W := mkw 0x33efde046ef7fc88 0x99f7ef02377bfe44 0x7dfffe00fffffe00 0x3effff007fffff00

def z349 : W := mkw 0x0ddaa1ba90000000 0x06ed50dd48000000 0x5fffe1fffc000000 0x2ffff0fffe000000

def z350 : W := mkw 0x0400213090000000 0x0200109848000000 0x020001f0fc000000 0x010000f87e000000

def z351 : W := mkw 0x00044a00204386aa 0x000225001021c355 0xec8cfe0000c78fff 0xf6467f000063c7ff

def z352 : W := mkw 0x9dca812210000000 0x4ee5409108000000 0x0000000000000000 0x0000000000000000

def z353 : W := mkw 0x2a3117ee6d59b1dc 0x15188bf736acd8ee 0xff731fffff79f1ff 0xffb98fffffbcf8ff

def z354 : W := mkw 0xb637feddfd59b198 0x5b1bff6efeacd8cc 0x7f73ffccff79f199 0xbfb9ffe67fbcf8cc

def z355 : W := mkw 0x11eb900002b46800 0x88f5c800015a3400 0x79ff000003fe7000 0x3cff800001ff3800

def z356 : W := mkw 0x11efd80002804800 0x08f7ec0001402400 0x7dfffe000381fe00 0x3effff0001c0ff00

def z357 : W := mkw 0xddcee93392804a60 0x6ee77499c9402530 0x008ce03300800e60 0x0046701980400730

def z358 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0xff8fe1ffffc7ffff 0xffc7f0ffffe3ffff

def z359 : W := mkw 0x223112c82d59b198 0x1118896416acd8cc 0x317301c01f79f199 0x98b980e00fbcf8cc

def z360 : W := mkw 0x00000000002c0014 0x000000000016000a 0x80000000007e001e 0xc0000000003f000f

def z361 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x0a701fccfc780199 0x85380fe67e3c00cc

def z362 : W := mkw 0x221006cc6d59b198 0x1108036636acd8cc 0x220001ccff79f199 0x910000e67fbcf8cc

def z363 : W := mkw 0x11cec80002a64c00 0x88e7640001532600 0x758fe0000387fe00 0x3ac7f00001c3ff00

def z364 : W := mkw 0x01cc4a0002e70400 0x00e6250001738200 0x7dfcfe0003ff8e00 0x3efe7f0001ffc700

def z365 : W := mkw 0x0180000002800000 0x00c0000001400000 0x7180000003800000 0x38c0000001c00000

def z366 : W := mkw 0x4582a370b7f7ffe0 0xa2c151b85bfbfff0 0x7783e1f0ffffffe1 0x3bc1f0f87ffffff0

def z367 : W := mkw 0x000002000043040a 0x0000010000218205 0x800000000046001e 0xc00000000023000f

def z368 : W := mkw 0x023114cc49080110 0x01188a6624840088 0x7f731fccff780199 0xbfb98fe67fbc00cc

def z369 : W := mkw 0x4582a13092804a60 0x22c1509849402530 0x7583e0300381fe60 0x3ac1f01801c0ff30

def z370 : W := mkw 0x4582816017805940 0x22c140b00bc02ca0 0x738301f01f8071e1 0x39c180f80fc038f0

def z371 : W := mkw 0x223116cc4d593118 0x11188b6626ac988c 0x19731fcc1f787018 0x8cb98fe60fbc380c

def z372 : W := mkw 0xba7d5ecf6d59b198 0x5d3eaf67b6acd8cc 0x7f7f1fcfff79f199 0xbfbf8fe7ffbcf8cc

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0x4a8c003f00000000 0x2546001f80000000

def z374 : W := mkw 0x33fb96cc6ffdf998 0x99fdcb6637fefccc 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z375 : W := mkw 0x01802170a38083e0 0x00c010b851c041f0 0x7780e1f0e3818fe1 0x3bc070f871c0c7f0

def z376 : W := mkw 0x4ddaa1fab7acdbf4 0x26ed50fd5bd66dfa 0x77f3e1f0ffb9ffe1 0x3bf9f0f87fdcfff0

def z377 : W := mkw 0x01ca800002a44800 0x00e5400001522400 0x7dffe00003fffe00 0x3efff00001ffff00

def z378 : W := mkw 0x8fd825bfd8000000 0x47ec12dfec000000 0x5bfc01fffc000000 0x2dfe00fffe000000

def z379 : W := mkw 0x0848000200240004 0x0424000100120002 0x800c000300060006 0x4006000180030003

def z380 : W := mkw 0x22146edded4b97ba 0x110a376ef6a5cbdd 0xee8cfffffcc78fff 0xf7467ffffe63c7ff

def z381 : W := mkw 0x31efda4027fffd98 0x98f7ed2013fffecc 0x7dfffe0003ffff99 0xbeffff0001ffffcc

def z382 : W := mkw 0x0000004003ac0154 0x0000002001d600aa 0x0000000003380000 0x00000000019c0000

def z383 : W := mkw 0x01846f75e3c387ea 0x00c237baf1e1c3f5 0xff8cffffe3c78fff 0xffc67ffff1e3c7ff

def z384 : W := mkw 0x09c8016203ac0154 0x04e400b101d600aa 0xa08c003303fe01ff 0xd046001981ff00ff

def z385 : W := mkw 0x11ceee15e2e7ceaa 0x88e7770af173e755 0xee8cfe3fe0c78fff 0xf7467f1ff063c7ff

def z386 : W := mkw 0x0231168c48512000 0x01188b4624289000 0x7f731fccff79f000 0x3fb98fe67fbcf800

def z387 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x6e00fe0ce0418f99 0xb7007f067020c7cc

def z388 : W := mkw 0x9bffdc8f48000000 0x4dffee47a4000000 0x5dfffe0f00000000 0x2effff0780000000

def z389 : W := mkw 0x9a7d7e9fe84386aa 0x4d3ebf4ff421c355 0xeefcfe3fe0c78fff 0xf77e7f1ff063c7ff

def z390 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x7b7001cc03780199 0xbdb800e601bc00cc

def z391 : W := mkw 0x11effa10a2f7eea0 0x88f7fd08517bf750 0x7ffffe30e3ffffe1 0x3fffff1871fffff0

def z392 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x937001ff033801ff 0xc9b800ff819c00ff

def z393 : W := mkw 0xbffffffffd5bb7ba 0x5ffffffffeaddbdd 0xffffffffffffffff 0xffffffffffffffff

def z394 : W := mkw 0x4402a170b500dbe0 0x220150b85a806df0 0x0603e1f0fc01ffe1 0x0301f0f87e00fff0

def z395 : W := mkw 0x0000000002a40044 0x0000000001520022 0x8000000000860066 0x4000000000430033

def z396 : W := mkw 0x40000040250093e0 0x20000020128049f0 0x00000000000001e1 0x00000000000000f0

def z397 : W := mkw 0x0000060440410008 0x0000030220208004 0x08001e0c00400018 0x84000f060020000c

def z398 : W := mkw 0x22357edded59b198 0x111abf6ef6acd8cc 0x7fffffffff79f199 0xbfffffffffbcf8cc

def z399 : W := mkw 0x9ffffdffd9080110 0x4ffffeffec840088 0x7fffffffff780199 0xbfffffffffbc00cc

def z400 : W := mkw 0x106fda0000776c00 0x8837ed00003bb600 0x0c7ffe00007ffe00 0x063fff00003fff00

def z401 : W := mkw 0x223116cc6ffdb1dc 0x11188b6637fed8ee 0xff731fccfffff1ff 0xffb98fe67ffff8ff

def z402 : W := mkw 0x2bf917ee4bfd215c 0x15fc8bf725fe90ae 0xfbfc1fff03fe01ff 0xfdfe0fff81ff00ff

def z403 : W := mkw 0x00002210a04386aa 0x000011085021c355 0xe680e030e0c78fff 0xf34070187063c7ff

def z404 : W := mkw 0x55eff970b780dbe0 0x2af7fcb85bc06df0 0x7ffffff0ff81ffe1 0x3ffffff87fc0fff0

def z405 : W := mkw 0x00000604604386aa 0x000003023021c355 0xee001e0ce0c78fff 0xf7000f067063c7ff

def z406 : W := mkw 0x00044a0000430400 0x0002250000218200 0x080c1e0000460000 0x04060f0000230000

def z407 : W := mkw 0x9a79108a08000000 0x4d3c884504000000 0x0070000000000000 0x0038000000000000

def z408 : W := mkw 0x0000004001000100 0x0000002000800080 0x730001c003000181 0x398000e0018000c0

def z409 : W := mkw 0x9627fc15d8000000 0x4b13fe0aec000000 0x4e8ffe3ffc000000 0x2747ff1ffe000000

def z410 : W := mkw 0x00000000200082a0 0x0000000010004150 0x2000000000818fe1 0x100000000040c7f0

def z411 : W := mkw 0x223110c82d18b190 0x11188864168c58c8 0x777301c0ff39f181 0x3bb980e07f9cf8c0

def z412 : W := mkw 0x01d800c803ac0110 0x00ec006401d60088 0x7bfc01cc03fe0199 0xbdfe00e601ff00cc

def z413 : W := mkw 0x44002170b50093e0 0x220010b85a8049f0 0x770301f0ff01f1e1 0x3b8180f87f80f8f0

def z414 : W := mkw 0x223116cc6ffffd98 0x91188b6637fffecc 0x7f731fccffffff99 0xbfb98fe67fffffcc

def z415 : W := mkw 0x0048000000240000 0x0024000000120000 0x087c0000007e0000 0x043e0000003f0000

def z416 : W := mkw 0x221024dded0893ba 0x1108126ef68449dd 0x820001fffc0001ff 0xc10000fffe0000ff

def z417 : W := mkw 0x085c6e9fe06f86be 0x042e374ff037c35f 0xeefcfe3fe0ff8fff 0xf77e7f1ff07fc7ff

def z418 : W := mkw 0x661025fcfd0893f8 0x330812fe7e8449fc 0x020001fcfc0001f9 0x810000fe7e0000fc

def z419 : W := mkw 0x09dc69fb83ae0776 0x04ee34fdc1d703bb 0xfbfce1ff03fe0fff 0xfdfe70ff81ff07ff

def z420 : W := mkw 0x9dceed37d0000000 0x4ee7769be8000000 0x4e8cfe3fe0000000 0x27467f1ff0000000

def z421 : W := mkw 0x9ffffdffd9080154 0x4ffffeffec8400aa 0xdffffffffc0001ff 0xeffffffffe0000ff

def z422 : W := mkw 0x222116446d51b188 0x11108b2236a8d8c4 0x77031fc0ff01f181 0x3b818fe07f80f8c0

def z423 : W := mkw 0x0182800000000000 0x00c1400000000000 0x5583e00000000000 0x2ac1f00000000000

def z424 : W := mkw 0x0858008a002c0014 0x042c00450016000a 0x0070000000380000 0x00380000001c0000

def z425 : W := mkw 0xdffffdffdf805940 0x6ffffeffefc02ca0 0x5fffffffff007000 0x2fffffffff803800

def z426 : W := mkw 0x200006446559b198 0x1000032232acd8cc 0x6e001e0ce379f199 0xb7000f0671bcf8cc

def z427 : W := mkw 0x55ebb170b7b4fbe0 0xaaf5d8b85bda7df0 0x77f3e1f0ffb9ffe1 0x3bf9f0f87fdcfff0

def z428 : W := mkw 0x00046e55e3ef87fe 0x0002372af1f7c3ff 0xee8cfe3fe3ff8fff 0xf7467f1ff1ffc7ff

def z429 : W := mkw 0x0182a010a280caa0 0x00c1500851406550 0x7783e030e381ffe1 0x3bc1f01871c0fff0

def z430 : W := mkw 0x9ffb91ea1bac0154 0x4ffdc8f50dd600aa 0x117301c01f380000 0x08b980e00f9c0000

def z431 : W := mkw 0x085c4e8f406f041e 0x042e2747a037820f 0x887c1e0f007e001e 0xc43e0f07803f000f

def z432 : W := mkw 0x000004054000000a 0x00000202a0000005 0x8000000f0000001e 0xc00000078000000f

def z433 : W := mkw 0x2231108808182010 0x11188844040c1008 0x0070000000380000 0x00380000001c0000

def z434 : W := mkw 0x4586e93192824e62 0x22c37498c9412731 0x808ce03300860e66 0x4046701980430733

def z435 : W := mkw 0x44002170b780dbe0 0x220010b85bc06df0 0x220001f0ff81ffe1 0x110000f87fc0fff0

def z436 : W := mkw 0x0000201180000222 0x00001008c0000111 0x8000003300000066 0x4000001980000033

def z437 : W := mkw 0x9ffbb1ba98000000 0x4ffdd8dd4c000000 0x57f3e1f0fc000000 0x2bf9f0f87e000000

def z438 : W := mkw 0x9ffffdffdb800140 0x4ffffeffedc000a0 0x7fffffffff8001e1 0x3fffffffffc000f0

def z439 : W := mkw 0x0186ee15e2c3ceaa 0x00c3770af161e755 0xff8ffe3fe3c7ffff 0xffc7ff1ff1e3ffff

def z440 : W := mkw 0x01c8004003ac0154 0x00e4002001d600aa 0xf9fc000003fe01ff 0xfcfe000001ff00ff

def z441 : W := mkw 0x00002614e04182a8 0x0000130a7020c154 0x6e80fe3ce0c18ff9 0xb7407f1e7060c7fc

def z442 : W := mkw 0x0180012000000000 0x00c0009000000000 0x538001f000000000 0x29c000f800000000

def z443 : W := mkw 0x9dcee93392a40044 0x4ee77499c9520022 0x808ce03300860066 0x4046701980430033

def z444 : W := mkw 0x00044e0460438488 0x000227023021c244 0x6e8cfe0ce0c78f99 0xb7467f067063c7cc

def z445 : W := mkw 0x9ffb91aa1ab46800 0xcffdc8d50d5a3400 0x117301c01f387000 0x08b980e00f9c3800

def z446 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x79fc01c003fe0000 0x3cfe00e001ff0000

def z447 : W := mkw 0x0182800002804800 0x00c1400001402400 0x1103000003007000 0x0881800001803800

def z448 : W := mkw 0x00046a10a04386a0 0x000235085021c350 0x6e8cfe30e0c78fe1 0x37467f187063c7f0

def z449 : W := mkw 0x0000020000772400 0x80000100003b9200 0x00000000007e0000 0x00000000003f0000

def z450 : W := mkw 0x49d801ea27acdbf4 0x24ec00f513d66dfa 0xfbfc01ff03ffffff 0xfdfe00ff81ffffff

def z451 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x91fc01f303be0066 0x48fe00f981df0033

def z452 : W := mkw 0x106d5a0000772400 0x8836ad00003b9200 0x6cfcfe0000ff8e00 0x367e7f00007fc700

def z453 : W := mkw 0x9a7d5c8f482c0014 0x4d3eae47a416000a 0x887c1e0f007e001e 0xc43e0f07803f000f

def z454 : W := mkw 0x8fd825ffdbac0154 0x47ec12ffedd600aa 0xfbfc01fffffe01ff 0xfdfe00ffffff00ff

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0x62800030008001e1 0x31400018004000f0

def z456 : W := mkw 0x2231168c6c59b098 0x11188b46362cd84c 0x0c731e0cfc79f018 0x86398f067e3cf80c

def z457 : W := mkw 0x55eb916017b47940 0xaaf5c8b00bda3ca0 0x117301c01f387000 0x08b980e00f9c3800

def z458 : W := mkw 0x44002170b50093e0 0x220010b85a8049f0 0x6680e1f0fc818fe1 0x334070f87e40c7f0

def z459 : W := mkw 0x86002415d8000000 0x4300120aec000000 0x00000000fc000000 0x000000007e000000

def z460 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x1573ffc0fc000000 0x0ab9ffe07e000000

def z461 : W := mkw 0x9e37fdbfd8000000 0x4f1bfedfec000000 0x0603fffffc000000 0x0301fffffe000000

def z462 : W := mkw 0x1027d80000000000 0x0813ec0000000000 0x0403fe0000000000 0x0201ff0000000000

def z463 : W := mkw 0x0021120000512000 0x0010890000289000 0x08701e0000780000 0x04380f00003c0000

def z464 : W := mkw 0x0000004025009180 0x00000020128048c0 0x200000000301f181 0x100000000180f8c0

def z465 : W := mkw 0x0021120002f76c00 0x80108900017bb600 0x7d731e0003fffe00 0x3eb98f0001ffff00

def z466 : W := mkw 0x0810008a00080014 0x040800450004000a 0x8000000f0000001e 0xc00000078000000f

def z467 : W := mkw 0x4dcaa13292a44a64 0x26e5509949522532 0x808ce03300860e66 0x4046701980430733

def z468 : W := mkw 0x11ceca0002e74c00 0x88e765000173a600 0x6c8cfe0000c78e00 0x36467f000063c700

def z469 : W := mkw 0x23b396cc6fd9f998 0x11d9cb6637ecfccc 0x7ff3ffccfff9ff99 0xbff9ffe67ffcffcc

def z470 : W := mkw 0x09d801ea01080154 0x04ec00f5008400aa 0xdbfc01ff000001ff 0xedfe00ff800000ff

def z471 : W := mkw 0x200002402559b198 0x1000012012acd8cc 0x770301c0ff79f199 0xbb8180e07fbcf8cc

def z472 : W := mkw 0xd7a7fd75ff80dbe0 0x6bd3febaffc06df0 0x7783fff0ff81ffe1 0x3bc1fff87fc0fff0

def z473 : W := mkw 0x13ffdc8c48000000 0x09ffee4624000000 0x5fffffccfc000000 0x2fffffe67e000000

def z474 : W := mkw 0x11efd80002a40000 0x08f7ec0001520000 0x7dfffe0003fe0000 0x3effff0001ff0000

def z475 : W := mkw 0x00002415e00082aa 0x0000120af0004155 0xe680e03fe0818fff 0xf340701ff040c7ff

def z476 : W := mkw 0x0004681180000000 0x00023408c0000000 0x008ce03300000000 0x0046701980000000

def z477 : W := mkw 0x11efdb6003f76d40 0x88f7edb001fbb6a0 0x7ffffff003ffffe1 0x3ffffff801fffff0

def z478 : W := mkw 0xcf92a5ffff80dbe0 0x67c952ffffc06df0 0x7783e1ffff81ffe1 0x3bc1f0ffffc0fff0

def z479 : W := mkw 0x001006cc61498198 0x0008036630a4c0cc 0x7f701fcce3798199 0xbfb80fe671bcc0cc

def z480 : W := mkw 0x9a7d7c9fc8000000 0x4d3ebe4fe4000000 0x4efcfe3fe0000000 0x277e7f1ff0000000

def z481 : W := mkw 0x11effe15c2f76c00 0x88f7ff0ae17bb600 0x7ffffe3fe3fffe00 0x3fffff1ff1ffff00

def z482 : W := mkw 0x8e3135bfd8000000 0x47189adfec000000 0x5f731ffffc000000 0x2fb98ffffe000000

def z483 : W := mkw 0x07b3b5bcd8000000 0x03d9dade6c000000 0x5ff3fffcfc000000 0x2ff9fffe7e000000

def z484 : W := mkw 0x4582816017805940 0x22c140b00bc02ca0 0x7583e1c01f81fe00 0x3ac1f0e00fc0ff00

def z485 : W := mkw 0x9feffd37d8000000 0x4ff7fe9bec000000 0x048ffe33fc000000 0x0247ff19fe000000

def z486 : W := mkw 0x0000000020008080 0x0000000010004040 0x66000000e0018181 0x330000007000c0c0

def z487 : W := mkw 0x9fffddaf58000000 0x4fffeed7ac000000 0x197f1fcf1c000000 0x0cbf8fe78e000000

def z488 : W := mkw 0x4406ee15f443deaa 0x2203770afa21ef55 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z489 : W := mkw 0x2bfd7fffefffb7fe 0x15febffff7ffdbff 0xffffffffffffffff 0xffffffffffffffff

def z490 : W := mkw 0x002116046051a088 0x00108b023028d044 0x7f731e0ce379f199 0xbfb98f0671bcf8cc

def z491 : W := mkw 0x223136dced59b3b8 0x11189b6e76acd9dc 0x7ff3fffcfff9fff9 0xbff9fffe7ffcfffc

def z492 : W := mkw 0x19fd5bea03ff2554 0x8cfeadf501ff92aa 0xfbfc1fff03fe01ff 0xfdfe0fff81ff00ff

def z493 : W := mkw 0x0210048c48000000 0x0108024624000000 0x020001ccfc000000 0x010000e67e000000

def z494 : W := mkw 0x27b3b7fcfd59b198 0x13d9dbfe7eacd8cc 0x7ff3fffcff79f199 0xbff9fffe7fbcf8cc

def z495 : W := mkw 0x4582a130b400daa0 0x22c150985a006d50 0x5783e1f0fc01fe00 0x2bc1f0f87e00ff00

def z496 : W := mkw 0x0021120000512000 0x0010890000289000 0x04031e000001f000 0x02018f000000f800

def z497 : W := mkw 0x081001ea03ac0154 0x040800f501d600aa 0xa20001ff03fe01ff 0xd10000ff81ff00ff

def z498 : W := mkw 0x01c8020002f76c00 0x80e40100017bb600 0x79fc000003fffe00 0x3cfe000001ffff00

def z499 : W := mkw 0x11efd80002b46800 0x88f7ec00015a3400 0x5dfffe0003387000 0x2effff00019c3800

def z500 : W := mkw 0x221004cc6d089198 0x11080266368448cc 0x770301ccff01f199 0xbb8180e67f80f8cc

def z501 : W := mkw 0x458281603780dbe0 0x22c140b01bc06df0 0x310301c01f81ffe1 0x188180e00fc0fff0

def z502 : W := mkw 0x4402800014005800 0x220140000a002c00 0x000300001c007000 0x000180000e003800

def z503 : W := mkw 0x106d5e054077240a 0x8836af02a03b9205 0x887c1e0f007e001e 0xc43e0f07803f000f

def z504 : W := mkw 0x9bffde8f4af76c00 0xcdffef47a57bb600 0x7dfffe0f03fffe00 0x3effff0781ffff00

def z505 : W := mkw 0x085800ca012c0114 0x042c00650096008a 0xfb7c01cf037e019f 0xfdbe00e781bf00cf

def z506 : W := mkw 0x00046c15e00082a0 0x0002360af0004150 0x6e8cfe3fe0818fe1 0x37467f1ff040c7f0

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x7970000003780000 0x3cb8000001bc0000

def z508 : W := mkw 0x2bf911ea0fbc3154 0x15fc88f507de18aa 0x117301c01f387000 0x08b980e00f9c3800

def z509 : W := mkw 0x106d5a0002f76c00 0x8836ad00017bb600 0x287c1e0003fffe00 0x143e0f0001ffff00

def z510 : W := mkw 0x23b117ec6fd9b1d8 0x11d88bf637ecd8ec 0x7ff31ffcfff9f1f9 0xbff98ffe7ffcf8fc

def z511 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x828c01ff008601ff 0xc14600ff804300ff

def z512 : W := mkw 0x663137fcfd59b3f8 0x33189bfe7eacd9fc 0x7f731ffcff79f1f9 0xbfb98ffe7fbcf8fc

def z513 : W := mkw 0xdffffdbfda804a60 0x6ffffedfed402530 0x5ffffffffc800e60 0x2ffffffffe400730

def z514 : W := mkw 0x22355e8d485b241a 0x111aaf46a42d920d 0x887c1e0f007e001e 0xc43e0f07803f000f

def z515 : W := mkw 0x9fffffbfd8536c00 0xcfffffdfec29b600 0x5ffffffffc01fe00 0x2ffffffffe00ff00

def z516 : W := mkw 0x33ffdecc6d59b198 0x19ffef6636acd8cc 0x7fffffccff79f199 0xbfffffe67fbcf8cc

def z517 : W := mkw 0x0002800000004800 0x0001400000002400 0x0403e0000001fe00 0x0201f0000000ff00

def z518 : W := mkw 0x1069100000342000 0x88348800001a1000 0x0070000000380000 0x00380000001c0000

def z519 : W := mkw 0x11eb920002f76c00 0x88f5c900017bb600 0x3173000003fffe00 0x18b9800001ffff00

def z520 : W := mkw 0x09d801aa02a40000 0x04ec00d501520000 0x7bfc01ff03fe0000 0x3dfe00ff81ff0000

def z521 : W := mkw 0x623116cc6fd9fbf8 0x31188b6637ecfdfc 0x7f731fccfff9fff9 0xbfb98fe67ffcfffc

def z522 : W := mkw 0x00002415c0000000 0x0000120ae0000000 0x0200003fe0000000 0x0100001ff0000000

def z523 : W := mkw 0x0858008a00000000 0x042c004500000000 0x087c000f00000000 0x043e000780000000

def z524 : W := mkw 0x00046e55e54397aa 0x0002372af2a1cbd5 0xff8fffffffc7ffff 0xffc7ffffffe3ffff

def z525 : W := mkw 0x9ffffffffbef87fe 0x4ffffffffdf7c3ff 0xffffffffffff8fff 0xffffffffffffc7ff

def z526 : W := mkw 0x77fffffcfffffff8 0xbbfffffe7ffffffc 0x7ffffffcfffffff9 0xbffffffe7ffffffc

def z527 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0xfffffffffcc601ff 0xfffffffffe6300ff

def z528 : W := mkw 0x11a7da0002d36c00 0x88d3ed000169b600 0x7583fe000381fe00 0x3ac1ff0001c0ff00

def z529 : W := mkw 0x4586e971b782dfe2 0x22c374b8dbc16ff1 0xf78fe1f3ff87ffe7 0x7bc7f0f9ffc3fff3

def z530 : W := mkw 0x00044e054043040a 0x00022702a0218205 0xec8cfe0f00c78e1e 0xf6467f078063c70f

def z531 : W := mkw 0x4ddeeffff7efdffe 0x26ef77fffbf7efff 0xffffffffffffffff 0xffffffffffffffff

def z532 : W := mkw 0x11ca800002a44800 0x88e5400001522400 0x0000000000000000 0x0000000000000000

def z533 : W := mkw 0x8e1025bff80082aa 0x470812dffc004155 0x820001fffc0001ff 0xc10000fffe0000ff

def z534 : W := mkw 0x2a79168e487d201c 0x153c8b47243e900e 0x887c1e0f007e001e 0xc43e0f07803f000f

def z535 : W := mkw 0x00046a1180430622 0x00023508c0218311 0xec8cfe3300c78e66 0x76467f198063c733

def z536 : W := mkw 0x222110000c103000 0x1110880006081800 0x000300001c007000 0x000180000e003800

def z537 : W := mkw 0x00146edde14b87ba 0x000a376ef0a5c3dd 0xfffcffffe3ff8fff 0xfffe7ffff1ffc7ff

def z538 : W := mkw 0xbffffdfffd089198 0x5ffffefffe8448cc 0x5ffffffffc000199 0xaffffffffe0000cc

def z539 : W := mkw 0x09d801aa02ac0054 0x04ec00d50156002a 0x88fc003f00fe007e 0xc47e001f807f003f

def z540 : W := mkw 0x22357e9de85ba6ba 0x111abf4ef42dd35d 0xeefcfe3fe0ff8fff 0xf77e7f1ff07fc7ff

def z541 : W := mkw 0x400000402780dbe0 0x2000002013c06df0 0x770301c0ff81ffe1 0x3b8180e07fc0fff0

def z542 : W := mkw 0x0000020000410000 0x0000010000208000 0x6c001e0000418000 0x36000f000020c000

def z543 : W := mkw 0x458281603780d9c0 0x22c140b01bc06ce0 0x770301c0ff01f181 0x3b8180e07f80f8c0

def z544 : W := mkw 0x19cec92202a64c44 0x8ce7649101532622 0x808ce03300860e66 0x4046701980430733

def z545 : W := mkw 0x4582a170b7acdbf4 0x22c150b85bd66dfa 0xf783e1f0ffffffff 0xfbc1f0f87fffffff

def z546 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x08fcfe0000fe0e00 0x047e7f00007f0700

def z547 : W := mkw 0x09c8012202a40044 0x04e4009101520022 0xf9fc003303fe0066 0x7cfe001981ff0033

def z548 : W := mkw 0x001000c801080110 0x0008006400840088 0x117001c003380000 0x08b800e0019c0000

def z549 : W := mkw 0x0000000002a40000 0x0000000001520000 0x2000000003fe0000 0x1000000001ff0000

def z550 : W := mkw 0x22355ecc6d5bb598 0x111aaf6636addacc 0x7fffffccffffff99 0xbfffffe67fffffcc

def z551 : W := mkw 0x9ddee9bb90000000 0x4eef74ddc8000000 0x5bfce1ff00000000 0x2dfe70ff80000000

def z552 : W := mkw 0x00257e15e053a6aa 0x0012bf0af029d355 0xfffffe3fe3ffffff 0xffffff1ff1ffffff

def z553 : W := mkw 0x4dda81ea17ac5954 0x26ed40f50bd62caa 0x117301c01f387000 0x08b980e00f9c3800

def z554 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x8a0c1e3fe04601ff 0xc5060f1ff02300ff

def z555 : W := mkw 0x081001ea01080154 0x040800f5008400aa 0xea8c01ff00c601ff 0xf54600ff806300ff

def z556 : W := mkw 0x0021100000102000 0x0010880000081000 0x1173000003387000 0x08b98000019c3800

def z557 : W := mkw 0x09dc6dffc3ac0154 0x04ee36ffe1d600aa 0xfffcffffe3fe01ff 0xfffe7ffff1ff00ff

def z558 : W := mkw 0xdffffdfffd0093e0 0x6ffffefffe8049f0 0x5ffffffffc0001e1 0x2ffffffffe0000f0

def z559 : W := mkw 0x09dc4bea03ef0554 0x04ee25f501f782aa 0xfffcffff03ff8fff 0xfffe7fff81ffc7ff

def z560 : W := mkw 0x55effa10b6f7fea0 0xaaf7fd085b7bff50 0x7dfffe00fffffe00 0x3effff007fffff00

def z561 : W := mkw 0x9a7d5e8f4843040a 0x4d3eaf47a4218205 0x887c1e0f0046001e 0xc43e0f078023000f

def z562 : W := mkw 0x9fffffbffaf7eeaa 0xcfffffdffd7bf755 0xffffffffffffffff 0xffffffffffffffff

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x8200003f000001ff 0xc100001f800000ff

def z564 : W := mkw 0x223114cc6d18b198 0x11188a66368c58cc 0x137301ccff387199 0x89b980e67f9c38cc

def z565 : W := mkw 0x9627fe15f84386aa 0x4b13ff0afc21c355 0x0403fe00fc018e00 0x0201ff007e00c700

def z566 : W := mkw 0x9fdeedbfd8000000 0x4fef76dfec000000 0x028ce1fffc000000 0x014670fffe000000

def z567 : W := mkw 0x9fffffbfd8772400 0xcfffffdfec3b9200 0x5ffffffffc7e0000 0x2ffffffffe3f0000

def z568 : W := mkw 0x55a7fb70b7d3ffe0 0xaad3fdb85be9fff0 0x7783fff0ff81ffe1 0x3bc1fff87fc0fff0

def z569 : W := mkw 0x09dc6fbfe04386aa 0x04ee37dff021c355 0xfffcffffe0c78fff 0xfffe7ffff063c7ff

def z570 : W := mkw 0x9fffffbfd8430400 0x4fffffdfec218200 0x7ffffffffcc78e00 0x3ffffffffe63c700

def z571 : W := mkw 0x11effc15c0000000 0x08f7fe0ae0000000 0x5ffffe3fe0000000 0x2fffff1ff0000000

def z572 : W := mkw 0x09d821faa3ac83f4 0x04ec10fd51d641fa 0xfffce1ffe3ff8fff 0xfffe70fff1ffc7ff

def z573 : W := mkw 0x9dcee93390020622 0x4ee77499c8010311 0x808ce03300860e66 0x4046701980430733

def z574 : W := mkw 0x2a1005ee6d0891dc 0x150802f7368448ee 0x820001fffc0001ff 0xc10000fffe0000ff

def z575 : W := mkw 0x202112402559b198 0x1010892012acd8cc 0x7d731e000379f199 0xbeb98f0001bcf8cc

def z576 : W := mkw 0x9ffffdfffd009180 0x4ffffefffe8048c0 0x7fffffffff01f181 0x3fffffffff80f8c0

def z577 : W := mkw 0xddcee973b780dbe0 0x6ee774b9dbc06df0 0x778fe1f3ff81ffe1 0x3bc7f0f9ffc0fff0

def z578 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0xb17001c003fe01ff 0xd8b800e001ff00ff

def z579 : W := mkw 0x44046f75f54397ea 0x220237bafaa1cbf5 0xee8cfffffcc78fff 0xf7467ffffe63c7ff

def z580 : W := mkw 0x09dc6dbfc0000000 0x04ee36dfe0000000 0x5ffcffffe0000000 0x2ffe7ffff0000000

def z581 : W := mkw 0x2231168c6859a098 0x11188b46342cd04c 0x6e701e0ce0798199 0xb7380f06703cc0cc

def z582 : W := mkw 0x0000024003ff6d54 0x8000012001ffb6aa 0xa000000003ffffff 0xd000000001ffffff

def z583 : W := mkw 0x0582a13090000000 0x02c1509848000000 0x0080e03000000000 0x0040701800000000

def z584 : W := mkw 0x11effe15e2f7eeaa 0x88f7ff0af17bf755 0x7dfffe00e3fffe00 0x3effff0071ffff00

def z585 : W := mkw 0x0000000000020622 0x0000000000010311 0x8000000000860e66 0x4000000000430733

def z586 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x048ffe000087fe00 0x0247ff000043ff00

def z587 : W := mkw 0x55efff75f7f7ffea 0xaaf7ffbafbfbfff5 0xffffffffffffffff 0xffffffffffffffff

def z588 : W := mkw 0x0000016001000140 0x000000b0008000a0 0x020001f0000001e1 0x010000f8000000f0

def z589 : W := mkw 0x4d92a1fab788dbf4 0x26c950fd5bc46dfa 0xf783e1ffff81ffff 0xfbc1f0ffffc0ffff

def z590 : W := mkw 0x0000000002a64c00 0x8000000001532600 0x0000000000860e00 0x0000000000430700

def z591 : W := mkw 0x2231168c48592018 0x11188b46242c900c 0x7d731e0c0379f018 0xbeb98f0601bcf80c

def z592 : W := mkw 0x55effb3092f76e60 0xaaf7fd98497bb730 0x7dfffe3003fffe60 0x3effff1801ffff30

def z593 : W := mkw 0x11efda0022f7eeaa 0x88f7ed00117bf755 0xfdfffe0003ffffff 0xfeffff0001ffffff

def z594 : W := mkw 0x01cc6e15e2e786aa 0x00e6370af173c355 0xfffcfe3fe3ff8fff 0xfffe7f1ff1ffc7ff

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x688c000000c60000 0x3446000000630000

def z596 : W := mkw 0x2221160448512008 0x11108b0224289004 0x00001e0000000000 0x00000f0000000000

def z597 : W := mkw 0x0010008800000000 0x0008004400000000 0x5b7001cc00000000 0x2db800e600000000

def z598 : W := mkw 0x01c8000002a40000 0x00e4000001520000 0x1170000003380000 0x08b80000019c0000

def z599 : W := mkw 0x9ffffdbfd8020622 0x4ffffedfec010311 0xdffffffffc860e66 0x6ffffffffe430733

def z600 : W := mkw 0x09f913ea03fd2154 0x04fc89f501fe90aa 0xffff1fff03fff1ff 0xffff8fff81fff8ff

def z601 : W := mkw 0x0582a130b00082a0 0x02c1509858004150 0x7783e1f0fc818fe1 0x3bc1f0f87e40c7f0

def z602 : W := mkw 0x2a7916ce6d7db19c 0x153c8b6736bed8ce 0xff7f1fcfff7ff19f 0xffbf8fe7ffbff8cf

def z603 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0xffff1ffffffff1ff 0xffff8ffffffff8ff

def z604 : W := mkw 0x223110c80d183110 0x11188864068c1888 0x7b7301cc1f787199 0xbdb980e60fbc38cc

def z605 : W := mkw 0x2bf917ee6ffdb1dc 0x15fc8bf737fed8ee 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z606 : W := mkw 0x4400016015001140 0x220000b00a8008a0 0x000001c01c000000 0x000000e00e000000

def z607 : W := mkw 0x67b397ec7fd9f9d8 0x33d9cbf63fecfcec 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z608 : W := mkw 0x67a3b774ffd1fbe8 0x33d1dbba7fe8fdf4 0x7783fff0ff81ffe1 0x3bc1fff87fc0fff0

def z609 : W := mkw 0x6633b6dcfd59fbb8 0x3319db6e7eacfddc 0x7f73ffccff79ff99 0xbfb9ffe67fbcffcc

def z610 : W := mkw 0x19dec9ea03ae4d54 0x8cef64f501d726aa 0xfbfce1ff03fe0fff 0xfdfe70ff81ff07ff

def z611 : W := mkw 0x9deff93390000000 0x4ef7fc99c8000000 0x5dfffe3300000000 0x2effff1980000000

def z612 : W := mkw 0x09d801ea01080110 0x04ec00f500840088 0x7bfc01ff03780199 0xbdfe00ff81bc00cc

def z613 : W := mkw 0x0586ef35f04386aa 0x02c3779af821c355 0xff8ffffffcc78fff 0xffc7fffffe63c7ff

def z614 : W := mkw 0x09c8012202a40044 0x04e4009101520022 0xea8c003f00c601ff 0xf546001f806300ff

def z615 : W := mkw 0x33ffdac80fff7d10 0x99ffed6407ffbe88 0x7dffffc01ffffe00 0x3effffe00fffff00

def z616 : W := mkw 0x11cee81182a64e22 0x88e77408c1532711 0x808ce03300860e66 0x4046701980430733

def z617 : W := mkw 0x0000004005001100 0x0000002002800880 0x110301c01f007000 0x088180e00f803800

def z618 : W := mkw 0x001000c801080110 0x0008006400840088 0x020001cc00000199 0x810000e6000000cc

def z619 : W := mkw 0x0582812010000000 0x02c1409008000000 0x110301c01c000000 0x088180e00e000000

def z620 : W := mkw 0x4586ed75f780dbe0 0x22c376bafbc06df0 0x7f8fffffff81ffe1 0x3fc7ffffffc0fff0

def z621 : W := mkw 0x003112c801592110 0x0018896400ac9088 0x7f731fcc0379f199 0xbfb98fe601bcf8cc

def z622 : W := mkw 0x9ddee9fb93ac0154 0x4eef74fdc9d600aa 0xfbfce1ff03fe01ff 0xfdfe70ff81ff00ff

def z623 : W := mkw 0x0004480000020400 0x0002240000010200 0x008ce00000860e00 0x0046700000430700

def z624 : W := mkw 0x0000020000536c00 0x800001000029b600 0x000000000001fe00 0x000000000000ff00

def z625 : W := mkw 0x8a10048f48000000 0x45080247a4000000 0x0000000f00000000 0x0000000780000000

def z626 : W := mkw 0x9bfd5def4bac0154 0x4dfeaef7a5d600aa 0xfbfc1fff03fe01ff 0xfdfe0fff81ff00ff

def z627 : W := mkw 0x11efda4003ff6d54 0x88f7ed2001ffb6aa 0xfdfffe0003ffffff 0xfeffff0001ffffff

def z628 : W := mkw 0x00046e15c0430400 0x0002370ae0218200 0x6e8cfe3fe0c78e00 0x37467f1ff063c700

def z629 : W := mkw 0x00044e05604386aa 0x00022702b021c355 0xa80c1e0f00c78fff 0xd4060f078063c7ff

def z630 : W := mkw 0x187d5a8a007f2414 0x8c3ead45003f920a 0x887c1e0f007e001e 0xc43e0f07803f000f

def z631 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x848cfe33e0878e66 0x42467f19f043c733

def z632 : W := mkw 0x9406e81190000000 0x4a037408c8000000 0x0000e00000000000 0x0000700000000000

def z633 : W := mkw 0x22257e15ec53b6aa 0x1112bf0af629db55 0xee8ffe3ffcc7ffff 0xf747ff1ffe63ffff

def z634 : W := mkw 0x0582a17093800140 0x02c150b849c000a0 0x7783e1f0ff8001e1 0x3bc1f0f87fc000f0

def z635 : W := mkw 0x9ffffdffdbac0154 0x4ffffeffedd600aa 0x5fffffffff380000 0x2fffffffff9c0000

def z636 : W := mkw 0x1027fe15e053eeaa 0x8813ff0af029f755 0xee8ffe3fe0c7ffff 0xf747ff1ff063ffff

def z637 : W := mkw 0x400000002400daa0 0x2000000012006d50 0x000000000001fe00 0x000000000000ff00

def z638 : W := mkw 0xae3137fffd59b198 0x57189bfffeacd8cc 0x7f731fffff79f199 0xbfb98fffffbcf8cc

def z639 : W := mkw 0x2231168c48592018 0x11188b46242c900c 0x5f731fccfc780018 0xafb98fe67e3c000c

def z640 : W := mkw 0x0000004001080154 0x00000020008400aa 0x80000000000001ff 0xc0000000000000ff

def z641 : W := mkw 0x0004480000000000 0x0002240000000000 0x4c8cfe0000000000 0x26467f0000000000

def z642 : W := mkw 0x4ddaa1fa93ac4b74 0x26ed50fd49d625ba 0xfbfce1ff03fe0fff 0xfdfe70ff81ff07ff

def z643 : W := mkw 0x0180016003ac0154 0x00c000b001d600aa 0xf38001f003fe01ff 0xf9c000f801ff00ff

def z644 : W := mkw 0x0000000002b46800 0x80000000015a3400 0x0000000003387000 0x00000000019c3800

def z645 : W := mkw 0x08146fffe14b87fe 0x040a37fff0a5c3ff 0xee8cffffe0c78fff 0xf7467ffff063c7ff

def z646 : W := mkw 0x15effb3092f76c00 0x8af7fd98497bb600 0x7ffffff0fffffe00 0x3ffffff87fffff00

def z647 : W := mkw 0x4402a050b780dbe0 0x220150285bc06df0 0x2403e000ff81ffe1 0x1201f0007fc0fff0

def z648 : W := mkw 0x0221140448000000 0x01108a0224000000 0x04031e00fc000000 0x02018f007e000000

def z649 : W := mkw 0x0010008800080010 0x0008004400040008 0x0870000c00780018 0x84380006003c000c

def z650 : W := mkw 0x081001ea01080154 0x040800f5008400aa 0x000001c000000000 0x000000e000000000

def z651 : W := mkw 0x222116446d59b198 0x11108b2236acd8cc 0x24031e00ff79f199 0x92018f007fbcf8cc

def z652 : W := mkw 0x8f92a5bfd8000000 0x47c952dfec000000 0x5783e1fffc000000 0x2bc1f0fffe000000

def z653 : W := mkw 0x0231148c48000000 0x01188a4624000000 0x08701e0c00000000 0x04380f0600000000

def z654 : W := mkw 0x418001602780dbe0 0x20c000b013c06df0 0x738001f00381ffe1 0x39c000f801c0fff0

def z655 : W := mkw 0x0180012002800040 0x00c0009001400020 0x0080003000800060 0x0040001800400030

def z656 : W := mkw 0xdffffdbffc00daa0 0x6ffffedffe006d50 0x5ffffffffc01fe00 0x2ffffffffe00ff00

def z657 : W := mkw 0x223114cc6d089198 0x11188a66368448cc 0x5f731fccfc000199 0xafb98fe67e0000cc

def z658 : W := mkw 0x0000040440000000 0x0000020220000000 0x4e001e0ce0000000 0x27000f0670000000

def z659 : W := mkw 0xbffffffffffffd98 0xdffffffffffffecc 0x7fffffffffffff99 0xbfffffffffffffcc

def z660 : W := mkw 0x00044e054043040a 0x00022702a0218205 0xea8c1e3f00c601ff 0xf5460f1f806300ff

def z661 : W := mkw 0x223116cc49592118 0x11188b6624ac908c 0x7b701fcc03780199 0xbdb80fe601bc00cc

def z662 : W := mkw 0x55cee970b7a6dfe0 0xaae774b85bd36ff0 0x778fe1f0ff87ffe1 0x3bc7f0f87fc3fff0

def z663 : W := mkw 0x106d580000000000 0x0836ac0000000000 0x087c1e0000000000 0x043e0f0000000000

def z664 : W := mkw 0x9ffffdbff80082a0 0x4ffffedffc004150 0x7ffffffffc818fe1 0x3ffffffffe40c7f0

def z665 : W := mkw 0x67b3b1f8bf98fbf0 0x33d9d8fc5fcc7df8 0x77f3e1f0ffb9ffe1 0x3bf9f0f87fdcfff0

def z666 : W := mkw 0x4582a370b7c3dfea 0x22c151b85be1eff5 0xf783e1f0ffc7ffff 0xfbc1f0f87fe3ffff

def z667 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x4e8cfe3fe0018e00 0x27467f1ff000c700

def z668 : W := mkw 0x104c480000260400 0x8826240000130200 0x000c000000060000 0x0006000000030000

def z669 : W := mkw 0x09c8016203a40144 0x04e400b101d200a2 0xf38c01f3038601e7 0x79c600f981c300f3

def z670 : W := mkw 0x11efde0542f76c0a 0x88f7ef02a17bb605 0xfdfffe0f03fffe1e 0xfeffff0781ffff0f

def z671 : W := mkw 0x4dd821fab7ac93f4 0x26ec10fd5bd649fa 0xfbfc01fffffe01ff 0xfdfe00ffffff00ff

def z672 : W := mkw 0x00002615e04386aa 0x0000130af021c355 0xa200003fe0c78fff 0xd100001ff063c7ff

def z673 : W := mkw 0x0004681180020622 0x00023408c0010311 0xea8ce03f00c60fff 0xf546701f806307ff

def z674 : W := mkw 0x2210048c48080018 0x110802462404000c 0x0000000c00000018 0x800000060000000c

def z675 : W := mkw 0x44002575f50093ea 0x220012bafa8049f5 0x820001fffc0001ff 0xc10000fffe0000ff

def z676 : W := mkw 0x220004046c009088 0x1100020236004844 0x00000000fc000000 0x000000007e000000

def z677 : W := mkw 0x00000200204386aa 0x000001001021c355 0xea8c003f00c78fff 0xf546001f8063c7ff

def z678 : W := mkw 0x0182820002f76c00 0x80c14100017bb600 0x7583e00003fffe00 0x3ac1f00001ffff00

def z679 : W := mkw 0x0000020000430400 0x0000010000218200 0x2000000000c78e00 0x100000000063c700

def z680 : W := mkw 0xdffffffffff7ffe0 0xeffffffffffbfff0 0x7fffffffffffffe1 0x3ffffffffffffff0

def z681 : W := mkw 0x0000000000000000 0x0000000000000000 0x6a00000c00400199 0xb5000006002000cc

def z682 : W := mkw 0x11cec80000000000 0x08e7640000000000 0x008ce00000000000 0x0046700000000000

def z683 : W := mkw 0x0000024023ef87fe 0x0000012011f7c3ff 0xa000000003ff8fff 0xd000000001ffc7ff

def z684 : W := mkw 0x0000000024009080 0x0000000012004840 0x04030000fc01f000 0x020180007e00f800

def z685 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x0280e1f0fc800fe1 0x014070f87e4007f0

def z686 : W := mkw 0x3227de046c53fc88 0x9913ef023629fe44 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z687 : W := mkw 0x222116046c51b088 0x11108b023628d844 0x6e031e0cfc41f199 0xb7018f067e20f8cc

def z688 : W := mkw 0x9fffffffdbff6d54 0xcfffffffedffb6aa 0xffffffffffffffff 0xffffffffffffffff

def z689 : W := mkw 0x00002615e04182aa 0x0000130af020c155 0xee001e3fe04181ff 0xf7000f1ff020c0ff

def z690 : W := mkw 0x09cc6f37e2e786ee 0x04e6379bf173c377 0xee8cfe3fe0c78fff 0xf7467f1ff063c7ff

def z691 : W := mkw 0x67b391e81f987950 0x33d9c8f40fcc3ca8 0x117301c01f387000 0x08b980e00f9c3800

def z692 : W := mkw 0x00044e056043848a 0x00022702b021c245 0xee0c1e0fe047819f 0xf7060f07f023c0cf

def z693 : W := mkw 0x9fffd9aa18000000 0x4fffecd50c000000 0x5dffffc01c000000 0x2effffe00e000000

def z694 : W := mkw 0x45a3b370b7d1fbe0 0x22d1d9b85be8fdf0 0x7ff3fff0fff9ffe1 0x3ff9fff87ffcfff0

def z695 : W := mkw 0x09c8012202a40044 0x04e4009101520022 0x0000000000000000 0x0000000000000000

def z696 : W := mkw 0x45802170b78093e0 0x22c010b85bc049f0 0x738001f0ff8001e1 0x39c000f87fc000f0

def z697 : W := mkw 0x01c8016003a40140 0x00e400b001d200a0 0x7bfc01f003fe01e1 0x3dfe00f801ff00f0

def z698 : W := mkw 0x00044e054043040a 0x00022702a0218205 0x00001e0000000000 0x00000f0000000000

def z699 : W := mkw 0x9ffb91aa18000000 0x4ffdc8d50c000000 0x5bff01ff1c000000 0x2dff80ff8e000000

def z700 : W := mkw 0x1027da0000536c00 0x8813ed000029b600 0x6c8ffe0000c7fe00 0x3647ff000063ff00

def z701 : W := mkw 0xdffbb1fabf80dbe0 0x6ffdd8fd5fc06df0 0x77f3e1f0ff81ffe1 0x3bf9f0f87fc0fff0

def z702 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x06031fccfc01f199 0x83018fe67e00f8cc

def z703 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x997c01cf037e001e 0xccbe00e781bf000f

def z704 : W := mkw 0x9bfd5daf48000000 0x4dfeaed7a4000000 0x5bfc1fff00000000 0x2dfe0fff80000000

def z705 : W := mkw 0x8e1025ffd9080154 0x470812ffec8400aa 0x820001fffc0001ff 0xc10000fffe0000ff

def z706 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x73f001f003b801e1 0x39f800f801dc00f0

def z707 : W := mkw 0x106d5a0000772400 0x8836ad00003b9200 0x7dfffe0003fffe00 0x3effff0001ffff00

def z708 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x5f731fccff39f000 0x2fb98fe67f9cf800

def z709 : W := mkw 0x9e37fdbfd8000000 0x4f1bfedfec000000 0x0403ffc0fc000000 0x0201ffe07e000000

def z710 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0xa8fc003f03fe01ff 0xd47e001f81ff00ff

def z711 : W := mkw 0x2000024027fdf998 0x9000012013fefccc 0x200000000379f199 0x9000000001bcf8cc

def z712 : W := mkw 0x19efdb2202f76c00 0x8cf7ed91017bb600 0x7dfffe3303fffe00 0x3effff1981ffff00

def z713 : W := mkw 0x9ffffdbfda804800 0x4ffffedfed402400 0x5fffffffff007000 0x2fffffffff803800

def z714 : W := mkw 0x05a3b13090000000 0x02d1d89848000000 0x5ff3fff0fc000000 0x2ff9fff87e000000

def z715 : W := mkw 0x8a31148f48000000 0x45188a47a4000000 0x5f731fcffc000000 0x2fb98fe7fe000000

def z716 : W := mkw 0x0582a130b280caa0 0x02c1509859406550 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z717 : W := mkw 0x9a7d5e8f4877240a 0xcd3eaf47a43b9205 0x887c1e0f007e001e 0xc43e0f07803f000f

def z718 : W := mkw 0x9ffffdbfda804800 0x4ffffedfed402400 0x5ffffffffc800e00 0x2ffffffffe400700

def z719 : W := mkw 0x4402a010b400daa0 0x220150085a006d50 0x5703e1c0fc01fe00 0x2b81f0e07e00ff00

def z720 : W := mkw 0x4582a050b780dba0 0x22c150285bc06dd0 0x7783e1c0ff81ff81 0x3bc1f0e07fc0ffc0

def z721 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0xff7f1fcfff7ff19f 0xffbf8fe7ffbff8cf

def z722 : W := mkw 0x9ffffdbfdab46800 0xcffffedfed5a3400 0x7ffffffffffe7000 0x3fffffffffff3800

def z723 : W := mkw 0x9ffffdbfd8020622 0x4ffffedfec010311 0xfffffffffcc60fff 0xfffffffffe6307ff

def z724 : W := mkw 0x9637fc9dd8000000 0x4b1bfe4eec000000 0x0603ffccfc000000 0x0301ffe67e000000

def z725 : W := mkw 0x67b3b7bcdad96a78 0x33d9dbde6d6cb53c 0x08f0fe3c00f80e78 0x84787f1e007c073c

def z726 : W := mkw 0x001006cc65499198 0x0008036632a4c8cc 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z727 : W := mkw 0x223578d98d1a3732 0x111abc6cc68d1b99 0x91ffe1f31fbe7e66 0x48fff0f98fdf3f33

def z728 : W := mkw 0x8631349dd8000000 0x43189a4eec000000 0x5f731fccfc000000 0x2fb98fe67e000000

def z729 : W := mkw 0x44046e15f44396aa 0x2202370afa21cb55 0xee8cfe3ffcc78fff 0xf7467f1ffe63c7ff

def z730 : W := mkw 0x9ffffdbfd800000a 0x4ffffedfec000005 0xdffffffffc00001e 0xeffffffffe00000f

def z731 : W := mkw 0x01ed5a0002f72400 0x00f6ad00017b9200 0x7dfffe0003fffe00 0x3effff0001ffff00

def z732 : W := mkw 0x19efdb2202f76c44 0x8cf7ed91017bb622 0xfffffe3f03ffffff 0xffffff1f81ffffff

def z733 : W := mkw 0x20000240254b97ba 0x1000012012a5cbdd 0xa000000000c78fff 0xd00000000063c7ff

def z734 : W := mkw 0x4dcaa172b7a4dbe4 0x26e550b95bd26df2 0xffffe1f3ffffffe7 0x7ffff0f9fffffff3

def z735 : W := mkw 0x223116cc6d59b3b8 0x11188b6636acd9dc 0x7f731fccfff9fff9 0xbfb98fe67ffcfffc

def z736 : W := mkw 0x3227fe15ec53feaa 0x9913ff0af629ff55 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z737 : W := mkw 0x09d801ea07ac1154 0x04ec00f503d608aa 0xfbff01ff1ffe71ff 0xfdff80ff8fff38ff

def z738 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x7ff3e1f0fff9ffe1 0x3ff9f0f87ffcfff0

def z739 : W := mkw 0x4582a130b680dae0 0x22c150985b406d70 0x5783e1f0fc81fe60 0x2bc1f0f87e40ff30

def z740 : W := mkw 0x661024dcfd0893b8 0x3308126e7e8449dc 0x020001ccfc000199 0x810000e67e0000cc

def z741 : W := mkw 0x4000024027c3dfe0 0x2000012013e1eff0 0x2000000003c7ffe1 0x1000000001e3fff0

def z742 : W := mkw 0x4586cf6557c35d4a 0x22c367b2abe1aea5 0x990f1fcf1f46701e 0xcc878fe78fa3380f

def z743 : W := mkw 0x9ffffdbfdaa40000 0x4ffffedfed520000 0x5fffffffff380000 0x2fffffffff9c0000

def z744 : W := mkw 0x8fd801ea1bac0154 0x47ec00f50dd600aa 0xfbfc01ff1ffe01ff 0xfdfe00ff8fff00ff

def z745 : W := mkw 0x9dda81ea13ac0154 0x4eed40f509d600aa 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z746 : W := mkw 0x00046c15c0020622 0x0002360ae0010311 0xee8cfe3fe0c60fff 0xf7467f1ff06307ff

def z747 : W := mkw 0x600002402559fbb8 0x3000012012acfddc 0x200000000379ff99 0x9000000001bcffcc

def z748 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x7ffffe0c03ffff99 0xbfffff0601ffffcc

def z749 : W := mkw 0x11ebb415e2b4eaaa 0x88f5da0af15a7555 0x9373003fe33871ff 0xc9b9801ff19c38ff

def z750 : W := mkw 0x4402a170b500dbe0 0x220150b85a806df0 0x0403e1c0fc01fe00 0x0201f0e07e00ff00

def z751 : W := mkw 0x97a7fd35d8000000 0x4bd3fe9aec000000 0x1503ffc0fc000000 0x0a81ffe07e000000

def z752 : W := mkw 0x9ffffdbfdaa40000 0x4ffffedfed520000 0x5ffffffffc860000 0x2ffffffffe430000

def z753 : W := mkw 0x4402a050b500dba0 0x220150285a806dd0 0x1503e1c0ff01fe00 0x0a81f0e07f80ff00

def z754 : W := mkw 0x0582a13090004800 0x02c1509848002400 0x5783e1f0fc01fe00 0x2bc1f0f87e00ff00

def z755 : W := mkw 0x9ffb95ae58000000 0x4ffdcad72c000000 0x5fff1ffffc000000 0x2fff8ffffe000000

def z756 : W := mkw 0x202112402559b198 0x1010892012acd8cc 0x317300000379f199 0x98b9800001bcf8cc

def z757 : W := mkw 0xddcee93392a44a64 0x6ee77499c9522532 0x808ce03300860e66 0x4046701980430733

def z758 : W := mkw 0x200002402559b198 0x1000012012acd8cc 0x750300000379f199 0xba81800001bcf8cc

def z759 : W := mkw 0x0000000000000000 0x0000000000000000 0xfbfc003f03fe01ff 0xfdfe001f81ff00ff

def z760 : W := mkw 0x00046e15e053a6aa 0x0002370af029d355 0xee8cfe3fe3ffffff 0xf7467f1ff1ffffff

def z761 : W := mkw 0x9dcee93392a64e22 0xcee77499c9532711 0x808ce03300860e66 0x4046701980430733

def z762 : W := mkw 0x97b7fdbdd8000000 0x4bdbfedeec000000 0x5ff3fffcfc000000 0x2ff9fffe7e000000

def z763 : W := mkw 0x9ffffdbfdaac0014 0x4ffffedfed56000a 0xfffffffffffe001e 0xffffffffffff000f

def z764 : W := mkw 0x4582a13092804a60 0x22c1509849402530 0x7783e1f0ff81fe60 0x3bc1f0f87fc0ff30

def z765 : W := mkw 0x0231148c48000000 0x01188a4624000000 0x5fff1ffffc000000 0x2fff8ffffe000000

def z766 : W := mkw 0x09dc6fffe3ef87fe 0x04ee37fff1f7c3ff 0x1570ffc0e3398e00 0x0ab87fe0719cc700

def z767 : W := mkw 0x9627fd35d8000000 0x4b13fe9aec000000 0x0603fff0fc000000 0x0301fff87e000000

def z768 : W := mkw 0x0021100000000000 0x0010880000000000 0x5f731fc0fc000000 0x2fb98fe07e000000

def z769 : W := mkw 0x200002402559b198 0x1000012012acd8cc 0x797000000379f199 0xbcb8000001bcf8cc

def z770 : W := mkw 0x1837dbea015b6d54 0x8c1bedf500adb6aa 0x8603ffff0001ffff 0xc301ffff8000ffff

def z771 : W := mkw 0x09d801aa02a40000 0x04ec00d501520000 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z772 : W := mkw 0x9627fc55dbac0154 0x4b13fe2aedd600aa 0xa403fe00fffe01ff 0xd201ff007fff00ff

def z773 : W := mkw 0x200002402559b198 0x1000012012acd8cc 0xa000000003fff1ff 0xd000000001fff8ff

def z774 : W := mkw 0x1237dc8c48000000 0x091bee4624000000 0x5f73ffccfc000000 0x2fb9ffe67e000000

def z775 : W := mkw 0x6000024027d1fbe8 0x3000012013e8fdf4 0x200000000381ffe1 0x1000000001c0fff0

def z776 : W := mkw 0x4c5aa09ab42cdab4 0x262d504d5a166d5a 0x8c7fe00ffc7ffe1e 0xc63ff007fe3fff0f

def z777 : W := mkw 0x00000240254397aa 0x0000012012a1cbd5 0xa000000003c7ffff 0xd000000001e3ffff

def z778 : W := mkw 0x09da81ea03ac0154 0x04ed40f501d600aa 0xffffe1ff03fe01ff 0xfffff0ff81ff00ff

def z779 : W := mkw 0x0021120000512000 0x0010890000289000 0x7f731fc0ff79f000 0x3fb98fe07fbcf800

def z780 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x57f3fff0fc000000 0x2bf9fff87e000000

def z781 : W := mkw 0x223114cc6d18b198 0x11188a66368c58cc 0x5f731fccff387199 0xafb98fe67f9c38cc

def z782 : W := mkw 0x9ffffdbfdaa40000 0x4ffffedfed520000 0xfffffffffffe01ff 0xffffffffffff00ff

def z783 : W := mkw 0x9ffbb5bed8000000 0x4ffddadf6c000000 0x5ff3fffcfc000000 0x2ff9fffe7e000000

def z784 : W := mkw 0x2be917266ef5b0cc 0x15f48b93377ad866 0x848f1e33fc87f066 0x42478f19fe43f833

def z785 : W := mkw 0xdffb91ea1fac5954 0x6ffdc8f50fd62caa 0x117301c01f387000 0x08b980e00f9c3800

def z786 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x5783e1f0ff01fe00 0x2bc1f0f87f80ff00

def z787 : W := mkw 0x0231148c48000000 0x01188a4624000000 0xffff1ffffcc601ff 0xffff8ffffe6300ff

def z788 : W := mkw 0x9a7d7c9fc8000000 0x4d3ebe4fe4000000 0x5ffffffffc000000 0x2ffffffffe000000

def z789 : W := mkw 0x11efdb2002f76c40 0x88f7ed90017bb620 0x7dfffe3003fffe60 0x3effff1801ffff30

def z790 : W := mkw 0xddcee93392a64e60 0xeee77499c9532730 0x008ce03300860e60 0x0046701980430730

def z791 : W := mkw 0xbdceeb73b559b198 0x5ee775b9daacd8cc 0x208ce0330379f199 0x9046701981bcf8cc

def z792 : W := mkw 0x07b7fdbdd8000000 0x03dbfedeec000000 0x5ffffffffc000000 0x2ffffffffe000000

def z793 : W := mkw 0x00046c15e00082a0 0x0002360af0004150 0xee8cfe3fe0c78fff 0xf7467f1ff063c7ff

def z794 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x1703e1f0ff01ffe1 0x0b81f0f87f80fff0

def z795 : W := mkw 0x9637fc9dd8000000 0x4b1bfe4eec000000 0x1573ffc0fc000000 0x0ab9ffe07e000000

def z796 : W := mkw 0x0000004025009180 0x00000020128048c0 0x7783e1c0ff81ff81 0x3bc1f0e07fc0ffc0

def z797 : W := mkw 0x9ffffdbfdaa64e22 0xcffffedfed532711 0xdffffffffc860e66 0x6ffffffffe430733

def z798 : W := mkw 0x09da81ea03ac4954 0x04ed40f501d624aa 0xfbff01ff03fe71ff 0xfdff80ff81ff38ff

def z799 : W := mkw 0x6000024027dbfffa 0x3000012013edfffd 0xa000000003ffffff 0xd000000001ffffff

def z800 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0xff8ffffffcc78fff 0xffc7fffffe63c7ff

def z801 : W := mkw 0x9ffffdbfdaa40044 0x4ffffedfed520022 0x5ffffffffc000000 0x2ffffffffe000000

def z802 : W := mkw 0xddcaa172b780dbe0 0x6ee550b95bc06df0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z803 : W := mkw 0x4c1025fff50893fe 0x260812fffa8449ff 0x820001fffc0001ff 0xc10000fffe0000ff

def z804 : W := mkw 0x9ffffdbfdaa40044 0x4ffffedfed520022 0xfffffffffffe0066 0x7fffffffffff0033

def z805 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x1d7ffe00037ffe00 0x0ebfff0001bfff00

def z806 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x3573fe0003fffe00 0x1ab9ff0001ffff00

def z807 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x7ff3ffccfff9ff99 0xbff9ffe67ffcffcc

def z808 : W := mkw 0x223112c82d59b198 0x1118896416acd8cc 0x207000000379f199 0x9038000001bcf8cc

def z809 : W := mkw 0x9ffb95ae58000000 0x4ffdcad72c000000 0x15731fc0fc000000 0x0ab98fe07e000000

def z810 : W := mkw 0x9ffffdbfd82c0014 0x4ffffedfec16000a 0x5ffffffffc380000 0x2ffffffffe1c0000

def z811 : W := mkw 0x002116446551b188 0x00108b2232a8d8c4 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z812 : W := mkw 0x018281602780d9c0 0x00c140b013c06ce0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z813 : W := mkw 0x33decccc6faedd98 0x99ef666637d76ecc 0x028ce1ccfc860f99 0x814670e67e4307cc

def z814 : W := mkw 0x2231148c48080018 0x11188a462404000c 0x5f731fccfc000018 0xafb98fe67e00000c

def z815 : W := mkw 0x8e1027bfdaf76c00 0xc70813dfed7bb600 0x220001fffffffe00 0x110000ffffffff00

def z816 : W := mkw 0x44002170b50093e0 0x220010b85a8049f0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z817 : W := mkw 0x0231148c48102000 0x01188a4624081000 0x5f731fccff387000 0x2fb98fe67f9c3800

def z818 : W := mkw 0x2000024027ffffba 0x9000012013ffffdd 0xa000000003ffffff 0xd000000001ffffff

def z819 : W := mkw 0x000280402500d980 0x0001402012806cc0 0x7703e1c0ff01ff81 0x3b81f0e07f80ffc0

def z820 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0xfdfffe0f03fffe1e 0xfeffff0781ffff0f

def z821 : W := mkw 0x200002402559b198 0x1000012012acd8cc 0x000000000001f199 0x800000000000f8cc

def z822 : W := mkw 0x8e3115ae58000000 0x47188ad72c000000 0x5f731fccfc000000 0x2fb98fe67e000000

def z823 : W := mkw 0x97effd35d8000000 0x4bf7fe9aec000000 0x5ffffff0fc000000 0x2ffffff87e000000

def z824 : W := mkw 0x085801ea03ac0154 0x042c00f501d600aa 0xaa7c01ff03fe01ff 0xd53e00ff81ff00ff

def z825 : W := mkw 0x01d800c803ac0110 0x00ec006401d60088 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z826 : W := mkw 0x20046a51a55bb7ba 0x10023528d2addbdd 0xa08ce03303ffffff 0xd046701981ffffff

def z827 : W := mkw 0x9627fe15f853eeaa 0xcb13ff0afc29f755 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z828 : W := mkw 0x2231168c6c51b088 0x11188b463628d844 0x7f731fccff79f000 0x3fb98fe67fbcf800

def z829 : W := mkw 0x200002402551b188 0x1000012012a8d8c4 0x200000000301f181 0x100000000180f8c0

def z830 : W := mkw 0xba7d5e8f485b241a 0x5d3eaf47a42d920d 0x887c1e0f007e001e 0xc43e0f07803f000f

def z831 : W := mkw 0x11eb920002f56800 0x88f5c900017ab400 0x7df3fe0003f9fe00 0x3ef9ff0001fcff00

def z832 : W := mkw 0x285802ca257db19c 0x142c016512bed8ce 0xa87c000f037ff19f 0xd43e000781bff8cf

def z833 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x7ffffe3f03fffe00 0x3fffff1f81ffff00

def z834 : W := mkw 0x00046a10a04386a0 0x000235085021c350 0xee8cfe3fe0c78fff 0xf7467f1ff063c7ff

def z835 : W := mkw 0x11efda0000536c00 0x88f7ed000029b600 0x7dfffe000379fe00 0x3effff0001bcff00

def z836 : W := mkw 0x45caa170b7a4dbe0 0x22e550b85bd26df0 0x778fe1f0ff87ffe1 0x3bc7f0f87fc3fff0

def z837 : W := mkw 0xce1025fffd0893f4 0x670812fffe8449fa 0x820001fffc0001ff 0xc10000fffe0000ff

def z838 : W := mkw 0x9ffffdbfdaac0054 0x4ffffedfed56002a 0xdffffffffcfe007e 0xeffffffffe7f003f

def z839 : W := mkw 0x15effd35d0000000 0x0af7fe9ae8000000 0x5ffffffffc000000 0x2ffffffffe000000

def z840 : W := mkw 0x9fb7fdbfd8000000 0x4fdbfedfec000000 0x5783fffffc000000 0x2bc1fffffe000000

def z841 : W := mkw 0xda7d5ccf6f80dbe0 0x6d3eae67b7c06df0 0x287c1e0f0381ffe1 0x143e0f0781c0fff0

def z842 : W := mkw 0x8e146dbfd8000000 0x470a36dfec000000 0x0600fffffc000000 0x03007ffffe000000

def z843 : W := mkw 0x9ffffdbfd82c0014 0x4ffffedfec16000a 0xfffffffffcfe01ff 0xfffffffffe7f00ff

def z844 : W := mkw 0x4000024027d1fbe0 0x2000012013e8fdf0 0x2000000003f9ffe1 0x1000000001fcfff0

def z845 : W := mkw 0x000002402551b180 0x0000012012a8d8c0 0x200000000379f181 0x1000000001bcf8c0

def z846 : W := mkw 0x02357c9dc8000000 0x011abe4ee4000000 0x5f73ffccfc000000 0x2fb9ffe67e000000

def z847 : W := mkw 0x9ffffdbfdaa40044 0x4ffffedfed520022 0xfffffffffcc601ff 0xfffffffffe6300ff

def z848 : W := mkw 0x02355c8d48000000 0x011aae46a4000000 0x5f7f1fcffc000000 0x2fbf8fe7fe000000

def z849 : W := mkw 0x09d801ea01080110 0x04ec00f500840088 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z850 : W := mkw 0x10257e15e053a6aa 0x8812bf0af029d355 0x0400fe00e0018e00 0x02007f007000c700

def z851 : W := mkw 0x127d5c8c48000000 0x093eae4624000000 0x5f7f1fccfc000000 0x2fbf8fe67e000000

def z852 : W := mkw 0x4000024027f7ffea 0xa000012013fbfff5 0xa000000003ffffff 0xd000000001ffffff

def z853 : W := mkw 0x15a7f93090000000 0x0ad3fc9848000000 0x5783fff0fc000000 0x2bc1fff87e000000

def z854 : W := mkw 0x00255a0002f76c00 0x8012ad00017bb600 0x7dfffe0003fffe00 0x3effff0001ffff00

def z855 : W := mkw 0x4402a050b780dbe0 0x220150285bc06df0 0x7703e1c0ff81ffe1 0x3b81f0e07fc0fff0

def z856 : W := mkw 0x11efda0102f76c02 0x88f7ed00817bb601 0xfdfffe0303fffe06 0x7effff0181ffff03

def z857 : W := mkw 0x02146c9dc8000000 0x010a364ee4000000 0x4e8cfffffc000000 0x27467ffffe000000

def z858 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0xffff01fffffe01ff 0xffff80ffffff00ff

def z859 : W := mkw 0x9ffffdbfd8240004 0x4ffffedfec120002 0xdffffffffc060006 0x6ffffffffe030003

def z860 : W := mkw 0x9ffffdbfd8024c00 0xcffffedfec012600 0x5ffffffffc000e00 0x2ffffffffe000700

def z861 : W := mkw 0x4582a170b7a4dbe4 0x22c150b85bd26df2 0xf783e1f0ff87ffe7 0x7bc1f0f87fc3fff3

def z862 : W := mkw 0x9ffb91ea1bbc6954 0xcffdc8f50dde34aa 0x117301c01f387000 0x08b980e00f9c3800

def z863 : W := mkw 0x97a7fd35d8000000 0x4bd3fe9aec000000 0x5f8ffffffc000000 0x2fc7fffffe000000

def z864 : W := mkw 0x200002402559b3ba 0x1000012012acd9dd 0xa00000000379f1ff 0xd000000001bcf8ff

def z865 : W := mkw 0x17fffdbcd8000000 0x0bfffede6c000000 0x5ffffffcfc000000 0x2ffffffe7e000000

def z866 : W := mkw 0x09da81ea03ac4954 0x04ed40f501d624aa 0xfbfce1ff03fe0fff 0xfdfe70ff81ff07ff

def z867 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x7703e1c0ff01ff81 0x3b81f0e07f80ffc0

def z868 : W := mkw 0x45caa170b7a4dbe0 0x22e550b85bd26df0 0xffffe1ffffffffff 0xfffff0ffffffffff

def z869 : W := mkw 0x5427fe15f453feaa 0xaa13ff0afa29ff55 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z870 : W := mkw 0x4000024027c1dbe8 0x2000012013e0edf4 0x2000000003c1fff9 0x9000000001e0fffc

def z871 : W := mkw 0x0dda81ea13ac0154 0x06ed40f509d600aa 0xfbff01ff1ffe01ff 0xfdff80ff8fff00ff

def z872 : W := mkw 0x221024dced0893b8 0x1108126e768449dc 0x020001fcfc0001f9 0x810000fe7e0000fc

def z873 : W := mkw 0x9dcee93392a44800 0xcee77499c9522400 0x008ce03300000000 0x0046701980000000

def z874 : W := mkw 0x9ffb93aa384386aa 0x4ffdc9d51c21c355 0xb17301c01cc78fff 0xd8b980e00e63c7ff

def z875 : W := mkw 0x99efda0302f76c00 0xccf7ed01817bb600 0x7dfffe0303fffe00 0x3effff0181ffff00

def z876 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x1b7f1ffffc000000 0x0dbf8ffffe000000

def z877 : W := mkw 0xdffffdbfdaa44a64 0x6ffffedfed522532 0xdffffffffc860e66 0x6ffffffffe430733

def z878 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0xa88cfe3f00c78fff 0xd4467f1f8063c7ff

def z879 : W := mkw 0x200002402559b198 0x1000012012acd8cc 0x0000000000780199 0x80000000003c00cc

def z880 : W := mkw 0x8fdc6dbfd8000000 0x47ee36dfec000000 0x5ffcfffffc000000 0x2ffe7ffffe000000

def z881 : W := mkw 0x01a3920002f76c00 0x80d1c900017bb600 0x7df3fe0003fffe00 0x3ef9ff0001ffff00

def z882 : W := mkw 0x00046a1180430622 0x00023508c0218311 0xee8cfe3f00c78fff 0xf7467f1f8063c7ff

def z883 : W := mkw 0x9ffffdbfd8260400 0xcffffedfec130200 0x5ffffffffc060000 0x2ffffffffe030000

def z884 : W := mkw 0x92355c8d48000000 0x491aae46a4000000 0x5f731fccfc000000 0x2fb98fe67e000000

def z885 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x1d7fffcffc000000 0x0ebfffe7fe000000

def z886 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x15fffe0003bffe00 0x0affff0001dfff00

def z887 : W := mkw 0x01802170a78093e0 0x00c010b853c049f0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z888 : W := mkw 0x9637fc9dd8000000 0x4b1bfe4eec000000 0x5ffffffffc000000 0x2ffffffffe000000

def z889 : W := mkw 0x9ffbb5bfd8000000 0x4ffddadfec000000 0x5f731ffffc000000 0x2fb98ffffe000000

def z890 : W := mkw 0x0bf915ae4aa40044 0x05fc8ad725520022 0xdfff1ffffc860066 0x6fff8ffffe430033

def z891 : W := mkw 0x09d801ea012c0154 0x04ec00f5009600aa 0xdbfc01ff007e01ff 0xedfe00ff803f00ff

def z892 : W := mkw 0x00046c15c0000000 0x0002360ae0000000 0x5f8ffffffc000000 0x2fc7fffffe000000

def z893 : W := mkw 0x31ceca4027fffd98 0x98e7652013fffecc 0x208ce00003ffff99 0x9046700001ffffcc

def z894 : W := mkw 0x0182800002804800 0x00c1400001402400 0x7783e1c0ff81fe00 0x3bc1f0e07fc0ff00

def z895 : W := mkw 0x4dcaa172b7acdbf4 0x26e550b95bd66dfa 0xf78fe1f3ffffffff 0xfbc7f0f9ffffffff

def z896 : W := mkw 0x11efda0002f76c0a 0x88f7ed00017bb605 0xfdfffe0003fffe1e 0xfeffff0001ffff0f

def z897 : W := mkw 0x9e7ffdbfd8000000 0x4f3ffedfec000000 0x0e7ffffffc000000 0x073ffffffe000000

def z898 : W := mkw 0x0231148c48000000 0x01188a4624000000 0x15731fc0fc000000 0x0ab98fe07e000000

def z899 : W := mkw 0x200002402559b198 0x1000012012acd8cc 0xea8c003f03fff1ff 0xf546001f81fff8ff

def z900 : W := mkw 0x458281603780d9c0 0x22c140b01bc06ce0 0x7783e1c0ff81ff81 0x3bc1f0e07fc0ffc0

def z901 : W := mkw 0x1dfff9ba90000000 0x0efffcdd48000000 0x5ffffffffc000000 0x2ffffffffe000000

def z902 : W := mkw 0x223116cc6d59b1dc 0x11188b6636acd8ee 0xff731fccff79f1ff 0xffb98fe67fbcf8ff

def z903 : W := mkw 0x4582a170b788dbf0 0x22c150b85bc46df8 0x7783e1f0fff9fff9 0xbbc1f0f87ffcfffc

def z904 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0xff731fccfffff1ff 0xffb98fe67ffff8ff

def z905 : W := mkw 0x222116446d51b188 0x11108b2236a8d8c4 0x7f731fc0ff79f181 0x3fb98fe07fbcf8c0

def z906 : W := mkw 0x11efda0002d16800 0x08f7ed000168b400 0x7dfffe0003f9fe00 0x3effff0001fcff00

def z907 : W := mkw 0x001000c803ac0154 0x0008006401d600aa 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z908 : W := mkw 0x2182824027d9f998 0x10c1412013ecfccc 0x7583e00003f9ff99 0xbac1f00001fcffcc

def z909 : W := mkw 0x9ffffdbfd8240000 0x4ffffedfec120000 0x5ffffffffc7e0000 0x2ffffffffe3f0000

def z910 : W := mkw 0x4582a130b400daa0 0x22c150985a006d50 0x7783e1f0fc81ffe1 0x3bc1f0f87e40fff0

def z911 : W := mkw 0x9a79148e48000000 0x4d3c8a4724000000 0x5f731fccfc000000 0x2fb98fe67e000000

def z912 : W := mkw 0x00002614e04182a8 0x0000130a7020c154 0xee8cfe3fe0c78fff 0xf7467f1ff063c7ff

def z913 : W := mkw 0x201002c82559b198 0x1008016412acd8cc 0x2870000c0379f199 0x9438000601bcf8cc

def z914 : W := mkw 0x4582a170b7acdbf4 0x22c150b85bd66dfa 0xff8fe1ffffffffff 0xffc7f0ffffffffff

def z915 : W := mkw 0x4dcaa172b780dbe0 0x26e550b95bc06df0 0x778fe1f3ff81ffe1 0x3bc7f0f9ffc0fff0

def z916 : W := mkw 0x45caa170b7acdbf4 0x22e550b85bd66dfa 0xffffe1f0ffffffff 0xfffff0f87fffffff

def z917 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x7d731fc0ff79f000 0x3eb98fe07fbcf800

def z918 : W := mkw 0x9bffdc8f48000000 0x4dffee47a4000000 0x5fffffcffc000000 0x2fffffe7fe000000

def z919 : W := mkw 0x9ffff9ba98000000 0x4ffffcdd4c000000 0x5ffffff0fc000000 0x2ffffff87e000000

def z920 : W := mkw 0x11a7da0002d36c00 0x88d3ed000169b600 0x7df3fe0003f9fe00 0x3ef9ff0001fcff00

def z921 : W := mkw 0x09d801aa02ac0054 0x04ec00d50156002a 0xeafc003f00fe01ff 0xf57e001f807f00ff

def z922 : W := mkw 0x13ffdc8c4aa64c00 0x89ffee4625532600 0x5fffffccfc860e00 0x2fffffe67e430700

def z923 : W := mkw 0x02355c8c48000000 0x011aae4624000000 0x5fffffccfc000000 0x2fffffe67e000000

def z924 : W := mkw 0x081001ea01080154 0x040800f5008400aa 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z925 : W := mkw 0x97fffc9dd8000000 0x4bfffe4eec000000 0x5fffffccfc000000 0x2fffffe67e000000

def z926 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x7f8fe1ffff81ffe1 0x3fc7f0ffffc0fff0

def z927 : W := mkw 0x0858008a002c0014 0x042c00450016000a 0x8a7c003f007e01ff 0xc53e001f803f00ff

def z928 : W := mkw 0x4586ed35d2824e62 0x22c3769ae9412731 0xdf8ffffffc860e66 0x6fc7fffffe430733

def z929 : W := mkw 0x106d5a0002f76c00 0x8836ad00017bb600 0x6cfcfe0003fffe00 0x367e7f0001ffff00

def z930 : W := mkw 0x45caa170b780dbe0 0x22e550b85bc06df0 0x7fffe1f0ff81ffe1 0x3ffff0f87fc0fff0

def z931 : W := mkw 0x8e3135bfd8000000 0x47189adfec000000 0x0a701ffffc000000 0x05380ffffe000000

def z932 : W := mkw 0x0ddeedbfd0000000 0x06ef76dfe8000000 0x5ffffffffc000000 0x2ffffffffe000000

def z933 : W := mkw 0x4dd801ea17ac1154 0x26ec00f50bd608aa 0xfbfc01ff1ffe01ff 0xfdfe00ff8fff00ff

def z934 : W := mkw 0x106fda0000776c00 0x8837ed00003bb600 0x7d7ffe00037ffe00 0x3ebfff0001bfff00

def z935 : W := mkw 0x4d82a172b780dbe4 0x26c150b95bc06df2 0xf783e1f3ff81ffe7 0x7bc1f0f9ffc0fff3

def z936 : W := mkw 0x9ffffdbfdaa44800 0x4ffffedfed522400 0x7ffffffffffffe00 0x3fffffffffffff00

def z937 : W := mkw 0x0182a050a780dba0 0x00c1502853c06dd0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z938 : W := mkw 0x03f9148c48000000 0x01fc8a4624000000 0x5fff1fccfc000000 0x2fff8fe67e000000

def z939 : W := mkw 0x202112402559b198 0x1010892012acd8cc 0x7f731fc0ff79f199 0xbfb98fe07fbcf8cc

def z940 : W := mkw 0x9ffffdbfdaa60666 0x4ffffedfed530333 0xdffffffffc860e66 0x6ffffffffe430733

def z941 : W := mkw 0x20000240255bb598 0x1000012012addacc 0x2000000003ffff99 0x9000000001ffffcc

def z942 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0xfdfffe0003ffffff 0xfeffff0001ffffff

def z943 : W := mkw 0x6e1025fefd0893fc 0x370812ff7e8449fe 0x820001fffc0001ff 0xc10000fffe0000ff

def z944 : W := mkw 0x2bd801ea0fac1154 0x15ec00f507d608aa 0xfbfc01ff1ffe01ff 0xfdfe00ff8fff00ff

def z945 : W := mkw 0x221024dded0893ba 0x1108126ef68449dd 0x020001ccfc000199 0x810000e67e0000cc

def z946 : W := mkw 0x9ffffdbfd8000222 0x4ffffedfec000111 0xdffffffffc000066 0x6ffffffffe000033

def z947 : W := mkw 0x00046e15e44396aa 0x0002370af221cb55 0xee8ffe3ffcc7ffff 0xf747ff1ffe63ffff

def z948 : W := mkw 0x9ffffdbfd8020400 0x4ffffedfec010200 0x5ffffffffc860e00 0x2ffffffffe430700

def z949 : W := mkw 0x00044a00204386aa 0x000225001021c355 0xee8cfe3f00c78fff 0xf7467f1f8063c7ff

def z950 : W := mkw 0x0048000000240000 0x0024000000120000 0xeafc003f00fe01ff 0xf57e001f807f00ff

def z951 : W := mkw 0x223116cc6d5bb7ba 0x11188b6636addbdd 0x7f731fccff79ff99 0xbfb98fe67fbcffcc

def z952 : W := mkw 0x01c8016003a40140 0x00e400b001d200a0 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z953 : W := mkw 0x1027da0000536c00 0x8813ed000029b600 0x1573fe000339fe00 0x0ab9ff00019cff00

def z954 : W := mkw 0x19efda0202f76c04 0x8cf7ed01017bb602 0xfdfffe0303fffe06 0x7effff0181ffff03

def z955 : W := mkw 0x546d7b70b577b7e0 0xaa36bdb85abbdbf0 0x0a7c1ff0fc7e01e1 0x053e0ff87e3f00f0

def z956 : W := mkw 0x55eff93092a64e60 0xaaf7fc9849532730 0x5ffffff0fc860e60 0x2ffffff87e430730

def z957 : W := mkw 0x0000024025419188 0x0000012012a0c8c4 0x200000000341f199 0x9000000001a0f8cc

def z958 : W := mkw 0x223116cc6d5bb59a 0x11188b6636addacd 0xff731fccff7ff19f 0xffb98fe67fbff8cf

def z959 : W := mkw 0x223114cc6d18b190 0x11188a66368c58c8 0x7f731fccff39f181 0x3fb98fe67f9cf8c0

def z960 : W := mkw 0x223114cc4d183110 0x11188a66268c1888 0x15731fc0ff387000 0x0ab98fe07f9c3800

def z961 : W := mkw 0x15cee93092a64c00 0x8ae7749849532600 0x008ce03000860e00 0x0046701800430700

def z962 : W := mkw 0x200002402559b198 0x1000012012acd8cc 0x000000000339f000 0x00000000019cf800

def z963 : W := mkw 0x19da81ea03ac4954 0x8ced40f501d624aa 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z964 : W := mkw 0x9a7d5e8f487f2414 0xcd3eaf47a43f920a 0x887c1e0f007e001e 0xc43e0f07803f000f

def z965 : W := mkw 0x1027da0000536c00 0x8813ed000029b600 0x7dfffe0003fffe00 0x3effff0001ffff00

def z966 : W := mkw 0x4582a171b780dbe2 0x22c150b8dbc06df1 0xf783e1f3ff81ffe7 0x7bc1f0f9ffc0fff3

def z967 : W := mkw 0x22046e15ec4396aa 0x1102370af621cb55 0xee8cfe3ffcc78fff 0xf7467f1ffe63c7ff

def z968 : W := mkw 0x0231349dc8000000 0x01189a4ee4000000 0x5f731ffffc000000 0x2fb98ffffe000000

def z969 : W := mkw 0x11efd80002a44800 0x08f7ec0001522400 0x7dfffe0003fffe00 0x3effff0001ffff00

def z970 : W := mkw 0x9e7d7dbfd8000000 0x4f3ebedfec000000 0x5f7f1ffffc000000 0x2fbf8ffffe000000

def z971 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x7fffffc0fffffe00 0x3fffffe07fffff00

def z972 : W := mkw 0x20000240257db19c 0x1000012012bed8ce 0xa0000000037ff19f 0xd000000001bff8cf

def z973 : W := mkw 0x4dda81ea13ac4954 0x26ed40f509d624aa 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z974 : W := mkw 0x20046e15e453b6aa 0x1002370af229db55 0xee8cfe3fe0c7ffff 0xf7467f1ff063ffff

def z975 : W := mkw 0x0a79148e48000000 0x053c8a4724000000 0x5f7f1fcffc000000 0x2fbf8fe7fe000000

def z976 : W := mkw 0x0231148c48000000 0x01188a4624000000 0x0a701fccfc000000 0x05380fe67e000000

def z977 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x5f73ffccfc000000 0x2fb9ffe67e000000

def z978 : W := mkw 0x8e3135bfd8000000 0x47189adfec000000 0x06031ffffc000000 0x03018ffffe000000

def z979 : W := mkw 0x09d8008a02ac0014 0x04ec00450156000a 0xfbfc003f03fe01ff 0xfdfe001f81ff00ff

def z980 : W := mkw 0x661025fdfd0893fa 0x330812fefe8449fd 0x820001fffc0001ff 0xc10000fffe0000ff

def z981 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x1583e1f0ff81fe60 0x0ac1f0f87fc0ff30

def z982 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x1d731fccff79f018 0x8eb98fe67fbcf80c

def z983 : W := mkw 0x4582a130b400daa0 0x22c150985a006d50 0x1503e1c0fc01fe00 0x0a81f0e07e00ff00

def z984 : W := mkw 0x9a7d5e8f48532400 0xcd3eaf47a4299200 0x087c1e0f00000000 0x043e0f0780000000

def z985 : W := mkw 0x2000024027fdb198 0x1000012013fed8cc 0x2000000003fff199 0x9000000001fff8cc

def z986 : W := mkw 0x0ffbb5bed8000000 0x07fddadf6c000000 0x5ffffffffc000000 0x2ffffffffe000000

def z987 : W := mkw 0x22257e15e853a6aa 0x1112bf0af429d355 0x0400fe00e0018e00 0x02007f007000c700

def z988 : W := mkw 0x0582a170b50093a0 0x02c150b85a8049d0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z989 : W := mkw 0x6000024027fdfbfc 0x3000012013fefdfe 0xa000000003ffffff 0xd000000001ffffff

def z990 : W := mkw 0x003112c82559b190 0x0018896412acd8c8 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z991 : W := mkw 0x9fffddae58000000 0x4fffeed72c000000 0x5fffffccfc000000 0x2fffffe67e000000

def z992 : W := mkw 0x223116cc6d5bb7ba 0x11188b6636addbdd 0xffff1fffffffffff 0xffff8fffffffffff

def z993 : W := mkw 0x51efd8402780dbe0 0x28f7ec2013c06df0 0x7dfffe000381ffe1 0x3effff0001c0fff0

def z994 : W := mkw 0x0000024027f7fd80 0x8000012013fbfec0 0x2000000003ffff81 0x1000000001ffffc0

def z995 : W := mkw 0x4582a170b780dbea 0x22c150b85bc06df5 0xf783e1f0ff81ffff 0xfbc1f0f87fc0ffff

def z996 : W := mkw 0x55efdb2012f76c40 0xaaf7ed90097bb620 0x7dfffe0003fffe00 0x3effff0001ffff00

def z997 : W := mkw 0xbffffdbfd8182010 0x5ffffedfec0c1008 0x5ffffffffc380000 0x2ffffffffe1c0000

def z998 : W := mkw 0x31eb924027fdf998 0x98f5c92013fefccc 0x317300000379f199 0x98b9800001bcf8cc

def z999 : W := mkw 0x9633948c58000000 0x4b19ca462c000000 0x5f731fccfc000000 0x2fb98fe67e000000

def z1000 : W := mkw 0x01ceca0002e74c00 0x00e765000173a600 0x7dfffe0003fffe00 0x3effff0001ffff00

def z1001 : W := mkw 0x45caa170b7a4dbe0 0x22e550b85bd26df0 0x77f3e1f0ffb9ffe1 0x3bf9f0f87fdcfff0

def z1002 : W := mkw 0x223112c82d59b190 0x1118896416acd8c8 0x7f731fc0ff79f181 0x3fb98fe07fbcf8c0

def z1003 : W := mkw 0x00046c15e00286aa 0x0002360af0014355 0xce8cfe3fe0860fff 0xe7467f1ff04307ff

def z1004 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0xfffcfe3fe3ff8fff 0xfffe7f1ff1ffc7ff

def z1005 : W := mkw 0x13fffc9dc8000000 0x09fffe4ee4000000 0x5ffffffffc000000 0x2ffffffffe000000

def z1006 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x7d73fe000379fe00 0x3eb9ff0001bcff00

def z1007 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x0683e1f0fc81ffe1 0x0341f0f87e40fff0

def z1008 : W := mkw 0x8e146dbfd8000000 0x470a36dfec000000 0x0a0c1ffffc000000 0x05060ffffe000000

def z1009 : W := mkw 0x1027da0002f76c00 0x8813ed00017bb600 0x7d73fe0003fffe00 0x3eb9ff0001ffff00

def z1010 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x1b731fccff787199 0x8db98fe67fbc38cc

def z1011 : W := mkw 0x11efda0000532400 0x08f7ed0000299200 0x7dfffe0003fffe00 0x3effff0001ffff00

def z1012 : W := mkw 0x2a1025ffed0893fe 0x150812fff68449ff 0x820001fffc0001ff 0xc10000fffe0000ff

def z1013 : W := mkw 0x9feffd37d8000000 0x4ff7fe9bec000000 0x578ffff3fc000000 0x2bc7fff9fe000000

def z1014 : W := mkw 0x4000024027efdffe 0x2000012013f7efff 0xa000000003ffffff 0xd000000001ffffff

def z1015 : W := mkw 0x4402a170b500dbe0 0x220150b85a806df0 0x6683e1f0fc81ffe1 0x3341f0f87e40fff0

def z1016 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x8afc01ff00fe01ff 0xc57e00ff807f00ff

def z1017 : W := mkw 0x0010008800080010 0x0008004400040008 0xeafc003f00fe01ff 0xf57e001f807f00ff

def z1018 : W := mkw 0x11efda0002f76c44 0x88f7ed00017bb622 0xfdfffe0003fffe66 0x7effff0001ffff33

def z1019 : W := mkw 0x20000240257fb598 0x9000012012bfdacc 0x20000000037ff199 0x9000000001bff8cc

def z1020 : W := mkw 0x8e1025bfd8000000 0x470812dfec000000 0x4e001ffffc000000 0x27000ffffe000000

def z1021 : W := mkw 0x09d801aa002c0014 0x04ec00d50016000a 0xfbfc01ff00fe01ff 0xfdfe00ff807f00ff

def z1022 : W := mkw 0x9e37fdbfd8000000 0x4f1bfedfec000000 0x4e8ffffffc000000 0x2747fffffe000000

def z1023 : W := mkw 0x11efd80002b46800 0x88f7ec00015a3400 0x7dfffe0003b9fe00 0x3effff0001dcff00

def z1024 : W := mkw 0x11efd80000000000 0x08f7ec0000000000 0x5fffffc0fc000000 0x2fffffe07e000000

def z1025 : W := mkw 0xbffffdbfd8080018 0x5ffffedfec04000c 0x5ffffffffc000018 0xaffffffffe00000c

def z1026 : W := mkw 0x5dfb91ea17bc7954 0xaefdc8f50bde3caa 0x117301c01f387000 0x08b980e00f9c3800

def z1027 : W := mkw 0xdffffdbfdaa64e60 0xeffffedfed532730 0x5ffffffffc860e60 0x2ffffffffe430730

def z1028 : W := mkw 0x4000024027c3dfea 0x2000012013e1eff5 0x200000000381ffe1 0x1000000001c0fff0

def z1029 : W := mkw 0x21c8024027fdb198 0x10e4012013fed8cc 0x79fc000003fff199 0xbcfe000001fff8cc

def z1030 : W := mkw 0x9ffffdbfd8106800 0xcffffedfec083400 0x5ffffffffc007000 0x2ffffffffe003800

def z1031 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0xff8ffe3fe3c7ffff 0xffc7ff1ff1e3ffff

def z1032 : W := mkw 0x4582a170b7acdbf4 0x22c150b85bd66dfa 0x7783e1f0ffb9ffe1 0x3bc1f0f87fdcfff0

def z1033 : W := mkw 0x4582a170b7a4dbe0 0x22c150b85bd26df0 0x7783e1f0ffffffe1 0x3bc1f0f87ffffff0

def z1034 : W := mkw 0x106fda0002f76c00 0x8837ed00017bb600 0x2c7ffe0003fffe00 0x163fff0001ffff00

def z1035 : W := mkw 0xba7d5e8f487f2418 0xdd3eaf47a43f920c 0x087c1e0f007e0018 0x843e0f07803f000c

def z1036 : W := mkw 0x40002050a780dbe0 0x2000102853c06df0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z1037 : W := mkw 0x4dcaa172b7a4dbe4 0x26e550b95bd26df2 0xff8fe1ffffc7ffff 0xffc7f0ffffe3ffff

def z1038 : W := mkw 0x86046e15f84386aa 0x4302370afc21c355 0xee8cfe3ffcc78fff 0xf7467f1ffe63c7ff

def z1039 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x7fff1fffff79f199 0xbfff8fffffbcf8cc

def z1040 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x7f83e1fcffc1fff9 0xbfc1f0fe7fe0fffc

def z1041 : W := mkw 0x9ffffdbfdaa64c00 0xcffffedfed532600 0x7fffffffff87fe00 0x3fffffffffc3ff00

def z1042 : W := mkw 0xdffffdbfd8000260 0x6ffffedfec000130 0x5ffffffffc000060 0x2ffffffffe000030

def z1043 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0xf783e1ffff81ffff 0xfbc1f0ffffc0ffff

def z1044 : W := mkw 0x4dda81ea17ac5954 0x26ed40f50bd62caa 0xffffe1ff1fffffff 0xfffff0ff8fffffff

def z1045 : W := mkw 0x200002402559b3b8 0x1000012012acd9dc 0x2000000003f9fff9 0x9000000001fcfffc

def z1046 : W := mkw 0x0231148c48000000 0x01188a4624000000 0x7f731fccff01f000 0x3fb98fe67f80f800

def z1047 : W := mkw 0xaa3116cf6d59b198 0x55188b67b6acd8cc 0x7f731fcfff79f199 0xbfb98fe7ffbcf8cc

def z1048 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x7583e1c0ff81fe00 0x3ac1f0e07fc0ff00

def z1049 : W := mkw 0x0582a170b780d980 0x02c150b85bc06cc0 0x7783e1f0ff81ff81 0x3bc1f0f87fc0ffc0

def z1050 : W := mkw 0x9dceed37d0000000 0x4ee7769be8000000 0x5f8ffffffc000000 0x2fc7fffffe000000

def z1051 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x3503e1c0ff81ffe1 0x1a81f0e07fc0fff0

def z1052 : W := mkw 0x13fb948c48000000 0x09fdca4624000000 0x5f731fccfc000000 0x2fb98fe67e000000

def z1053 : W := mkw 0x0bfd7dbfc8000000 0x05febedfe4000000 0x5ffffffffc000000 0x2ffffffffe000000

def z1054 : W := mkw 0x9ffffdbfd8342000 0xcffffedfec1a1000 0x5ffffffffc380000 0x2ffffffffe1c0000

def z1055 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x7fffffffff01f000 0x3fffffffff80f800

def z1056 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x7ff31ffcfff9f1f9 0xbff98ffe7ffcf8fc

def z1057 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0x9b7c01ff037e01ff 0xcdbe00ff81bf00ff

def z1058 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x7ffffffffc818e00 0x3ffffffffe40c700

def z1059 : W := mkw 0x2000024027ffb7fe 0x1000012013ffdbff 0xa000000003ffffff 0xd000000001ffffff

def z1060 : W := mkw 0xdffffdbfda804840 0x6ffffedfed402420 0x5ffffffffc000000 0x2ffffffffe000000

def z1061 : W := mkw 0x0231148c48000000 0x01188a4624000000 0x7f731fccff780000 0x3fb98fe67fbc0000

def z1062 : W := mkw 0x223116cc4d593118 0x11188b6626ac988c 0x5f731fccff787018 0xafb98fe67fbc380c

def z1063 : W := mkw 0x9ffffdbfd8080014 0x4ffffedfec04000a 0xdffffffffc00001e 0xeffffffffe00000f

def z1064 : W := mkw 0xae1025fffd0893ba 0x570812fffe8449dd 0x820001fffc0001ff 0xc10000fffe0000ff

def z1065 : W := mkw 0x223116cc6d59b3ba 0x11188b6636acd9dd 0xff731fccff79f1ff 0xffb98fe67fbcf8ff

def z1066 : W := mkw 0x9ffffdbfdaa64c00 0xcffffedfed532600 0x7ffffffffffe0e00 0x3fffffffffff0700

def z1067 : W := mkw 0x00044e0460438488 0x000227023021c244 0xee8cfe3fe0c78fff 0xf7467f1ff063c7ff

def z1068 : W := mkw 0x4000024027fffff4 0xa000012013fffffa 0xa000000003ffffff 0xd000000001ffffff

def z1069 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x1773fffffc000000 0x0bb9fffffe000000

def z1070 : W := mkw 0x4582a170b500dba0 0x22c150b85a806dd0 0x7783e1f0ff01ff81 0x3bc1f0f87f80ffc0

def z1071 : W := mkw 0x0a3115ae48000000 0x05188ad724000000 0x5f731ffffc000000 0x2fb98ffffe000000

def z1072 : W := mkw 0x03b3948c48000000 0x01d9ca4624000000 0x5ff3ffccfc000000 0x2ff9ffe67e000000

def z1073 : W := mkw 0x9ffffdbfda800000 0x4ffffedfed400000 0x7fffffffff800000 0x3fffffffffc00000

def z1074 : W := mkw 0x0586e93090000000 0x02c3749848000000 0x5f8ffff0fc000000 0x2fc7fff87e000000

def z1075 : W := mkw 0x9e37fdbfd8000000 0x4f1bfedfec000000 0x5f73fffffc000000 0x2fb9fffffe000000

def z1076 : W := mkw 0x4402a170b780dbe0 0x220150b85bc06df0 0x2603e1f0ff81ffe1 0x1301f0f87fc0fff0

def z1077 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0xdffffffffc0001ff 0xeffffffffe0000ff

def z1078 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x75f3fe0003b9fe00 0x3af9ff0001dcff00

def z1079 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x5dfffe000339fe00 0x2effff00019cff00

def z1080 : W := mkw 0x0bf915ae48000000 0x05fc8ad724000000 0x5f731fccfc000000 0x2fb98fe67e000000

def z1081 : W := mkw 0x9defdb2212f76c00 0xcef7ed91097bb600 0x7dfffe0003fffe00 0x3effff0001ffff00

def z1082 : W := mkw 0x9ffffdbfdaa64c44 0xcffffedfed532622 0xdffffffffc860e66 0x6ffffffffe430733

def z1083 : W := mkw 0x0582a17093804940 0x02c150b849c024a0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z1084 : W := mkw 0x127d5e8c48772400 0x893eaf46243b9200 0x087c1e0c007e0000 0x043e0f06003f0000

def z1085 : W := mkw 0x9fffddaf58000000 0x4fffeed7ac000000 0x5f7f1fcffc000000 0x2fbf8fe7fe000000

def z1086 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x7ffffe3003ffffe1 0x3fffff1801fffff0

def z1087 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x77731fc0ff39f181 0x3bb98fe07f9cf8c0

def z1088 : W := mkw 0x2a7d5e8f487f241e 0x153eaf47a43f920f 0x887c1e0f007e001e 0xc43e0f07803f000f

def z1089 : W := mkw 0x4000024027d3ffe0 0xa000012013e9fff0 0x200000000381ffe1 0x1000000001c0fff0

def z1090 : W := mkw 0x0a79148e482c0014 0x053c8a472416000a 0xdf7f1fcffc7e001e 0xefbf8fe7fe3f000f

def z1091 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0xffff01ff03fff1ff 0xffff80ff81fff8ff

def z1092 : W := mkw 0x0021120000512000 0x0010890000289000 0x7df3fe0003f9fe00 0x3ef9ff0001fcff00

def z1093 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0x7f8fe1f0ffc7ffe1 0x3fc7f0f87fe3fff0

def z1094 : W := mkw 0x22355e8d485b241a 0x111aaf46a42d920d 0x08701e0c00780018 0x84380f06003c000c

def z1095 : W := mkw 0x3a7d5e8e487f241c 0x9d3eaf47243f920e 0x887c1e0f007e001e 0xc43e0f07803f000f

def z1096 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0xf78fe1f3ff87ffe7 0x7bc7f0f9ffc3fff3

def z1097 : W := mkw 0x32355e8c485b2418 0x991aaf46242d920c 0x08701e0c00780018 0x84380f06003c000c

def z1098 : W := mkw 0x9ffffdbfd8000044 0x4ffffedfec000022 0xdffffffffc000066 0x6ffffffffe000033

def z1099 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x0afcfffffc000000 0x057e7ffffe000000

def z1100 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x5dffffc0fc000000 0x2effffe07e000000

def z1101 : W := mkw 0x223116cc4d593110 0x11188b6626ac9888 0x7f731fccff79f000 0x3fb98fe67fbcf800

def z1102 : W := mkw 0x4582a170b500dbe0 0x22c150b85a806df0 0x5783e1f0fc01ffe1 0x2bc1f0f87e00fff0

def z1103 : W := mkw 0x9ffffdbfdab66c00 0xcffffedfed5b3600 0x5fffffffffbe7e00 0x2fffffffffdf3f00

def z1104 : W := mkw 0x085800ca03ac0154 0x042c006501d600aa 0xeafc003f03fe01ff 0xf57e001f81ff00ff

def z1105 : W := mkw 0x9ffffdbfd8080010 0x4ffffedfec040008 0x5ffffffffc780018 0xaffffffffe3c000c

def z1106 : W := mkw 0x0023920000516800 0x0011c9000028b400 0x7d73fe000379fe00 0x3eb9ff0001bcff00

def z1107 : W := mkw 0x9627fc15d8000000 0x4b13fe0aec000000 0x5703ffc0fc000000 0x2b81ffe07e000000

def z1108 : W := mkw 0x2000024027fdb1dc 0x1000012013fed8ee 0x200000000379f199 0x9000000001bcf8cc

def z1109 : W := mkw 0x6582a170b788dbf8 0x32c150b85bc46dfc 0x7783e1f0ff81fff9 0xbbc1f0f87fc0fffc

def z1110 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0x28fcfe0003fffe00 0x147e7f0001ffff00

def z1111 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x7ffffffffc400199 0xbffffffffe2000cc

def z1112 : W := mkw 0x20000240255bb7ba 0x1000012012addbdd 0x200000000379ff99 0x9000000001bcffcc

def z1113 : W := mkw 0x19efdb2202f76c44 0x8cf7ed91017bb622 0x7dfffe0003fffe00 0x3effff0001ffff00

def z1114 : W := mkw 0x09c8012202a40044 0x04e4009101520022 0xfbfc003f03fe01ff 0xfdfe001f81ff00ff

def z1115 : W := mkw 0x023114cc6d089190 0x01188a66368448c8 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z1116 : W := mkw 0x223116cd6d59b19a 0x11188b66b6acd8cd 0xff731fcfff79f19f 0xffb98fe7ffbcf8cf

def z1117 : W := mkw 0x13fb948c4ab46800 0x89fdca46255a3400 0x5f731fccff387000 0x2fb98fe67f9c3800

def z1118 : W := mkw 0x9ffffdbfd8102000 0x4ffffedfec081000 0x5fffffffff387000 0x2fffffffff9c3800

def z1119 : W := mkw 0x07b395ac58000000 0x03d9cad62c000000 0x5f731fccfc000000 0x2fb98fe67e000000

def z1120 : W := mkw 0x00044e054043040a 0x00022702a0218205 0xee8cfe3f00c78fff 0xf7467f1f8063c7ff

def z1121 : W := mkw 0x9dcee93392a64c44 0xcee77499c9532622 0x808ce03300860e66 0x4046701980430733

def z1122 : W := mkw 0x0633b49cd8000000 0x0319da4e6c000000 0x5f73ffccfc000000 0x2fb9ffe67e000000

def z1123 : W := mkw 0x47b3b5bcda804a60 0x23d9dade6d402530 0x5ff3fffcfc800e60 0x2ff9fffe7e400730

def z1124 : W := mkw 0x04046d35d0000000 0x0202369ae8000000 0x4e8cfffffc000000 0x27467ffffe000000

def z1125 : W := mkw 0x20000240255bb59a 0x1000012012addacd 0xa0000000037ff19f 0xd000000001bff8cf

def z1126 : W := mkw 0x49d801ea07ac5954 0x24ec00f503d62caa 0xfbfc01ff03fe71ff 0xfdfe00ff81ff38ff

def z1127 : W := mkw 0x8fb3b5bfd8000000 0x47d9dadfec000000 0x5ff3fffffc000000 0x2ff9fffffe000000

def z1128 : W := mkw 0x221006cc6d59b198 0x1108036636acd8cc 0x2000000c0379f199 0x9000000601bcf8cc

def z1129 : W := mkw 0x327d5e8d487f241a 0x993eaf46a43f920d 0x887c1e0f007e001e 0xc43e0f07803f000f

def z1130 : W := mkw 0x6627fe15fc53feaa 0x3313ff0afe29ff55 0x0403fe00fc01fe00 0x0201ff007e00ff00

def z1131 : W := mkw 0x01a7da0002d36c00 0x00d3ed000169b600 0x7dfffe0003fffe00 0x3effff0001ffff00

def z1132 : W := mkw 0x1bffddae48000000 0x0dffeed724000000 0x5ffffffffc000000 0x2ffffffffe000000

def z1133 : W := mkw 0x00257e15e053a6aa 0x0012bf0af029d355 0x0403fe00e001fe00 0x0201ff007000ff00

def z1134 : W := mkw 0x0221140448000000 0x01108a0224000000 0x57031fc0fc000000 0x2b818fe07e000000

def z1135 : W := mkw 0x00046e15c0430400 0x0002370ae0218200 0xee8cfe3fe0c78fff 0xf7467f1ff063c7ff

def z1136 : W := mkw 0x11efdb2002f76c00 0x88f7ed90017bb600 0x7ffffff003fffe00 0x3ffffff801ffff00

def z1137 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x7fff1fccfffff199 0xbfff8fe67ffff8cc

def z1138 : W := mkw 0x9ffffdbfda800040 0x4ffffedfed400020 0x5ffffffffc800060 0x2ffffffffe400030

def z1139 : W := mkw 0x9e357dbfd8000000 0x4f1abedfec000000 0x02001ffffc000000 0x01000ffffe000000

def z1140 : W := mkw 0x11efda0002f76c00 0x88f7ed00017bb600 0xfdfffe3303fffe66 0x7effff1981ffff33

def z1141 : W := mkw 0x2000024027fffddc 0x9000012013fffeee 0xa000000003ffffff 0xd000000001ffffff

def z1142 : W := mkw 0xcd82a173b780dbe0 0x66c150b9dbc06df0 0x7783e1f3ff81ffe1 0x3bc1f0f9ffc0fff0

def z1143 : W := mkw 0x4402a130b400daa0 0x220150985a006d50 0x0603e1f0fc01fe00 0x0301f0f87e00ff00

def z1144 : W := mkw 0x4dcee93392a64e66 0x26e77499c9532733 0x808ce03300860e66 0x4046701980430733

def z1145 : W := mkw 0x6000024027fffff8 0xb000012013fffffc 0x2000000003fffff9 0x9000000001fffffc

def z1146 : W := mkw 0x3bfb91ea0fbc7954 0x9dfdc8f507de3caa 0x117301c01f387000 0x08b980e00f9c3800

def z1147 : W := mkw 0x00255a0000532400 0x0012ad0000299200 0x7d73fe000379fe00 0x3eb9ff0001bcff00

def z1148 : W := mkw 0x09d801ea03ac0154 0x04ec00f501d600aa 0xfffce1ff03ff8fff 0xfffe70ff81ffc7ff

def z1149 : W := mkw 0x5dcee93292a64e64 0xaee7749949532732 0x808ce03300860e66 0x4046701980430733

def z1150 : W := mkw 0x2a3116ce6d59b19c 0x15188b6736acd8ce 0xff731fcfff79f19f 0xffb98fe7ffbcf8cf

def z1151 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x7ffffffffc8001e1 0x3ffffffffe4000f0

def z1152 : W := mkw 0x223116cc6d5bb598 0x11188b6636addacc 0x7f731fccffffff99 0xbfb98fe67fffffcc

def z1153 : W := mkw 0x4582a17097805940 0x22c150b84bc02ca0 0x7783e1f0ff81fe00 0x3bc1f0f87fc0ff00

def z1154 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x068ffffffc000000 0x0347fffffe000000

def z1155 : W := mkw 0x55ceeb70b7f7ffe0 0xaae775b85bfbfff0 0x208ce03003ffffe1 0x1046701801fffff0

def z1156 : W := mkw 0x085801ea012c0154 0x042c00f5009600aa 0xeafc01ff00fe01ff 0xf57e00ff807f00ff

def z1157 : W := mkw 0x8ff935bfd8000000 0x47fc9adfec000000 0x5fff1ffffc000000 0x2fff8ffffe000000

def z1158 : W := mkw 0xdffffdbfd8004a20 0x6ffffedfec002510 0x5ffffffffc000e00 0x2ffffffffe000700

def z1159 : W := mkw 0x023116cc6d51b180 0x01188b6636a8d8c0 0x7f731fccff79f181 0x3fb98fe67fbcf8c0

def z1160 : W := mkw 0x97efda001af76c00 0xcbf7ed000d7bb600 0x7dfffe001ffffe00 0x3effff000fffff00

def z1161 : W := mkw 0x6582a370b7d9fbf8 0x32c151b85becfdfc 0x2080e03003f9fff9 0x9040701801fcfffc

def z1162 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0xdffffffffc46001e 0xeffffffffe23000f

def z1163 : W := mkw 0x01c8004003ac0154 0x00e4002001d600aa 0xfbfc003f03fe01ff 0xfdfe001f81ff00ff

def z1164 : W := mkw 0x0000040440000000 0x0000020220000000 0x5f031fccfc000000 0x2f818fe67e000000

def z1165 : W := mkw 0x019001e803880150 0x00c800f401c400a8 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z1166 : W := mkw 0x9bfd5daf48000000 0x4dfeaed7a4000000 0x5fff1ffffc000000 0x2fff8ffffe000000

def z1167 : W := mkw 0x600002402559b3f8 0x3000012012acd9fc 0x200000000379f1f9 0x9000000001bcf8fc

def z1168 : W := mkw 0x0582a33092f76c00 0x82c15198497bb600 0x7783e1f0fffffe00 0x3bc1f0f87fffff00

def z1169 : W := mkw 0x0231148c48000000 0x01188a4624000000 0x06031fccfc000000 0x03018fe67e000000

def z1170 : W := mkw 0x418280402780dbe0 0x20c1402013c06df0 0x7783e1c0ff81ffe1 0x3bc1f0e07fc0fff0

def z1171 : W := mkw 0x2000024027d9f998 0x1000012013ecfccc 0x2000000003f9ff99 0x9000000001fcffcc

def z1172 : W := mkw 0x4402a050b500dba0 0x220150285a806dd0 0x0603e1c0fc01ff81 0x0301f0e07e00ffc0

def z1173 : W := mkw 0x09d801ea03ac4954 0x04ec00f501d624aa 0xfbfc01ff03ffffff 0xfdfe00ff81ffffff

def z1174 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x17731fccff39f199 0x8bb98fe67f9cf8cc

def z1175 : W := mkw 0x6ffb91ea1fbc7954 0x37fdc8f50fde3caa 0x117301c01f387000 0x08b980e00f9c3800

def z1176 : W := mkw 0x223114cc4d183110 0x11188a66268c1888 0x7f731fccff787199 0xbfb98fe67fbc38cc

def z1177 : W := mkw 0xee1025fffd0893f8 0x770812fffe8449fc 0x020001fffc0001f9 0x810000fffe0000fc

def z1178 : W := mkw 0x03f9148c4aa40000 0x01fc8a4625520000 0x7fff1fccfffe0000 0x3fff8fe67fff0000

def z1179 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0xff731fffff79f1ff 0xffb98fffffbcf8ff

def z1180 : W := mkw 0x4dcaa172b7a4dbe4 0x26e550b95bd26df2 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z1181 : W := mkw 0x2000024025499198 0x1000012012a4c8cc 0x2000000000418199 0x900000000020c0cc

def z1182 : W := mkw 0x02357c9dc8020622 0x011abe4ee4010311 0xdffffffffc860e66 0x6ffffffffe430733

def z1183 : W := mkw 0x9ffffdbfdaa44800 0xcffffedfed522400 0x5ffffffffc000000 0x2ffffffffe000000

def z1184 : W := mkw 0x6000024027d9f9d8 0x3000012013ecfcec 0x200000000379f199 0x9000000001bcf8cc

def z1185 : W := mkw 0x0210048c48000000 0x0108024624000000 0x4e001fccfc000000 0x27000fe67e000000

def z1186 : W := mkw 0x9ffffdbfd8020402 0x4ffffedfec010201 0xdffffffffc060006 0x6ffffffffe030003

def z1187 : W := mkw 0x4586eb71b7c3dfea 0x22c375b8dbe1eff5 0xa08ce03303c7ffff 0xd046701981e3ffff

def z1188 : W := mkw 0x03b115ac48000000 0x01d88ad624000000 0x5ff31ffcfc000000 0x2ff98ffe7e000000

def z1189 : W := mkw 0x0231349cc8000000 0x01189a4e64000000 0x5ff3fffcfc000000 0x2ff9fffe7e000000

def z1190 : W := mkw 0x9ffd7dbfd8000000 0x4ffebedfec000000 0x5bfc1ffffc000000 0x2dfe0ffffe000000

def z1191 : W := mkw 0x4402a170b500dbe0 0x220150b85a806df0 0x7703e1f0ff01ffe1 0x3b81f0f87f80fff0

def z1192 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x868cfe3fe0878fff 0xc3467f1ff043c7ff

def z1193 : W := mkw 0x55cee93192a64e62 0xaae77498c9532731 0x808ce03300860e66 0x4046701980430733

def z1194 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0xdffffffffc860066 0x6ffffffffe430033

def z1195 : W := mkw 0x200002402559b1dc 0x1000012012acd8ee 0xa00000000379f1ff 0xd000000001bcf8ff

def z1196 : W := mkw 0x00046e15e04386aa 0x0002370af021c355 0x8a8cfe3fe0c60fff 0xc5467f1ff06307ff

def z1197 : W := mkw 0x4402a050b500dba0 0x220150285a806dd0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z1198 : W := mkw 0x2231148c48182010 0x11188a46240c1008 0x5f731fccfc380000 0x2fb98fe67e1c0000

def z1199 : W := mkw 0x15efdb2012f76c00 0x8af7ed90097bb600 0x7dffffc01ffffe00 0x3effffe00fffff00

def z1200 : W := mkw 0x9fdeedbfd8000000 0x4fef76dfec000000 0x4e8cfffffc000000 0x27467ffffe000000

def z1201 : W := mkw 0x0582a534d0000000 0x02c1529a68000000 0x5f83fffcfc000000 0x2fc1fffe7e000000

def z1202 : W := mkw 0xdffffdbfda824e62 0x6ffffedfed412731 0xdffffffffc860e66 0x6ffffffffe430733

def z1203 : W := mkw 0x20000240255bfd98 0x9000012012adfecc 0x200000000379ff99 0x9000000001bcffcc

def z1204 : W := mkw 0x085801ea012c0154 0x042c00f5009600aa 0xfb7c01ff037e01ff 0xfdbe00ff81bf00ff

def z1205 : W := mkw 0x9e7d7dbfd8000000 0x4f3ebedfec000000 0x4efcfffffc000000 0x277e7ffffe000000

def z1206 : W := mkw 0x023116cc49592110 0x01188b6624ac9088 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z1207 : W := mkw 0x2000024027d9b1d8 0x1000012013ecd8ec 0x2000000003f9f1f9 0x9000000001fcf8fc

def z1208 : W := mkw 0x623116cc6d59b3f8 0x31188b6636acd9fc 0x7f731fccff79f1f9 0xbfb98fe67fbcf8fc

def z1209 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x15fffff3fc000000 0x0afffff9fe000000

def z1210 : W := mkw 0x0231148c48000000 0x01188a4624000000 0x7f731fccfc400199 0xbfb98fe67e2000cc

def z1211 : W := mkw 0x00002050a50093a0 0x00001028528049d0 0x7703e1c0ff01ff81 0x3b81f0e07f80ffc0

def z1212 : W := mkw 0x00046e15c043062a 0x0002370ae0218315 0xea8cfe3f00c60fff 0xf5467f1f806307ff

def z1213 : W := mkw 0x223116cc6d59b198 0x11188b6636acd8cc 0x35731fc0ff79f199 0x9ab98fe07fbcf8cc

def z1214 : W := mkw 0x01cc4a0002f76c00 0x80e62500017bb600 0x7dfcfe0003fffe00 0x3efe7f0001ffff00

def z1215 : W := mkw 0xdffffdbfda804a60 0x6ffffedfed402530 0x7fffffffff81fe60 0x3fffffffffc0ff30

def z1216 : W := mkw 0x40000240254397ea 0x2000012012a1cbf5 0xa000000000c78fff 0xd00000000063c7ff

def z1217 : W := mkw 0x8f96edbfd8000000 0x47cb76dfec000000 0x5f8ffffffc000000 0x2fc7fffffe000000

def z1218 : W := mkw 0x2231168c48592018 0x11188b46242c900c 0x7f731fccff79f018 0xbfb98fe67fbcf80c

def z1219 : W := mkw 0x9a7d5c8f48000000 0x4d3eae47a4000000 0x0a7c1fcffc000000 0x053e0fe7fe000000

def z1220 : W := mkw 0x55caa170b7a4dbe0 0xaae550b85bd26df0 0x7783e1f0ff81ffe1 0x3bc1f0f87fc0fff0

def z1221 : W := mkw 0x8e357dbfd8000000 0x471abedfec000000 0x5ffffffffc000000 0x2ffffffffe000000

def z1222 : W := mkw 0x0231148c48080010 0x01188a4624040008 0x5f731fccfc780018 0xafb98fe67e3c000c

def z1223 : W := mkw 0x9ffffdbfd8020622 0x4ffffedfec010311 0x5ffffffffc000e00 0x2ffffffffe000700

def z1224 : W := mkw 0x0586ed35d0000000 0x02c3769ae8000000 0x5783fff0fc000000 0x2bc1fff87e000000

def z1225 : W := mkw 0x0231168c6851a088 0x01188b463428d044 0x7f731fccff79f199 0xbfb98fe67fbcf8cc

def z1226 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x7fffffffff780000 0x3fffffffffbc0000

def z1227 : W := mkw 0x4582a170b780dbe0 0x22c150b85bc06df0 0xf783e1f0ffc7ffff 0xfbc1f0f87fe3ffff

def z1228 : W := mkw 0x085800ca012c0114 0x042c00650096008a 0xfbfc01ff03fe01ff 0xfdfe00ff81ff00ff

def z1229 : W := mkw 0x9ffffdbfdab46800 0xcffffedfed5a3400 0x7fffffffffb9fe00 0x3fffffffffdcff00

def z1230 : W := mkw 0x4582a170b788dbf4 0x22c150b85bc46dfa 0xf783e1f0ff81ffff 0xfbc1f0f87fc0ffff

def z1231 : W := mkw 0x01eb920002f56800 0x00f5c900017ab400 0x7dfffe0003fffe00 0x3effff0001ffff00

def z1232 : W := mkw 0x03b3948c4a804800 0x01d9ca4625402400 0x7ff3ffccff81fe00 0x3ff9ffe67fc0ff00

def z1233 : W := mkw 0x22355e8c485b2418 0x111aaf46242d920c 0x087c1e0c007e0018 0x843e0f06003f000c

def z1234 : W := mkw 0x07a3b534d8000000 0x03d1da9a6c000000 0x5783fff0fc000000 0x2bc1fff87e000000

def z1235 : W := mkw 0x9deff93390000000 0x4ef7fc99c8000000 0x5ffffff3fc000000 0x2ffffff9fe000000

def z1236 : W := mkw 0x9ffffdbfd8000000 0x4ffffedfec000000 0x7ffffffffcc60000 0x3ffffffffe630000

def z1237 : W := mkw 0x9ffffdbfd8004800 0x4ffffedfec002400 0x5ffffffffc01fe00 0x2ffffffffe00ff00

def z1238 : W := mkw 0x29c8036227fdb1dc 0x14e401b113fed8ee 0xa08c003303fff1ff 0xd046001981fff8ff

def z1239 : W := mkw 0x063135bcd8000000 0x03189ade6c000000 0x5f731ffcfc000000 0x2fb98ffe7e000000

def z1240 : W := mkw 0x9ffffdbfd8000220 0x4ffffedfec000110 0x5ffffffffc800e60 0x2ffffffffe400730

def z1241 : W := mkw 0x4582a130b680daa0 0x22c150985b406d50 0x7783e1f0ff81fe00 0x3bc1f0f87fc0ff00

def z1242 : W := mkw 0x9e7ffc9fd8000000 0x4f3ffe4fec000000 0x5f7fffcffc000000 0x2fbfffe7fe000000

def z1243 : W := mkw 0x200002402559b198 0x1000012012acd8cc 0x6a00000c0379f199 0xb500000601bcf8cc

def z1244 : W := mkw 0xb627fe15fc53b6aa 0x5b13ff0afe29db55 0x0403fe00fc01fe00 0x0201ff007e00ff00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z10,z11,z6]),(0,[z0,z1,z2,z3,z4,z12,z6]),(0,[z0,z1,z13,z2,z14,z3,z4])],[(0,[z15,z0,z1,z16,z3,z4,z6]),(0,[z17,z0,z1,z2,z3,z4,z6]),(0,[z18,z0,z1,z2,z3,z4,z6]),(0,[z19,z0,z20,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z21,z6]),(0,[z0,z1,z2,z3,z4,z6,z22]),(0,[z0,z1,z2,z3,z4,z23,z6]),(0,[z0,z1,z2,z3,z4,z12,z24]),(0,[z0,z1,z2,z3,z4,z25,z6]),(0,[z0,z26,z1,z2,z3,z4,z6])],[(0,[z27,z0,z1,z2,z3,z4,z6]),(1,[z0,z9,z1,z2,z28,z4]),(0,[z0,z1,z29,z2,z3,z4,z6]),(0,[z0,z30,z1,z2,z3,z4,z6]),(0,[z31,z0,z1,z2,z3,z4,z6]),(0,[z32,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z33,z6])],[(0,[z0,z1,z34,z2,z3,z4,z6]),(0,[z35,z0,z1,z36,z2,z4,z6]),(0,[z0,z1,z2,z14,z3,z37,z4])],[(0,[z0,z38,z1,z2,z14,z3,z4]),(0,[z0,z1,z2,z39,z3,z4,z6]),(0,[z0,z1,z40,z2,z3,z4,z41]),(0,[z0,z1,z2,z42,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z4,z6]),(0,[z44,z0,z45,z1,z2,z3,z4]),(0,[z0,z9,z1,z46,z2,z3,z4]),(0,[z0,z1,z2,z47,z3,z4,z6]),(1,[z0,z1,z48,z3,z37,z6]),(0,[z0,z1,z2,z3,z49,z4,z6]),(0,[z0,z1,z2,z3,z24,z6,z50])],[(0,[z0,z1,z2,z3,z51,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z52]),(0,[z53,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z49,z4,z24])],[(0,[z0,z1,z2,z3,z54,z4,z6]),(0,[z0,z1,z2,z3,z4,z24,z55]),(0,[z0,z9,z1,z56,z2,z3,z4])]],
   [[(0,[z0,z1,z57,z2,z3,z4,z6]),(0,[z0,z58,z1,z2,z3,z4,z6]),(0,[z59,z1,z2,z60,z3,z4,z6]),(0,[z61,z0,z1,z2,z3,z4,z6]),(0,[z35,z0,z1,z2,z3,z62,z6]),(1,[z0,z9,z1,z2,z4,z63])],[(0,[z0,z1,z2,z3,z4,z6,z64]),(0,[z0,z65,z1,z2,z66,z4,z6]),(0,[z0,z1,z67,z2,z3,z66,z4]),(0,[z68,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z69])],[(0,[z70,z0,z1,z2,z71,z4,z6]),(0,[z0,z1,z2,z3,z4,z72,z6]),(0,[z44,z0,z1,z2,z14,z3,z4]),(0,[z0,z1,z73,z2,z3,z4,z6]),(0,[z74,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z75,z4,z6]),(0,[z76,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z62]),(0,[z77,z0,z1,z2,z3,z4,z6]),(0,[z0,z78,z1,z2,z79,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z80]),(0,[z81,z0,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z82,z4,z6])],[(0,[z83,z0,z1,z40,z3,z4,z6]),(0,[z84,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z85,z3,z4,z6]),(0,[z0,z86,z1,z87,z3,z4,z6]),(1,[z0,z88,z1,z2,z4,z6]),(0,[z0,z1,z48,z2,z89,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z90])],[(0,[z0,z1,z91,z2,z3,z4,z6]),(0,[z1,z2,z28,z3,z71,z4,z6]),(0,[z0,z1,z2,z92,z3,z4,z6]),(0,[z0,z1,z93,z2,z3,z4,z6]),(0,[z0,z65,z1,z2,z14,z3,z4]),(0,[z35,z0,z1,z2,z3,z10,z6]),(0,[z0,z78,z9,z1,z2,z4,z6]),(0,[z0,z1,z2,z94,z3,z4,z6])],[(0,[z95,z0,z1,z2,z3,z4,z96]),(0,[z0,z97,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z98,z3,z4,z6])],[(0,[z0,z99,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z100,z4,z6]),(0,[z0,z20,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z22]),(1,[z0,z20,z2,z3,z10,z6]),(0,[z0,z1,z2,z101,z3,z4,z6]),(0,[z0,z1,z2,z3,z102,z4,z6]),(0,[z0,z1,z2,z3,z4,z103,z6])],[(0,[z15,z0,z1,z2,z14,z3,z4]),(0,[z0,z1,z2,z3,z4,z104,z6]),(0,[z0,z1,z105,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z106,z4,z6]),(0,[z0,z65,z2,z3,z66,z4,z6]),(0,[z0,z107,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z108])]],
   [[(0,[z8,z0,z1,z2,z3,z4,z6]),(0,[z0,z86,z1,z2,z3,z109,z6]),(0,[z0,z1,z2,z3,z4,z6,z110]),(0,[z0,z111,z1,z2,z14,z3,z4]),(0,[z0,z112,z1,z113,z3,z4,z6])],[(0,[z0,z1,z2,z114,z3,z4,z6]),(1,[z0,z1,z115,z3,z4,z6]),(0,[z116,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z117,z4,z6]),(0,[z0,z1,z2,z3,z118,z4,z6]),(0,[z0,z86,z1,z2,z3,z4,z6]),(1,[z0,z78,z9,z1,z2,z4]),(0,[z0,z1,z2,z3,z4,z119,z6])],[(0,[z15,z0,z1,z2,z120,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z121]),(0,[z95,z0,z1,z2,z14,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z55]),(0,[z0,z1,z2,z14,z3,z4,z122]),(0,[z0,z45,z1,z2,z3,z4,z50])],[(0,[z0,z1,z2,z120,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z123,z6]),(0,[z0,z1,z2,z124,z3,z4,z6]),(0,[z0,z9,z125,z1,z2,z3,z4])],[(0,[z70,z0,z1,z2,z28,z4,z6]),(0,[z0,z1,z2,z126,z3,z4,z6]),(0,[z0,z1,z2,z127,z3,z4,z6]),(0,[z128,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z129])],[(0,[z0,z130,z1,z2,z3,z4,z6]),(0,[z131,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z132])],[(0,[z0,z1,z2,z3,z4,z133,z6]),(1,[z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z134,z6]),(0,[z0,z135,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z136,z4,z6])],[(0,[z44,z0,z1,z2,z3,z4,z12]),(0,[z0,z9,z1,z2,z3,z4,z96]),(0,[z81,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z137]),(0,[z0,z1,z48,z2,z3,z4,z6]),(0,[z0,z9,z45,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z138,z6]),(0,[z0,z1,z2,z139,z3,z4,z6]),(0,[z140,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z141,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z142,z6])],[(0,[z143,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z110]),(0,[z144,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z63])],[(0,[z145,z0,z1,z2,z3,z4,z6]),(0,[z0,z146,z1,z3,z71,z4,z6]),(0,[z147,z0,z1,z2,z3,z49,z4]),(0,[z0,z1,z2,z3,z4,z148,z6]),(0,[z0,z1,z2,z3,z37,z62,z6]),(0,[z0,z1,z2,z3,z4,z149,z6]),(0,[z0,z1,z150,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z113,z3,z4]),(0,[z35,z0,z1,z2,z3,z132,z6])],[(0,[z151,z0,z1,z2,z3,z4,z6]),(0,[z152,z0,z9,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z153]),(0,[z0,z107,z1,z2,z3,z4,z6])],[(0,[z154,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z40,z3,z4,z6]),(0,[z0,z1,z2,z3,z155,z4,z6]),(0,[z0,z1,z2,z3,z4,z156,z6]),(0,[z0,z9,z1,z2,z14,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z157])]],
   [[(0,[z158,z0,z1,z2,z3,z4,z6]),(0,[z159,z0,z1,z2,z14,z3,z4]),(0,[z0,z1,z2,z160,z3,z4,z6])],[(0,[z0,z161,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z162,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z163])],[(0,[z164,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z165,z3,z4,z6]),(0,[z0,z166,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z10,z4,z62,z6]),(0,[z0,z1,z167,z2,z3,z4,z6]),(0,[z168,z0,z9,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z169,z4,z6]),(0,[z1,z2,z160,z60,z3,z4,z6]),(0,[z0,z78,z1,z36,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z170,z6]),(0,[z171,z0,z1,z2,z14,z3,z4])],[(0,[z0,z1,z172,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z173]),(1,[z0,z1,z2,z174,z3,z4]),(0,[z0,z1,z175,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z176,z6])],[(0,[z177,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z178,z3,z4]),(0,[z179,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z4,z6,z180]),(1,[z0,z78,z1,z181,z4,z6]),(1,[z0,z1,z2,z3,z4,z182])],[(0,[z0,z1,z183,z2,z3,z4,z6]),(0,[z0,z1,z46,z2,z14,z3,z4])],[(0,[z0,z1,z2,z3,z4,z184,z6]),(0,[z0,z185,z2,z186,z3,z4,z6]),(0,[z0,z1,z2,z187,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z188]),(0,[z0,z9,z189,z1,z2,z3,z4]),(0,[z0,z1,z2,z190,z3,z4,z6]),(1,[z0,z1,z2,z191,z3,z4]),(0,[z192,z0,z1,z3,z4,z12,z6]),(0,[z0,z193,z1,z3,z4,z132,z6]),(0,[z0,z9,z1,z2,z4,z6,z63])]],
   [[(0,[z147,z0,z1,z2,z3,z4,z188]),(0,[z0,z1,z2,z14,z3,z66,z4]),(0,[z0,z1,z2,z3,z4,z62,z6])],[(0,[z0,z1,z2,z3,z4,z194,z6]),(0,[z0,z1,z2,z3,z4,z195,z6]),(0,[z0,z111,z1,z2,z3,z62,z6]),(0,[z0,z1,z2,z3,z4,z196,z6]),(0,[z0,z197,z1,z2,z3,z4,z6])],[(0,[z0,z1,z198,z2,z3,z4,z6]),(0,[z0,z199,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z11,z4,z21,z6]),(0,[z0,z1,z2,z3,z4,z200,z6]),(0,[z201,z0,z1,z2,z3,z4,z6]),(0,[z0,z202,z9,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z203,z6])],[(0,[z0,z1,z2,z3,z4,z69,z52]),(0,[z0,z1,z2,z204,z3,z4,z6]),(0,[z0,z111,z20,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z205,z4,z6]),(0,[z0,z1,z206,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z207]),(0,[z152,z0,z1,z2,z3,z4,z6]),(0,[z179,z0,z1,z2,z3,z11,z6]),(0,[z44,z0,z1,z2,z3,z4,z55]),(0,[z0,z111,z1,z2,z3,z10,z6])],[(0,[z0,z208,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z209,z6]),(1,[z0,z1,z2,z210,z4,z6]),(0,[z0,z211,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z212,z6]),(0,[z0,z9,z1,z2,z3,z4,z12]),(1,[z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z213,z6])],[(0,[z0,z1,z214,z2,z3,z4,z6]),(0,[z0,z215,z1,z2,z3,z4,z69])]],
   [[(0,[z83,z0,z1,z186,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z216]),(0,[z70,z0,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z217,z6]),(0,[z152,z0,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z3,z43,z4,z21]),(0,[z0,z1,z2,z3,z4,z218,z6]),(0,[z0,z1,z2,z3,z219,z4,z6]),(1,[z0,z1,z36,z113,z4,z6]),(0,[z0,z1,z2,z3,z4,z12,z50]),(0,[z220,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z63])],[(0,[z0,z9,z1,z2,z60,z3,z4]),(0,[z0,z1,z2,z3,z4,z221,z6]),(0,[z0,z1,z2,z3,z4,z6,z222]),(0,[z0,z45,z1,z2,z3,z4,z96]),(1,[z95,z0,z2,z3,z4,z69]),(0,[z0,z78,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z223,z4,z6]),(0,[z192,z0,z1,z2,z3,z4,z55]),(0,[z168,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z224,z14,z3,z4]),(0,[z0,z225,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z226,z6]),(0,[z0,z1,z2,z3,z4,z6,z227])],[(0,[z0,z1,z2,z3,z228,z4,z6]),(0,[z0,z1,z229,z2,z3,z4,z6]),(0,[z230,z0,z1,z2,z3,z4,z6])],[(0,[z0,z9,z1,z36,z2,z4,z6]),(0,[z0,z1,z2,z3,z49,z4,z50])],[(0,[z0,z1,z2,z3,z231,z4,z6]),(0,[z232,z0,z1,z2,z3,z4,z6]),(0,[z233,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z67,z2,z3,z4,z6]),(0,[z0,z9,z215,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z234,z6]),(1,[z0,z9,z1,z2,z14,z4])],[(0,[z38,z1,z40,z2,z3,z4,z6]),(0,[z0,z1,z48,z3,z37,z4,z6]),(0,[z0,z235,z1,z2,z3,z4,z6]),(0,[z0,z125,z1,z2,z3,z4,z6])],[(1,[z0,z236,z1,z2,z3,z4]),(0,[z0,z237,z1,z2,z3,z4,z6]),(0,[z0,z86,z1,z115,z3,z4,z6]),(0,[z0,z238,z1,z2,z3,z4,z6]),(0,[z0,z45,z1,z2,z14,z3,z4])]],
   [[(0,[z83,z0,z78,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z239,z4,z6]),(0,[z152,z0,z1,z2,z3,z11,z6]),(0,[z0,z189,z1,z2,z14,z3,z4]),(0,[z0,z1,z240,z2,z3,z4,z6])],[(0,[z0,z202,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z52,z6,z188]),(0,[z0,z241,z1,z2,z14,z3,z4]),(0,[z0,z86,z1,z2,z242,z4,z6]),(0,[z243,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z1,z2,z3,z37,z4]),(0,[z0,z1,z2,z3,z4,z6,z244])],[(0,[z0,z1,z245,z2,z3,z4,z6]),(0,[z19,z0,z2,z242,z3,z4,z6]),(0,[z0,z1,z2,z210,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z246,z6])],[(0,[z147,z0,z1,z2,z247,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z52]),(0,[z0,z248,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z249,z6]),(1,[z0,z1,z2,z3,z250,z6]),(0,[z0,z251,z1,z2,z3,z4,z6]),(0,[z0,z1,z36,z2,z3,z4,z252]),(0,[z0,z1,z2,z3,z4,z253,z6]),(0,[z0,z1,z2,z4,z253,z6,z55]),(0,[z0,z1,z2,z3,z254,z4,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z40,z2,z3,z4,z216]),(0,[z0,z1,z2,z3,z10,z21,z6]),(0,[z0,z1,z2,z3,z4,z255,z6]),(0,[z35,z0,z1,z2,z89,z4,z6]),(0,[z0,z193,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z256,z14,z3,z4])],[(0,[z0,z1,z60,z113,z3,z4,z6]),(0,[z0,z78,z1,z2,z181,z4,z6]),(0,[z0,z1,z2,z3,z257,z4,z6]),(0,[z0,z1,z2,z3,z4,z132,z6])],[(1,[z0,z9,z1,z2,z71,z4]),(1,[z0,z258,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z52,z6]),(0,[z0,z1,z2,z3,z259,z4,z6]),(1,[z0,z1,z2,z3,z219,z6]),(0,[z0,z1,z260,z2,z3,z4,z6])],[(0,[z70,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z261,z3,z4,z6]),(0,[z262,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z62]),(0,[z0,z215,z1,z2,z3,z4,z96]),(0,[z0,z1,z36,z2,z181,z4,z6]),(0,[z0,z112,z1,z2,z3,z4,z263]),(0,[z0,z1,z2,z3,z4,z264,z6]),(1,[z0,z1,z2,z14,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z265,z4,z6]),(0,[z0,z78,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z266,z4,z6]),(0,[z0,z1,z2,z14,z3,z79,z4])],[(0,[z19,z0,z245,z2,z3,z4,z6]),(0,[z19,z0,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z242,z71,z4,z6]),(0,[z267,z0,z1,z2,z3,z4,z6]),(1,[z0,z65,z2,z66,z4,z6]),(0,[z0,z1,z113,z3,z181,z4,z6]),(1,[z0,z268,z1,z2,z3,z6])],[(0,[z0,z9,z1,z40,z2,z3,z4]),(0,[z269,z0,z1,z2,z3,z4,z6]),(1,[z0,z215,z2,z3,z4,z96]),(0,[z0,z1,z2,z3,z49,z4,z69]),(0,[z0,z1,z36,z2,z3,z4,z6])],[(1,[z0,z1,z2,z120,z4,z6]),(1,[z0,z185,z2,z3,z4,z6]),(0,[z0,z270,z1,z2,z3,z4,z6]),(0,[z0,z271,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z272,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z273]),(0,[z274,z0,z1,z2,z14,z3,z4]),(0,[z0,z1,z2,z14,z3,z275,z4]),(0,[z0,z276,z1,z2,z14,z3,z4])],[(0,[z0,z277,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z186,z3,z4,z6]),(0,[z0,z236,z1,z2,z3,z4,z6]),(0,[z278,z0,z1,z2,z3,z4,z6]),(0,[z0,z279,z1,z2,z3,z4,z6]),(0,[z0,z86,z1,z2,z3,z4,z153]),(0,[z0,z1,z2,z3,z219,z181,z6])],[(0,[z0,z1,z2,z280,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z281,z6]),(1,[z19,z38,z2,z3,z4,z6]),(0,[z0,z282,z1,z2,z3,z4,z6]),(0,[z0,z1,z283,z2,z3,z4,z6])],[(0,[z0,z1,z2,z284,z3,z4,z6]),(0,[z0,z1,z285,z2,z3,z4,z6]),(0,[z0,z1,z2,z178,z3,z4,z6]),(0,[z147,z0,z9,z1,z2,z3,z4]),(0,[z0,z46,z2,z60,z3,z4,z6])],[(0,[z0,z286,z1,z2,z3,z4,z6]),(0,[z0,z241,z1,z2,z3,z148,z6]),(0,[z35,z0,z1,z2,z4,z132,z6]),(0,[z0,z287,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z288,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z289,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z122])],[(1,[z0,z290,z2,z3,z4,z6])],[(0,[z0,z9,z1,z245,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z291]),(1,[z59,z1,z2,z3,z4,z6]),(0,[z0,z112,z290,z2,z3,z4,z6])],[(0,[z0,z1,z40,z2,z14,z3,z4]),(0,[z0,z1,z2,z89,z3,z62,z6]),(0,[z0,z1,z292,z2,z3,z4,z6]),(0,[z0,z1,z293,z2,z3,z4,z6])],[(0,[z8,z0,z78,z1,z3,z4,z6]),(0,[z0,z1,z2,z242,z28,z4,z6]),(0,[z0,z1,z2,z3,z294,z4,z6]),(0,[z192,z0,z45,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z25,z132])],[(0,[z0,z258,z1,z2,z3,z4,z21]),(1,[z0,z1,z2,z3,z148,z6]),(0,[z0,z1,z2,z3,z295,z4,z6]),(1,[z0,z1,z141,z3,z4,z55]),(0,[z0,z1,z296,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z297,z6]),(0,[z0,z1,z2,z3,z4,z12,z96])],[(0,[z83,z0,z1,z2,z14,z3,z4]),(0,[z0,z1,z2,z14,z28,z3,z4]),(0,[z0,z1,z2,z89,z3,z10,z6]),(0,[z0,z1,z36,z2,z79,z4,z6]),(0,[z298,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z19,z0,z1,z2,z3,z4,z6]),(1,[z147,z1,z2,z3,z4,z52]),(0,[z0,z45,z1,z2,z3,z62,z6]),(0,[z0,z1,z2,z3,z299,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z300])],[(0,[z0,z1,z2,z3,z301,z4,z6]),(0,[z0,z1,z2,z28,z3,z4,z6]),(0,[z302,z0,z1,z2,z3,z71,z6]),(0,[z192,z0,z1,z2,z14,z3,z4])],[(0,[z0,z9,z1,z2,z3,z71,z4]),(0,[z303,z0,z1,z2,z3,z4,z6]),(0,[z0,z241,z1,z2,z3,z4,z64]),(0,[z0,z1,z2,z3,z49,z4,z96]),(0,[z0,z9,z1,z2,z113,z3,z4]),(1,[z0,z1,z2,z4,z253,z6]),(0,[z0,z304,z1,z2,z3,z4,z6])],[(0,[z305,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z306]),(0,[z0,z9,z1,z2,z3,z10,z4]),(0,[z0,z1,z2,z3,z4,z307,z6]),(0,[z308,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z309,z4,z6])],[(0,[z19,z0,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z310,z4,z6]),(0,[z0,z189,z20,z2,z3,z4,z6]),(0,[z0,z1,z311,z2,z3,z4,z6]),(0,[z0,z45,z1,z2,z3,z10,z6]),(0,[z0,z1,z2,z14,z3,z4,z6])],[(0,[z19,z0,z65,z2,z3,z4,z6]),(0,[z0,z146,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z312,z4,z6]),(0,[z147,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z313,z4,z6]),(0,[z0,z9,z1,z2,z314,z3,z4]),(0,[z0,z1,z2,z315,z3,z4,z6]),(0,[z0,z316,z1,z2,z3,z4,z6])],[(1,[z70,z1,z2,z71,z4,z6]),(0,[z0,z1,z2,z3,z4,z317,z6]),(0,[z0,z1,z141,z3,z4,z6,z55]),(0,[z0,z1,z2,z3,z318,z4,z6])],[(0,[z147,z1,z2,z3,z4,z52,z6]),(0,[z0,z1,z2,z60,z3,z4,z6]),(0,[z0,z319,z1,z2,z3,z4,z6]),(0,[z0,z320,z1,z2,z3,z4,z6])]],
   [[(0,[z321,z0,z1,z2,z3,z4,z6]),(0,[z15,z0,z2,z3,z4,z62,z6]),(1,[z0,z1,z2,z3,z4,z64]),(0,[z0,z1,z322,z2,z3,z4,z6])],[(0,[z15,z83,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z323,z3,z4,z6]),(0,[z0,z111,z2,z3,z4,z62,z6]),(0,[z0,z9,z1,z36,z2,z3,z4]),(0,[z53,z0,z1,z2,z14,z3,z4])],[(0,[z0,z91,z2,z186,z3,z4,z6]),(0,[z0,z324,z1,z2,z3,z4,z6]),(0,[z325,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z86,z1,z2,z3,z4]),(0,[z0,z326,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z327,z6])],[(0,[z328,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z124,z3,z71,z4,z6]),(0,[z0,z1,z2,z3,z4,z329,z6])],[(0,[z330,z0,z1,z2,z3,z4,z6]),(0,[z0,z78,z1,z3,z37,z4,z6]),(0,[z0,z1,z2,z3,z79,z4,z6]),(0,[z0,z1,z2,z14,z89,z3,z4])],[(0,[z0,z1,z2,z3,z71,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z331]),(0,[z0,z9,z1,z2,z3,z66,z4]),(0,[z0,z1,z2,z3,z10,z170,z6]),(0,[z35,z0,z78,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z332,z4,z6])],[(0,[z0,z1,z333,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z334,z6]),(0,[z0,z335,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z336]),(0,[z0,z9,z38,z1,z2,z3,z4]),(0,[z0,z1,z2,z186,z14,z3,z4]),(0,[z0,z1,z2,z3,z21,z62,z6]),(0,[z0,z1,z2,z3,z337,z4,z6]),(0,[z0,z1,z115,z2,z3,z4,z6]),(0,[z338,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z294,z4]),(0,[z0,z1,z2,z339,z3,z4,z6]),(0,[z0,z340,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z49,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z341,z6]),(0,[z70,z159,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z342]),(0,[z0,z1,z2,z3,z4,z343,z6]),(1,[z0,z9,z1,z36,z2,z4]),(0,[z192,z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z2,z89,z3,z132,z6])],[(0,[z0,z1,z2,z3,z344,z4,z6]),(1,[z8,z1,z40,z3,z4,z6]),(0,[z0,z345,z2,z3,z71,z4,z6]),(0,[z0,z1,z2,z3,z346,z4,z6]),(0,[z0,z1,z2,z3,z347,z4,z6]),(0,[z0,z86,z1,z2,z3,z250,z6]),(0,[z0,z1,z2,z3,z348,z4,z6]),(0,[z0,z1,z349,z2,z3,z4,z6]),(0,[z0,z20,z1,z2,z14,z3,z4]),(0,[z0,z350,z1,z2,z3,z4,z6]),(0,[z0,z9,z1,z141,z2,z3,z4]),(0,[z351,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z89,z79,z6])],[(0,[z0,z1,z2,z3,z4,z352,z6]),(0,[z0,z1,z2,z3,z353,z4,z6]),(0,[z0,z86,z1,z2,z66,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z354])],[(0,[z0,z1,z355,z2,z3,z4,z6]),(0,[z8,z0,z1,z2,z14,z3,z4]),(0,[z147,z44,z1,z2,z3,z4,z6]),(0,[z0,z1,z356,z2,z3,z4,z6])],[(0,[z0,z189,z1,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z37,z10,z6]),(0,[z0,z1,z2,z162,z3,z4,z6])],[(0,[z0,z241,z1,z60,z3,z4,z6]),(0,[z0,z86,z1,z2,z14,z3,z4]),(0,[z0,z1,z36,z113,z3,z4,z6]),(0,[z0,z1,z3,z4,z12,z6,z55]),(0,[z0,z1,z2,z3,z4,z6,z357])],[(1,[z0,z1,z2,z3,z358,z6]),(0,[z0,z1,z2,z359,z3,z4,z6]),(0,[z360,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z361,z3,z4,z6]),(0,[z0,z1,z2,z362,z3,z4,z6]),(0,[z0,z304,z1,z2,z3,z6,z55]),(0,[z0,z1,z363,z2,z3,z4,z6])],[(0,[z0,z364,z1,z2,z3,z4,z6]),(0,[z0,z365,z1,z2,z3,z4,z6]),(0,[z0,z65,z9,z1,z2,z3,z4]),(0,[z0,z112,z45,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z366,z6])]],
   [[(0,[z367,z0,z1,z2,z3,z4,z6]),(0,[z0,z368,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z369,z4,z6]),(1,[z192,z0,z1,z3,z4,z12])],[(0,[z0,z1,z2,z3,z370,z4,z6]),(0,[z0,z1,z2,z371,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z52]),(0,[z0,z1,z2,z79,z4,z132,z6]),(0,[z0,z1,z2,z3,z4,z6,z372])],[(0,[z373,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z374,z4,z6]),(0,[z0,z1,z2,z3,z11,z62,z6]),(0,[z0,z9,z1,z2,z3,z102,z4])],[(0,[z0,z375,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z376,z6]),(0,[z0,z111,z9,z1,z2,z3,z4]),(0,[z0,z1,z13,z2,z3,z4,z6])],[(1,[z0,z91,z2,z3,z4,z6]),(0,[z0,z377,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z255,z6]),(0,[z0,z1,z56,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z378,z6]),(0,[z0,z379,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z380,z3,z4,z6]),(0,[z0,z1,z2,z3,z381,z4,z6])],[(0,[z15,z0,z20,z2,z3,z4,z6]),(0,[z382,z0,z1,z2,z3,z4,z6]),(0,[z0,z383,z1,z2,z3,z4,z6]),(0,[z0,z1,z141,z2,z14,z3,z4]),(0,[z0,z9,z384,z1,z2,z3,z4]),(0,[z140,z0,z1,z2,z14,z3,z4])],[(0,[z0,z38,z1,z2,z3,z4,z6]),(0,[z0,z1,z385,z2,z3,z4,z6]),(0,[z0,z386,z1,z2,z4,z6,z55])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z188]),(0,[z0,z1,z46,z113,z3,z4,z6]),(0,[z0,z1,z2,z4,z122,z6,z63])],[(0,[z387,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z388,z6]),(0,[z35,z0,z1,z2,z3,z79,z6]),(0,[z0,z1,z2,z3,z4,z389,z6])],[(0,[z83,z38,z1,z2,z3,z4,z6]),(0,[z0,z390,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z391,z3,z4,z6])],[(0,[z0,z392,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z393]),(0,[z0,z20,z1,z2,z3,z4,z22])],[(1,[z0,z2,z124,z3,z4,z6]),(0,[z0,z1,z2,z3,z394,z4,z6]),(0,[z0,z189,z1,z46,z3,z4,z6])],[(0,[z1,z40,z2,z186,z3,z4,z6]),(0,[z179,z0,z1,z2,z14,z3,z4]),(0,[z0,z241,z1,z46,z3,z4,z6]),(0,[z395,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z113,z3,z4,z6]),(0,[z0,z1,z2,z3,z396,z4,z6]),(0,[z0,z9,z1,z2,z3,z79,z4])],[(0,[z397,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z11,z4]),(1,[z0,z189,z46,z3,z4,z6]),(0,[z0,z65,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z242,z3,z4,z6]),(0,[z0,z88,z1,z2,z4,z170,z6]),(0,[z0,z9,z1,z206,z2,z3,z4]),(0,[z0,z1,z2,z14,z3,z82,z4])],[(1,[z15,z245,z2,z3,z4,z6]),(0,[z0,z1,z40,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z216,z6]),(0,[z0,z1,z2,z3,z398,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z399]),(0,[z0,z1,z400,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z401,z4,z6]),(0,[z0,z1,z2,z3,z402,z4,z6]),(0,[z403,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z15,z1,z40,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z247,z4,z6]),(0,[z0,z20,z2,z3,z10,z4,z6]),(0,[z0,z1,z2,z191,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z404,z6]),(0,[z405,z0,z1,z2,z3,z4,z6])],[(0,[z15,z0,z1,z2,z3,z358,z6]),(0,[z0,z1,z2,z3,z4,z358,z6]),(0,[z406,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z407,z6]),(0,[z408,z0,z1,z2,z3,z4,z6]),(0,[z0,z45,z1,z141,z2,z3,z4]),(0,[z0,z1,z2,z14,z3,z3,z4])],[(0,[z0,z1,z2,z3,z4,z409,z6]),(0,[z410,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z411,z3,z4,z6]),(0,[z0,z20,z1,z2,z3,z62,z6]),(0,[z0,z412,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z413,z4,z6]),(0,[z0,z1,z2,z3,z414,z4,z6])],[(0,[z159,z0,z9,z1,z2,z3,z4]),(0,[z0,z415,z1,z2,z3,z4,z6]),(0,[z0,z112,z1,z3,z4,z170,z6])],[(0,[z0,z1,z2,z416,z3,z4,z6]),(0,[z0,z1,z2,z3,z294,z4,z170])],[(0,[z0,z417,z1,z2,z3,z4,z6]),(0,[z0,z1,z141,z2,z3,z4,z12]),(0,[z0,z1,z3,z4,z418,z132,z6])],[(0,[z0,z1,z419,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z420,z6]),(0,[z0,z1,z2,z3,z4,z6,z421]),(0,[z0,z1,z2,z422,z3,z4,z6]),(0,[z0,z20,z1,z2,z3,z10,z6])],[(0,[z0,z1,z2,z14,z3,z181,z4]),(0,[z0,z423,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z94,z3,z4,z170]),(1,[z0,z193,z1,z3,z4,z6]),(0,[z0,z1,z2,z204,z14,z3,z4])]],
   [[(0,[z0,z424,z1,z2,z3,z4,z6]),(0,[z152,z0,z1,z2,z14,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z425]),(0,[z0,z1,z2,z426,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z153,z6])],[(0,[z0,z1,z2,z3,z4,z427,z6]),(0,[z0,z189,z2,z3,z4,z62,z6]),(0,[z0,z428,z1,z2,z3,z4,z6]),(0,[z0,z1,z48,z2,z3,z170,z6])],[(0,[z0,z429,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z430,z6])],[(0,[z0,z431,z1,z2,z3,z4,z6]),(0,[z19,z0,z38,z2,z3,z4,z6]),(0,[z0,z112,z1,z2,z14,z3,z4])],[(0,[z432,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z433,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z434,z6]),(0,[z0,z1,z2,z3,z435,z4,z6])],[(0,[z436,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z437,z6]),(0,[z0,z86,z1,z2,z3,z4,z110]),(0,[z0,z1,z2,z3,z4,z6,z438]),(0,[z0,z439,z1,z2,z3,z4,z6]),(0,[z0,z440,z1,z2,z3,z4,z6]),(0,[z441,z0,z1,z2,z3,z4,z6])],[(0,[z0,z2,z60,z3,z4,z62,z6]),(0,[z0,z442,z1,z2,z3,z4,z6]),(0,[z0,z112,z1,z2,z3,z37,z6])],[(0,[z0,z1,z2,z3,z4,z443,z6]),(0,[z444,z0,z1,z2,z3,z4,z6]),(0,[z0,z112,z1,z2,z3,z4,z273]),(0,[z0,z1,z2,z3,z4,z445,z6])]],
   [[(0,[z19,z0,z241,z2,z3,z4,z6]),(0,[z0,z446,z1,z2,z3,z4,z6]),(0,[z0,z447,z1,z2,z3,z4,z6]),(0,[z147,z0,z1,z2,z3,z4,z55]),(0,[z0,z1,z2,z174,z3,z66,z4]),(0,[z0,z215,z1,z2,z14,z3,z4]),(0,[z448,z0,z1,z2,z3,z4,z6]),(0,[z449,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z450,z6])],[(0,[z0,z451,z1,z2,z3,z4,z6]),(0,[z0,z1,z452,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z453,z6]),(0,[z0,z1,z2,z3,z4,z454,z6])],[(0,[z455,z0,z1,z2,z3,z4,z6]),(0,[z159,z0,z1,z2,z3,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z188]),(0,[z0,z1,z2,z456,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z52,z96]),(1,[z0,z161,z2,z3,z4,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z96,z188]),(0,[z0,z1,z2,z3,z4,z457,z6])],[(0,[z0,z1,z2,z3,z458,z4,z6]),(0,[z0,z1,z2,z3,z4,z459,z6]),(0,[z35,z0,z9,z1,z2,z3,z4])],[(0,[z15,z0,z1,z2,z3,z4,z460]),(0,[z0,z241,z1,z2,z3,z4,z461]),(0,[z0,z1,z462,z2,z3,z4,z6]),(0,[z0,z463,z1,z2,z3,z4,z6]),(0,[z464,z0,z1,z2,z14,z3,z4]),(0,[z0,z465,z1,z2,z3,z4,z6])],[(0,[z0,z466,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z467,z6]),(0,[z0,z1,z2,z3,z181,z4,z6])]],
   [[(0,[z0,z345,z1,z2,z3,z4,z6]),(1,[z0,z1,z416,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z69,z188]),(0,[z0,z1,z46,z2,z3,z4,z6])],[(0,[z0,z1,z468,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z69]),(0,[z0,z1,z2,z3,z469,z4,z6]),(0,[z0,z1,z141,z2,z3,z4,z55]),(0,[z0,z470,z1,z2,z3,z4,z6]),(0,[z0,z9,z1,z2,z89,z3,z4]),(0,[z0,z1,z2,z3,z4,z24,z6]),(0,[z0,z1,z2,z471,z3,z4,z6])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(1,[z302,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z472]),(0,[z0,z268,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z473,z3,z4,z6]),(0,[z0,z1,z2,z261,z14,z3,z4])],[(0,[z0,z215,z2,z3,z4,z6,z96]),(0,[z0,z1,z474,z2,z3,z4,z6]),(0,[z0,z78,z1,z2,z14,z3,z4]),(0,[z35,z0,z112,z1,z2,z3,z6]),(0,[z475,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z255,z6,z55])],[(0,[z476,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z461]),(0,[z0,z1,z2,z477,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z478]),(0,[z0,z9,z1,z2,z3,z49,z4])],[(0,[z0,z479,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z480,z6]),(0,[z0,z1,z2,z481,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z482]),(0,[z0,z483,z1,z2,z3,z4,z6]),(0,[z0,z45,z1,z2,z3,z49,z6]),(1,[z0,z45,z1,z2,z3,z50])],[(0,[z0,z9,z1,z2,z186,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z252])],[(0,[z0,z1,z2,z3,z484,z4,z6]),(0,[z0,z9,z1,z2,z71,z4,z6]),(0,[z147,z0,z1,z2,z210,z4,z6]),(0,[z0,z1,z2,z3,z4,z485,z6]),(0,[z0,z112,z1,z2,z3,z170,z6])]],
   [[(0,[z159,z0,z1,z2,z71,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z24])],[(0,[z486,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z487,z6]),(0,[z0,z1,z2,z3,z488,z4,z6]),(0,[z35,z152,z0,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z489,z4,z6]),(0,[z0,z490,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z491,z4,z6]),(1,[z0,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z275,z4,z6])],[(0,[z0,z1,z2,z492,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z418,z6]),(0,[z0,z493,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z494,z4,z6])],[(0,[z95,z0,z1,z2,z3,z495,z6]),(0,[z35,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z0,z496,z1,z2,z3,z4,z6]),(0,[z0,z65,z1,z2,z242,z4,z6]),(0,[z0,z497,z1,z2,z3,z4,z6])],[(0,[z0,z498,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z473,z3,z4])],[(0,[z0,z1,z46,z40,z3,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z188])]],
   [[(0,[z0,z1,z416,z3,z71,z4,z6]),(0,[z0,z1,z2,z14,z242,z3,z4]),(0,[z0,z1,z2,z4,z5,z170,z6])],[(0,[z0,z1,z2,z28,z66,z4,z6]),(0,[z0,z1,z499,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z96]),(0,[z0,z78,z1,z2,z113,z4,z6]),(0,[z0,z1,z2,z500,z3,z4,z6]),(0,[z0,z45,z1,z2,z3,z4,z6])],[(0,[z0,z9,z1,z2,z28,z4,z6]),(0,[z0,z1,z2,z3,z501,z4,z6]),(0,[z0,z189,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z69,z6,z96]),(1,[z0,z1,z2,z3,z4,z252])],[(0,[z0,z1,z2,z3,z502,z4,z6]),(0,[z19,z0,z1,z2,z14,z3,z4]),(0,[z0,z1,z503,z2,z3,z4,z6]),(0,[z70,z1,z2,z3,z71,z4,z6]),(0,[z159,z0,z1,z2,z28,z4,z6]),(0,[z147,z0,z45,z1,z2,z3,z4]),(1,[z0,z241,z60,z3,z4,z6]),(0,[z0,z78,z1,z2,z4,z122,z6]),(0,[z0,z1,z2,z191,z3,z181,z4]),(0,[z0,z1,z2,z3,z4,z504,z6])],[(0,[z0,z65,z86,z2,z3,z4,z6]),(0,[z0,z78,z112,z1,z3,z4,z6]),(0,[z0,z505,z1,z2,z3,z4,z6]),(0,[z506,z0,z1,z2,z3,z4,z6])],[(0,[z179,z1,z2,z3,z4,z21,z6]),(1,[z0,z324,z2,z3,z4,z6]),(0,[z507,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z508,z4,z6]),(0,[z0,z1,z36,z2,z4,z122,z6]),(0,[z0,z1,z509,z2,z3,z4,z6])],[(0,[z15,z0,z2,z242,z3,z4,z6]),(0,[z0,z1,z2,z3,z510,z4,z6]),(0,[z0,z511,z1,z2,z3,z4,z6]),(0,[z0,z1,z113,z3,z37,z4,z6]),(0,[z0,z1,z2,z256,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z512,z6]),(0,[z0,z1,z2,z3,z4,z6,z513])],[(0,[z0,z185,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z514,z71,z6]),(0,[z0,z1,z2,z3,z4,z6,z515]),(1,[z0,z1,z2,z3,z109,z6]),(0,[z0,z1,z2,z3,z516,z4,z6]),(0,[z0,z1,z2,z314,z3,z4,z6])]],
   [[(0,[z44,z0,z9,z1,z2,z3,z4]),(0,[z147,z0,z1,z2,z14,z3,z4]),(0,[z517,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z250,z4,z6]),(0,[z0,z1,z2,z3,z79,z4,z513])],[(0,[z0,z1,z518,z2,z3,z4,z6]),(0,[z0,z1,z519,z2,z3,z4,z6]),(0,[z0,z1,z2,z89,z79,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z213])],[(0,[z0,z1,z2,z3,z4,z6,z41]),(0,[z0,z1,z2,z60,z14,z3,z4]),(0,[z0,z520,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z521,z6])],[(0,[z522,z0,z1,z2,z3,z4,z6]),(0,[z0,z523,z1,z2,z3,z4,z6]),(0,[z0,z524,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z525]),(0,[z0,z1,z2,z3,z4,z526,z6]),(0,[z0,z1,z2,z3,z4,z6,z263]),(0,[z192,z0,z9,z1,z2,z3,z4])],[(0,[z15,z0,z245,z2,z3,z4,z6]),(0,[z15,z0,z9,z1,z2,z3,z4]),(0,[z8,z83,z1,z2,z3,z4,z6]),(0,[z274,z0,z1,z2,z3,z4,z6]),(0,[z0,z276,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z527]),(1,[z0,z2,z3,z4,z297,z6]),(0,[z0,z1,z528,z2,z3,z4,z6]),(1,[z0,z304,z1,z2,z3,z6]),(0,[z0,z384,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z529,z6])]],
   [[(0,[z0,z112,z1,z48,z3,z4,z6]),(0,[z0,z1,z48,z2,z14,z3,z4]),(0,[z530,z0,z1,z2,z3,z4,z6]),(1,[z35,z0,z1,z2,z132,z6])],[(0,[z0,z1,z2,z3,z4,z531,z6]),(0,[z0,z1,z532,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z533,z6]),(0,[z0,z241,z2,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z534,z4,z6]),(0,[z95,z0,z9,z1,z2,z3,z4]),(0,[z535,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z37,z4,z6])],[(1,[z0,z1,z2,z3,z4,z196]),(0,[z143,z0,z1,z2,z14,z3,z4])],[(0,[z0,z1,z2,z536,z3,z4,z6]),(0,[z0,z537,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z538]),(0,[z0,z1,z48,z2,z3,z37,z6]),(0,[z0,z539,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z540,z4,z6]),(0,[z0,z1,z2,z14,z3,z381,z4]),(0,[z0,z1,z2,z3,z541,z4,z6])],[(0,[z542,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z543,z4,z6]),(0,[z0,z1,z2,z28,z4,z122,z6]),(0,[z0,z1,z2,z544,z3,z4,z6]),(0,[z0,z1,z2,z174,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z545,z6]),(0,[z0,z1,z546,z2,z3,z4,z6]),(0,[z0,z1,z2,z89,z3,z79,z6])],[(0,[z0,z1,z40,z2,z3,z4,z6]),(0,[z0,z547,z1,z2,z3,z4,z6])],[(0,[z0,z548,z1,z2,z3,z4,z6]),(0,[z549,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z12])],[(0,[z0,z1,z2,z3,z550,z4,z6]),(0,[z44,z0,z1,z2,z3,z4,z6]),(0,[z147,z0,z1,z2,z3,z4,z12]),(1,[z0,z112,z1,z3,z170,z6]),(0,[z0,z1,z2,z14,z4,z122,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z551,z6]),(0,[z95,z0,z1,z2,z3,z545,z6]),(0,[z0,z552,z1,z2,z3,z4,z6])],[(1,[z0,z146,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z553,z6]),(0,[z554,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z109,z6])],[(0,[z0,z555,z1,z2,z3,z4,z6]),(0,[z0,z556,z1,z2,z3,z4,z6]),(0,[z0,z241,z1,z2,z3,z394,z6]),(0,[z192,z0,z1,z2,z3,z4,z6])],[(0,[z15,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z557,z2,z3,z4,z6])],[(1,[z83,z1,z186,z3,z4,z6]),(0,[z0,z111,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z69,z6]),(0,[z0,z1,z2,z473,z3,z181,z4]),(0,[z0,z1,z2,z3,z4,z273,z6]),(0,[z0,z1,z2,z3,z4,z6,z558]),(0,[z0,z9,z9,z1,z2,z3,z4])],[(1,[z0,z1,z2,z3,z4,z460]),(0,[z0,z1,z559,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z560,z6])],[(0,[z0,z1,z2,z3,z4,z561,z6]),(0,[z0,z78,z1,z60,z3,z4,z6])]],
   [[(0,[z15,z0,z46,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z562]),(0,[z95,z0,z1,z2,z3,z4,z6])],[(0,[z563,z0,z1,z2,z3,z4,z6]),(0,[z15,z0,z65,z2,z3,z4,z6]),(0,[z0,z1,z2,z564,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z565,z6]),(1,[z0,z1,z2,z3,z394,z6]),(0,[z0,z1,z2,z3,z4,z566,z6]),(0,[z0,z1,z2,z3,z4,z6,z567]),(0,[z171,z0,z9,z1,z2,z3,z4])],[(1,[z0,z1,z2,z3,z514,z6]),(0,[z159,z0,z1,z2,z3,z4,z72]),(0,[z0,z1,z2,z14,z3,z4,z21]),(0,[z44,z0,z1,z2,z3,z49,z4]),(0,[z0,z1,z2,z3,z4,z568,z6]),(0,[z0,z1,z569,z2,z3,z4,z6]),(0,[z0,z112,z1,z2,z3,z24,z6])],[(0,[z0,z1,z2,z3,z4,z6,z570]),(0,[z0,z1,z2,z571,z3,z4,z6]),(0,[z0,z1,z572,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z573,z6]),(0,[z0,z1,z2,z3,z574,z4,z6]),(0,[z0,z1,z2,z575,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z576]),(0,[z0,z1,z2,z3,z4,z6,z577])],[(0,[z0,z1,z46,z186,z3,z4,z6]),(0,[z0,z578,z1,z2,z3,z4,z6]),(0,[z147,z0,z1,z2,z3,z4,z52]),(0,[z0,z1,z2,z3,z579,z4,z6])],[(0,[z0,z1,z580,z2,z3,z4,z6]),(0,[z0,z1,z2,z581,z3,z4,z6]),(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z0,z583,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z584,z3,z4,z6]),(0,[z19,z38,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z71,z66,z4,z6]),(0,[z585,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z11,z4,z297,z6]),(0,[z0,z1,z586,z2,z3,z4,z6]),(0,[z192,z0,z1,z2,z3,z49,z4]),(0,[z0,z1,z2,z14,z3,z4,z50])],[(0,[z0,z1,z2,z3,z4,z587,z6]),(0,[z0,z9,z1,z2,z28,z3,z4]),(0,[z588,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z589,z6]),(0,[z0,z1,z2,z14,z3,z4,z170]),(1,[z0,z483,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z182,z6])]],
   [[(1,[z0,z1,z2,z3,z495,z6]),(0,[z590,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z591,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z592,z6])],[(0,[z0,z1,z2,z186,z3,z4,z6]),(0,[z0,z1,z2,z593,z3,z4,z6]),(0,[z0,z1,z2,z3,z62,z170,z6]),(0,[z95,z0,z215,z2,z3,z4,z6])],[(0,[z0,z236,z1,z2,z3,z71,z4]),(0,[z0,z594,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z37,z4,z170,z6]),(0,[z0,z1,z2,z14,z3,z4,z55])],[(0,[z595,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z67,z2,z3,z4]),(0,[z0,z1,z2,z596,z3,z4,z6]),(0,[z0,z1,z2,z3,z10,z24,z6]),(0,[z0,z597,z9,z1,z2,z3,z4])],[(0,[z83,z1,z2,z186,z3,z4,z6]),(0,[z8,z1,z40,z2,z3,z4,z6]),(0,[z0,z1,z2,z178,z3,z71,z4]),(0,[z0,z324,z2,z3,z11,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z50])],[(0,[z15,z0,z1,z2,z3,z4,z527]),(0,[z0,z598,z1,z2,z3,z4,z6]),(0,[z159,z0,z1,z2,z3,z4,z599]),(1,[z44,z1,z2,z3,z4,z188]),(0,[z0,z1,z600,z2,z3,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z24])],[(0,[z0,z601,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z602,z4,z6])],[(0,[z15,z0,z1,z2,z603,z4,z6]),(0,[z0,z1,z2,z604,z3,z4,z6]),(0,[z0,z1,z2,z3,z605,z4,z6]),(0,[z0,z1,z2,z3,z606,z4,z6]),(0,[z0,z1,z2,z3,z4,z607,z6]),(0,[z0,z78,z1,z46,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z608,z6]),(0,[z0,z1,z2,z3,z4,z609,z6]),(0,[z0,z112,z161,z2,z3,z4,z6])]],
   [[(0,[z171,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z245,z2,z14,z3,z4]),(0,[z179,z0,z1,z2,z89,z3,z6]),(0,[z179,z0,z9,z1,z2,z3,z4]),(1,[z1,z2,z160,z3,z4,z6]),(0,[z0,z1,z2,z610,z3,z4,z6])],[(1,[z0,z1,z2,z3,z301,z6]),(0,[z0,z1,z2,z87,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z611,z6]),(0,[z0,z612,z1,z2,z3,z4,z6]),(0,[z0,z613,z1,z2,z3,z4,z6])],[(0,[z0,z614,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z615,z4,z6]),(1,[z0,z1,z2,z247,z4,z6])],[(0,[z0,z1,z616,z2,z3,z4,z6]),(0,[z617,z0,z1,z2,z3,z4,z6]),(0,[z35,z179,z0,z1,z2,z3,z6]),(0,[z0,z618,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z495,z4,z6])],[(0,[z0,z619,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z620,z6]),(0,[z0,z621,z1,z2,z3,z4,z6]),(0,[z0,z20,z1,z2,z3,z4,z196]),(0,[z0,z1,z2,z3,z4,z622,z6])],[(0,[z623,z0,z1,z2,z3,z4,z6]),(0,[z70,z0,z1,z2,z14,z3,z4]),(0,[z624,z0,z1,z2,z3,z4,z6]),(0,[z0,z9,z1,z2,z242,z3,z4]),(0,[z0,z1,z2,z3,z4,z625,z6])],[(0,[z0,z1,z2,z3,z4,z626,z6])],[(0,[z0,z241,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z627,z3,z4,z6]),(0,[z628,z0,z1,z2,z3,z4,z6]),(0,[z629,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z630,z3,z4,z6]),(0,[z631,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z632,z6]),(0,[z0,z1,z2,z633,z3,z4,z6]),(0,[z0,z634,z1,z2,z3,z4,z6]),(0,[z0,z1,z36,z2,z14,z3,z4]),(0,[z0,z1,z2,z3,z79,z4,z182]),(0,[z0,z1,z2,z14,z3,z4,z103])],[(0,[z0,z1,z2,z3,z4,z6,z635]),(0,[z0,z1,z2,z71,z4,z122,z6]),(0,[z0,z20,z2,z60,z3,z4,z6]),(0,[z0,z1,z636,z2,z3,z4,z6]),(1,[z0,z111,z2,z3,z62,z6]),(0,[z0,z1,z2,z3,z637,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z638]),(1,[z0,z1,z2,z14,z4,z122]),(0,[z0,z1,z2,z639,z3,z4,z6])],[(0,[z0,z1,z2,z14,z3,z71,z4]),(0,[z640,z0,z1,z2,z3,z4,z6]),(0,[z0,z597,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z49,z24,z6])],[(0,[z0,z1,z2,z16,z3,z4,z6]),(0,[z152,z0,z1,z2,z89,z3,z6]),(0,[z0,z1,z2,z14,z3,z10,z4])],[(0,[z641,z0,z1,z2,z3,z4,z6]),(0,[z83,z0,z1,z113,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z642,z6])],[(0,[z0,z1,z2,z3,z4,z482,z6]),(0,[z0,z643,z1,z2,z3,z4,z6])],[(0,[z644,z0,z1,z2,z3,z4,z6]),(1,[z0,z345,z2,z3,z4,z6]),(0,[z0,z645,z1,z2,z3,z4,z6]),(0,[z0,z9,z20,z1,z2,z3,z4]),(0,[z0,z45,z1,z2,z3,z4,z69]),(0,[z0,z112,z1,z2,z89,z3,z6]),(0,[z0,z112,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z224,z3,z4,z6]),(0,[z0,z1,z2,z646,z3,z4,z6])],[(0,[z179,z0,z1,z2,z3,z4,z6]),(0,[z0,z258,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z647,z4,z6]),(0,[z0,z1,z2,z89,z3,z4,z6]),(0,[z0,z483,z1,z2,z3,z4,z132]),(0,[z0,z648,z9,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z460,z6]),(0,[z0,z1,z2,z3,z4,z6,z599]),(0,[z0,z649,z1,z2,z3,z4,z6])],[(0,[z0,z650,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z72]),(0,[z0,z241,z189,z2,z3,z4,z6]),(0,[z0,z1,z2,z651,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z652,z6]),(0,[z0,z1,z2,z14,z3,z4,z132]),(0,[z0,z653,z9,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z49,z24])],[(0,[z15,z19,z1,z2,z3,z4,z6]),(0,[z302,z0,z1,z2,z3,z4,z6]),(0,[z159,z1,z2,z28,z3,z4,z6]),(1,[z0,z1,z2,z3,z43,z4]),(0,[z0,z1,z2,z3,z66,z4,z6]),(0,[z0,z1,z2,z3,z654,z4,z6]),(1,[z0,z386,z1,z2,z4,z6])],[(1,[z159,z1,z2,z28,z4,z6]),(0,[z0,z1,z141,z2,z3,z49,z4])],[(0,[z15,z0,z1,z2,z3,z301,z6]),(0,[z0,z655,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z656]),(1,[z0,z1,z2,z3,z545,z6]),(0,[z0,z1,z2,z657,z3,z4,z6]),(0,[z658,z0,z9,z1,z2,z3,z4])],[(0,[z179,z152,z1,z2,z3,z4,z6]),(1,[z0,z1,z87,z3,z4,z6]),(0,[z0,z88,z1,z2,z3,z4,z6]),(0,[z0,z45,z1,z2,z3,z4,z24])],[(0,[z0,z241,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z659]),(0,[z0,z1,z36,z2,z113,z4,z6])],[(0,[z660,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z661,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z63])]],
   [[(1,[z0,z1,z198,z3,z4,z6]),(0,[z0,z1,z2,z3,z603,z4,z6]),(0,[z0,z1,z2,z3,z4,z662,z6]),(0,[z0,z1,z663,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z664]),(0,[z0,z189,z46,z2,z3,z4,z6]),(0,[z0,z268,z1,z2,z3,z181,z6]),(0,[z0,z1,z290,z2,z3,z4,z6]),(0,[z192,z0,z1,z141,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z665,z6]),(0,[z0,z1,z2,z3,z4,z666,z6]),(0,[z0,z1,z2,z3,z4,z6,z96]),(0,[z667,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z14,z3,z4])],[(0,[z44,z1,z2,z3,z4,z6,z188]),(0,[z0,z1,z668,z2,z3,z4,z6]),(0,[z0,z1,z36,z2,z3,z4,z482]),(0,[z0,z669,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z19,z0,z2,z3,z4,z62,z6]),(1,[z0,z1,z2,z3,z4,z599]),(1,[z179,z1,z2,z3,z21,z6]),(0,[z0,z1,z2,z670,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z96,z55]),(0,[z0,z1,z2,z3,z4,z671,z6])],[(0,[z83,z0,z9,z1,z2,z3,z4]),(0,[z59,z0,z1,z2,z3,z4,z6]),(0,[z0,z493,z1,z2,z3,z4,z6]),(0,[z0,z112,z1,z2,z3,z4,z6]),(0,[z672,z0,z1,z2,z3,z4,z6])],[(0,[z0,z9,z1,z2,z3,z11,z4]),(0,[z0,z1,z2,z3,z4,z461,z6]),(0,[z0,z2,z242,z3,z66,z4,z6]),(0,[z673,z0,z1,z2,z3,z4,z6]),(0,[z0,z648,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z674,z3,z4,z6]),(0,[z0,z386,z1,z2,z3,z4,z6])],[(0,[z15,z0,z38,z2,z3,z4,z6]),(1,[z0,z1,z16,z3,z4,z6]),(0,[z0,z1,z2,z3,z675,z4,z6]),(0,[z152,z1,z2,z3,z11,z4,z6]),(0,[z0,z1,z2,z676,z3,z4,z6]),(0,[z677,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z48,z2,z3,z24,z6]),(0,[z35,z0,z1,z2,z14,z3,z4]),(0,[z0,z678,z1,z2,z3,z4,z6])]],
   [[(0,[z679,z0,z1,z2,z3,z4,z6]),(0,[z8,z0,z1,z113,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z69,z55]),(0,[z0,z1,z2,z3,z4,z6,z680]),(0,[z0,z653,z1,z2,z3,z4,z6])],[(0,[z681,z0,z1,z2,z3,z4,z6]),(0,[z95,z0,z2,z3,z4,z69,z6]),(0,[z0,z9,z1,z2,z3,z3,z4])],[(0,[z0,z1,z186,z60,z3,z4,z6]),(0,[z0,z215,z1,z2,z3,z4,z6]),(0,[z0,z1,z682,z2,z3,z4,z6]),(0,[z35,z0,z1,z48,z2,z3,z6]),(1,[z0,z1,z3,z4,z418,z6])],[(0,[z683,z0,z1,z2,z3,z4,z6]),(0,[z658,z0,z1,z2,z3,z4,z6]),(0,[z684,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z685,z4,z6]),(0,[z0,z1,z2,z3,z686,z4,z6])],[(0,[z15,z0,z241,z2,z3,z4,z6]),(0,[z0,z1,z2,z687,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z688]),(0,[z0,z1,z2,z3,z62,z24,z6]),(0,[z689,z0,z1,z2,z3,z4,z6]),(0,[z0,z45,z1,z2,z3,z6,z50])],[(0,[z0,z1,z2,z3,z514,z4,z6]),(0,[z0,z690,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z691,z6]),(1,[z0,z1,z2,z3,z4,z513]),(0,[z0,z1,z2,z3,z4,z122,z6])],[(0,[z0,z1,z2,z3,z10,z4,z6]),(0,[z0,z9,z1,z48,z2,z3,z4]),(0,[z692,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z693,z6]),(0,[z0,z9,z1,z2,z3,z4,z21]),(0,[z0,z1,z2,z3,z4,z694,z6]),(0,[z0,z78,z1,z3,z181,z4,z6]),(0,[z0,z9,z1,z2,z3,z181,z4]),(0,[z0,z45,z1,z48,z2,z3,z6])]],
   [[(0,[z0,z695,z1,z2,z3,z4,z6]),(0,[z464,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z696,z4,z6]),(0,[z0,z697,z1,z2,z3,z4,z6])],[(0,[z0,z9,z1,z2,z14,z4,z6])],[(0,[z15,z0,z1,z198,z3,z4,z6]),(0,[z698,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z699,z6]),(0,[z0,z1,z700,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z12,z69]),(1,[z0,z1,z2,z3,z4,z263]),(1,[z0,z1,z2,z94,z3,z4]),(0,[z0,z9,z1,z2,z3,z4,z50])],[(0,[z83,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z701]),(0,[z0,z1,z2,z702,z3,z4,z6]),(0,[z0,z86,z2,z242,z3,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z170])],[(1,[z0,z1,z2,z3,z4,z527]),(0,[z15,z1,z245,z2,z3,z4,z6]),(0,[z0,z703,z1,z2,z3,z4,z6]),(1,[z152,z1,z2,z3,z11,z6]),(0,[z0,z1,z2,z3,z4,z704,z6]),(0,[z0,z1,z2,z3,z4,z705,z6]),(0,[z95,z0,z1,z2,z3,z4,z69])],[(0,[z38,z1,z245,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z11,z4,z6]),(0,[z0,z706,z1,z2,z3,z4,z6]),(1,[z0,z86,z2,z242,z4,z6]),(0,[z0,z1,z2,z3,z4,z55,z50])],[(1,[z0,z1,z2,z603,z4,z6]),(0,[z0,z9,z1,z2,z3,z4,z55])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z707,z3,z4,z6]),(0,[z0,z1,z2,z14,z4,z573]),(0,[z0,z1,z2,z3,z109,z153]),(0,[z0,z1,z36,z113,z4,z482])],[(0,[z0,z78,z1,z219,z181,z6])],[(0,[z0,z1,z2,z3,z4,z153]),(0,[z0,z1,z2,z3,z62,z196]),(0,[z0,z290,z2,z3,z24,z6])],[(0,[z0,z1,z2,z708,z4,z6]),(0,[z15,z46,z40,z3,z4,z6]),(0,[z0,z185,z2,z3,z4,z709]),(0,[z0,z386,z1,z2,z4,z69]),(0,[z0,z304,z1,z2,z253,z6]),(0,[z0,z9,z1,z2,z162,z4]),(0,[z0,z9,z710,z2,z3,z4])],[(0,[z0,z1,z2,z711,z3,z4]),(0,[z70,z9,z1,z2,z71,z4]),(0,[z0,z258,z1,z2,z3,z62]),(0,[z147,z0,z386,z1,z2,z4]),(0,[z0,z1,z712,z3,z4,z6]),(0,[z0,z86,z2,z14,z242,z4]),(0,[z0,z161,z2,z3,z4,z263]),(0,[z0,z304,z1,z2,z3,z50])],[(0,[z0,z345,z2,z3,z4,z6]),(0,[z0,z46,z584,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z713]),(0,[z70,z2,z124,z71,z4,z6]),(0,[z0,z714,z1,z2,z3,z4]),(0,[z0,z161,z2,z14,z3,z4]),(0,[z0,z1,z2,z3,z4,z715]),(0,[z0,z710,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z49,z103])],[(0,[z0,z9,z1,z2,z604,z4]),(0,[z0,z716,z1,z2,z3,z6]),(0,[z68,z1,z2,z3,z4,z188]),(0,[z0,z1,z56,z3,z4,z12]),(0,[z35,z0,z1,z2,z14,z132])],[(0,[z0,z1,z2,z3,z717,z6]),(0,[z0,z78,z1,z473,z181,z4]),(0,[z0,z1,z2,z3,z4,z718]),(0,[z0,z9,z1,z2,z3,z719])]],
   [[(0,[z0,z555,z46,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z72]),(0,[z0,z1,z2,z3,z720,z6]),(0,[z0,z1,z2,z174,z3,z4])],[(0,[z0,z1,z2,z721,z4,z6]),(0,[z0,z1,z2,z3,z301,z527]),(0,[z0,z1,z2,z3,z4,z722]),(0,[z0,z1,z2,z3,z4,z723]),(0,[z0,z276,z2,z3,z4,z96]),(0,[z0,z78,z1,z181,z4,z6]),(0,[z0,z1,z2,z79,z662,z6]),(0,[z0,z1,z2,z3,z4,z724]),(0,[z0,z1,z2,z3,z4,z182]),(0,[z0,z1,z2,z89,z725,z6]),(0,[z168,z0,z1,z2,z3,z213]),(0,[z0,z1,z2,z14,z4,z357])],[(0,[z0,z726,z1,z2,z4,z6]),(0,[z1,z2,z3,z727,z4,z6]),(0,[z159,z1,z2,z28,z4,z599]),(0,[z0,z2,z14,z3,z4,z297]),(0,[z0,z1,z2,z3,z4,z728]),(0,[z1,z2,z3,z729,z4,z6]),(0,[z95,z0,z2,z3,z275,z4])],[(0,[z0,z1,z2,z3,z4,z730]),(0,[z0,z9,z1,z2,z261,z4]),(0,[z0,z678,z1,z3,z4,z12])],[(0,[z0,z731,z1,z3,z4,z6]),(0,[z0,z1,z732,z3,z4,z6]),(0,[z0,z1,z2,z733,z3,z4]),(0,[z0,z1,z2,z3,z734,z6])],[(0,[z0,z1,z2,z735,z4,z6]),(0,[z59,z2,z3,z4,z62,z6]),(0,[z35,z0,z78,z112,z1,z6]),(0,[z0,z290,z113,z3,z4,z6])],[(0,[z0,z2,z3,z736,z4,z6]),(0,[z0,z737,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z738,z6]),(0,[z241,z160,z60,z3,z4,z6]),(0,[z59,z1,z113,z3,z4,z6]),(0,[z0,z1,z2,z3,z739,z6]),(0,[z0,z1,z3,z4,z740,z6]),(0,[z0,z9,z1,z2,z4,z108])],[(0,[z0,z1,z198,z3,z4,z6]),(0,[z0,z1,z2,z3,z741,z4]),(0,[z1,z2,z3,z742,z21,z6])]],
   [[(0,[z0,z2,z242,z603,z4,z6]),(0,[z0,z1,z2,z3,z4,z743]),(0,[z0,z2,z3,z4,z744,z6]),(0,[z0,z45,z1,z2,z210,z4]),(0,[z0,z235,z2,z3,z10,z6])],[(0,[z0,z2,z3,z4,z745,z6]),(0,[z9,z125,z1,z2,z28,z4]),(0,[z746,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z747])],[(0,[z0,z1,z2,z210,z4,z6]),(0,[z0,z9,z1,z2,z3,z255]),(0,[z0,z1,z2,z3,z4,z25])],[(0,[z0,z1,z748,z3,z4,z6]),(0,[z0,z1,z749,z3,z4,z6]),(0,[z0,z185,z2,z3,z750,z6]),(0,[z0,z1,z2,z3,z4,z599]),(0,[z179,z1,z2,z3,z21,z6]),(0,[z0,z324,z2,z3,z4,z751]),(0,[z0,z1,z2,z3,z4,z752]),(0,[z0,z669,z2,z3,z62,z6]),(0,[z0,z386,z1,z2,z4,z96]),(0,[z0,z9,z1,z3,z4,z418])],[(0,[z0,z1,z2,z3,z4,z216]),(0,[z0,z345,z9,z2,z71,z4]),(0,[z0,z1,z2,z3,z753,z6]),(0,[z0,z754,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z755]),(0,[z0,z1,z2,z756,z3,z4]),(0,[z0,z1,z2,z178,z3,z514]),(0,[z179,z9,z1,z2,z3,z21]),(0,[z0,z1,z2,z14,z210,z4]),(0,[z0,z1,z2,z4,z6,z757]),(0,[z0,z1,z2,z758,z3,z4]),(0,[z0,z1,z2,z725,z132,z6])],[(0,[z0,z1,z16,z3,z4,z6]),(0,[z759,z0,z2,z3,z4,z6]),(0,[z760,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z4,z761,z6]),(0,[z0,z1,z2,z3,z4,z751]),(0,[z0,z1,z2,z3,z4,z762])]],
   [[(0,[z0,z345,z2,z603,z4,z6]),(0,[z83,z552,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z763]),(0,[z0,z1,z2,z14,z3,z764])],[(0,[z0,z765,z1,z2,z603,z4]),(0,[z0,z2,z3,z370,z62,z6]),(0,[z0,z146,z1,z178,z3,z4]),(0,[z0,z9,z1,z2,z4,z137]),(0,[z0,z1,z36,z2,z473,z4]),(0,[z0,z1,z2,z191,z3,z219]),(0,[z0,z9,z1,z2,z14,z4])],[(0,[z0,z46,z16,z3,z4,z6]),(0,[z19,z766,z2,z3,z4,z6]),(0,[z0,z1,z2,z178,z247,z4]),(0,[z179,z1,z2,z3,z43,z21]),(0,[z147,z1,z2,z3,z318,z4]),(0,[z0,z271,z2,z3,z62,z6]),(0,[z0,z78,z9,z1,z56,z4]),(0,[z0,z112,z161,z3,z170,z6]),(0,[z0,z1,z2,z3,z4,z767])],[(0,[z0,z236,z1,z2,z3,z4]),(0,[z0,z768,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z148,z461]),(0,[z0,z1,z2,z769,z3,z4]),(0,[z0,z189,z770,z3,z4,z6]),(0,[z0,z78,z9,z1,z37,z4])],[(0,[z0,z771,z2,z3,z4,z6]),(0,[z44,z0,z386,z1,z2,z4]),(0,[z0,z1,z2,z210,z49,z4]),(0,[z0,z241,z60,z14,z3,z4]),(0,[z0,z20,z2,z3,z259,z6]),(0,[z0,z2,z3,z4,z772,z6])],[(0,[z179,z1,z2,z3,z742,z6]),(0,[z0,z189,z528,z3,z4,z6]),(0,[z0,z86,z87,z242,z4,z6]),(0,[z0,z26,z2,z3,z4,z69]),(0,[z0,z290,z2,z89,z3,z6])],[(0,[z0,z1,z2,z773,z603,z4]),(0,[z0,z324,z2,z14,z3,z4]),(0,[z59,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z774,z3,z4]),(0,[z0,z1,z2,z3,z250,z6]),(0,[z0,z1,z2,z3,z4,z775]),(0,[z0,z2,z3,z4,z776,z6]),(0,[z0,z9,z1,z2,z47,z4]),(0,[z777,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z198,z3,z4,z527]),(0,[z0,z1,z2,z3,z4,z41]),(0,[z0,z778,z2,z3,z4,z6]),(0,[z0,z779,z1,z2,z4,z6])],[(0,[z0,z1,z2,z3,z4,z780]),(0,[z0,z1,z2,z781,z4,z6]),(0,[z0,z1,z2,z3,z4,z782]),(0,[z70,z1,z416,z71,z4,z6]),(0,[z0,z1,z2,z3,z4,z783]),(0,[z0,z1,z2,z3,z742,z6]),(0,[z0,z1,z770,z3,z4,z6]),(0,[z0,z2,z784,z66,z4,z6]),(0,[z1,z2,z3,z4,z6,z785])],[(0,[z0,z1,z198,z603,z4,z6]),(0,[z0,z1,z2,z3,z786,z6]),(0,[z15,z559,z2,z3,z4,z6]),(0,[z0,z787,z1,z2,z3,z4]),(0,[z0,z9,z1,z2,z71,z4]),(0,[z0,z9,z2,z124,z3,z4]),(0,[z0,z1,z2,z3,z4,z788]),(0,[z0,z1,z789,z3,z4,z6]),(0,[z0,z1,z2,z3,z219,z6]),(0,[z0,z268,z9,z1,z2,z3]),(0,[z0,z1,z2,z3,z4,z263]),(0,[z0,z1,z2,z4,z6,z790]),(0,[z0,z1,z2,z3,z4,z791])],[(0,[z0,z1,z2,z14,z3,z4]),(0,[z19,z2,z3,z4,z553,z6]),(0,[z0,z146,z124,z3,z4,z6]),(0,[z405,z1,z2,z71,z4,z6]),(0,[z0,z792,z1,z2,z3,z4]),(0,[z0,z86,z2,z242,z109,z6]),(0,[z793,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z794,z6]),(0,[z0,z1,z2,z3,z4,z795])],[(0,[z0,z46,z770,z3,z4,z6]),(0,[z0,z9,z189,z46,z3,z4]),(0,[z0,z86,z2,z242,z4,z6])],[(0,[z0,z1,z2,z603,z4,z6]),(0,[z1,z2,z3,z11,z742,z6]),(0,[z44,z125,z1,z2,z3,z4]),(0,[z35,z0,z1,z2,z609,z6]),(0,[z0,z215,z2,z3,z4,z96]),(0,[z0,z9,z1,z2,z3,z545]),(0,[z0,z112,z1,z14,z3,z170])],[(0,[z0,z1,z16,z3,z4,z527]),(0,[z0,z185,z2,z3,z4,z6]),(0,[z796,z0,z1,z2,z3,z6]),(0,[z1,z749,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z797]),(0,[z0,z798,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z799]),(0,[z0,z236,z1,z2,z3,z514]),(0,[z152,z1,z2,z3,z742,z6]),(0,[z0,z377,z60,z3,z4,z6]),(0,[z0,z1,z115,z3,z4,z153]),(0,[z800,z9,z1,z2,z3,z4]),(0,[z0,z45,z1,z2,z3,z213])]],
   [[(0,[z0,z1,z2,z3,z4,z801]),(0,[z0,z1,z2,z3,z6,z802]),(0,[z0,z1,z2,z210,z4,z188]),(0,[z59,z241,z60,z3,z4,z6])],[(0,[z0,z1,z16,z603,z4,z6]),(0,[z0,z1,z3,z4,z803,z6]),(0,[z0,z1,z2,z3,z4,z804])],[(0,[z0,z1,z805,z3,z4,z6]),(0,[z0,z1,z806,z3,z4,z6]),(0,[z0,z1,z2,z807,z4,z6]),(0,[z0,z9,z1,z2,z28,z4]),(0,[z0,z1,z2,z808,z3,z4]),(0,[z0,z1,z2,z3,z4,z809]),(0,[z0,z1,z2,z3,z49,z453])],[(0,[z0,z65,z2,z603,z4,z6]),(0,[z0,z1,z2,z3,z4,z810]),(0,[z0,z811,z1,z2,z4,z6]),(0,[z302,z0,z345,z2,z3,z6]),(0,[z0,z241,z60,z3,z148,z6]),(0,[z0,z812,z1,z2,z3,z6]),(0,[z0,z1,z3,z813,z4,z6]),(0,[z0,z1,z2,z814,z3,z4]),(0,[z0,z1,z3,z4,z815,z6]),(0,[z0,z193,z9,z1,z3,z4]),(0,[z0,z493,z1,z56,z3,z4])],[(0,[z0,z1,z2,z3,z816,z6]),(1,[z0,z817,z1,z2,z4]),(0,[z0,z189,z2,z3,z148,z6]),(0,[z0,z1,z2,z3,z495,z69]),(0,[z0,z1,z2,z4,z122,z252]),(0,[z0,z1,z36,z4,z592,z6]),(0,[z0,z1,z48,z3,z37,z6])],[(0,[z0,z1,z2,z818,z3,z4]),(0,[z0,z9,z1,z616,z2,z4]),(0,[z660,z1,z2,z3,z11,z6]),(0,[z0,z290,z2,z3,z4,z6]),(0,[z819,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z4,z6,z791])],[(0,[z59,z1,z2,z3,z4,z6]),(0,[z0,z1,z820,z3,z4,z6]),(0,[z83,z0,z78,z9,z1,z4]),(0,[z0,z2,z124,z3,z514,z6]),(0,[z0,z1,z2,z821,z3,z4]),(0,[z0,z78,z9,z1,z36,z4]),(0,[z0,z1,z2,z813,z4,z6]),(0,[z0,z268,z1,z36,z2,z6])],[(0,[z0,z1,z2,z3,z4,z822]),(0,[z0,z1,z2,z14,z3,z514]),(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z1,z2,z4,z253,z252]),(0,[z0,z193,z483,z1,z3,z4]),(0,[z0,z9,z1,z2,z4,z63])]],
   [[(0,[z0,z1,z499,z3,z4,z55]),(0,[z0,z1,z2,z14,z4,z443]),(0,[z0,z824,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z94,z4])],[(0,[z0,z78,z1,z550,z4,z6]),(0,[z0,z825,z2,z3,z4,z6]),(0,[z0,z1,z2,z826,z3,z4]),(0,[z0,z1,z2,z3,z148,z6]),(0,[z0,z304,z1,z141,z3,z55])],[(0,[z0,z65,z9,z2,z66,z4]),(0,[z0,z1,z3,z37,z23,z6]),(0,[z0,z9,z304,z1,z2,z3])],[(0,[z0,z2,z3,z4,z827,z6]),(0,[z0,z146,z1,z14,z3,z4]),(0,[z0,z1,z2,z828,z4,z6]),(0,[z0,z1,z2,z829,z3,z4]),(0,[z0,z1,z2,z79,z725,z6])],[(0,[z0,z1,z2,z3,z6,z830]),(0,[z0,z1,z831,z3,z4,z6]),(0,[z147,z1,z2,z3,z4,z52]),(0,[z0,z1,z2,z3,z832,z4]),(0,[z95,z0,z2,z3,z495,z69]),(0,[z53,z0,z386,z1,z2,z4])],[(0,[z0,z1,z833,z3,z4,z6]),(0,[z834,z1,z2,z3,z4,z6]),(0,[z0,z1,z835,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z22])],[(0,[z0,z1,z2,z3,z836,z6]),(0,[z0,z241,z60,z3,z4,z64]),(0,[z0,z1,z3,z4,z6,z837]),(0,[z0,z386,z1,z141,z2,z4]),(0,[z0,z1,z2,z3,z4,z838]),(0,[z800,z1,z2,z3,z4,z6])],[(0,[z0,z1,z198,z3,z301,z6]),(0,[z0,z1,z2,z603,z4,z527]),(0,[z0,z9,z1,z2,z603,z4]),(0,[z83,z1,z186,z14,z3,z4]),(0,[z0,z1,z2,z839,z3,z4]),(0,[z0,z1,z2,z3,z4,z840]),(0,[z0,z1,z2,z14,z657,z4]),(0,[z0,z1,z2,z3,z49,z841])]],
   [[(0,[z0,z1,z2,z3,z4,z842]),(0,[z0,z324,z2,z3,z62,z6]),(0,[z0,z324,z2,z3,z4,z843]),(0,[z0,z9,z1,z2,z359,z4]),(0,[z44,z1,z2,z3,z4,z307]),(0,[z0,z1,z2,z3,z844,z4]),(0,[z845,z0,z1,z2,z3,z4]),(0,[z0,z386,z1,z2,z4,z50]),(0,[z0,z9,z1,z2,z89,z79])],[(0,[z0,z846,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z847]),(0,[z0,z848,z1,z2,z3,z4])],[(0,[z0,z9,z1,z2,z514,z71]),(0,[z0,z268,z1,z2,z14,z3]),(0,[z0,z1,z2,z14,z4,z5])],[(0,[z0,z9,z1,z2,z3,z301]),(0,[z302,z0,z1,z416,z3,z6]),(0,[z0,z849,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z495])],[(0,[z0,z1,z2,z120,z4,z460]),(0,[z0,z1,z2,z3,z4,z843]),(0,[z0,z324,z2,z3,z10,z6]),(0,[z0,z1,z2,z3,z4,z64]),(0,[z0,z1,z87,z3,z4,z110]),(0,[z0,z1,z2,z3,z495,z96]),(0,[z0,z850,z2,z3,z4,z6]),(0,[z0,z1,z2,z851,z3,z4]),(0,[z0,z1,z2,z14,z3,z739])],[(0,[z0,z1,z2,z3,z852,z4]),(0,[z59,z1,z40,z3,z4,z6]),(0,[z0,z1,z2,z853,z3,z4])],[(0,[z0,z1,z16,z3,z301,z6]),(0,[z0,z345,z2,z178,z3,z4]),(0,[z0,z854,z1,z3,z4,z6]),(0,[z0,z1,z87,z3,z4,z153]),(0,[z0,z1,z2,z3,z855,z6]),(0,[z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z856,z3,z4,z6]),(0,[z0,z2,z60,z3,z148,z6]),(0,[z0,z45,z1,z2,z3,z472]),(0,[z0,z857,z1,z2,z3,z4])]],
   [[(0,[z0,z146,z9,z1,z4,z6]),(0,[z0,z58,z2,z3,z62,z6]),(0,[z0,z483,z1,z3,z4,z418]),(0,[z0,z9,z858,z2,z3,z4])],[(0,[z0,z9,z1,z115,z3,z4]),(0,[z0,z1,z2,z3,z109,z110]),(0,[z0,z9,z1,z48,z3,z37])],[(1,[z766,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z859])],[(0,[z19,z636,z2,z3,z4,z6]),(0,[z0,z490,z9,z1,z2,z4]),(0,[z0,z146,z1,z4,z122,z6]),(0,[z588,z0,z2,z3,z62,z6]),(0,[z0,z1,z2,z3,z4,z860]),(0,[z0,z1,z2,z3,z4,z110]),(1,[z0,z2,z784,z4,z6]),(0,[z0,z1,z2,z3,z861,z6]),(0,[z0,z111,z2,z14,z3,z62]),(0,[z0,z386,z1,z2,z14,z4]),(0,[z0,z1,z2,z3,z4,z841])],[(0,[z0,z2,z3,z301,z62,z6]),(0,[z1,z766,z2,z3,z4,z6]),(0,[z147,z0,z304,z1,z2,z3]),(0,[z1,z2,z3,z4,z862,z6]),(0,[z0,z1,z115,z3,z250,z6]),(0,[z0,z268,z1,z113,z3,z6])],[(0,[z0,z1,z2,z3,z4,z863]),(0,[z8,z1,z40,z3,z4,z6]),(0,[z0,z1,z2,z864,z3,z4]),(0,[z0,z1,z2,z865,z3,z4]),(0,[z0,z866,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z867,z6]),(0,[z0,z112,z1,z3,z294,z170]),(0,[z0,z386,z1,z2,z255,z6])],[(0,[z0,z9,z1,z16,z3,z4]),(0,[z0,z1,z2,z14,z120,z4]),(0,[z0,z1,z2,z3,z868,z6]),(0,[z0,z2,z3,z4,z869,z6]),(0,[z0,z1,z2,z3,z870,z4]),(0,[z0,z871,z2,z3,z4,z6]),(0,[z0,z1,z2,z784,z4,z6])]],
   [[(0,[z19,z0,z2,z3,z148,z6]),(0,[z0,z1,z872,z3,z4,z6])],[(0,[z0,z1,z2,z4,z873,z6]),(0,[z0,z1,z2,z3,z10,z196]),(0,[z192,z0,z1,z3,z381,z4])],[(0,[z70,z146,z1,z71,z4,z6]),(0,[z147,z1,z2,z3,z4,z874]),(0,[z1,z2,z160,z14,z3,z4]),(0,[z0,z86,z115,z242,z4,z6]),(0,[z0,z1,z3,z4,z875,z6])],[(0,[z0,z1,z2,z3,z4,z876]),(0,[z159,z9,z1,z2,z28,z4]),(0,[z0,z1,z2,z3,z4,z877]),(0,[z878,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z224,z3,z82])],[(0,[z0,z1,z2,z178,z3,z4]),(0,[z0,z65,z2,z784,z4,z6]),(0,[z0,z2,z3,z776,z62,z6]),(0,[z0,z161,z2,z3,z4,z273]),(0,[z0,z1,z2,z879,z3,z4]),(0,[z0,z1,z48,z3,z254,z6]),(0,[z192,z0,z1,z3,z4,z12])],[(0,[z0,z1,z2,z3,z4,z880]),(0,[z0,z1,z2,z473,z3,z219]),(0,[z0,z881,z1,z3,z4,z6]),(0,[z81,z202,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z82,z50])],[(0,[z0,z241,z16,z3,z4,z6]),(0,[z0,z1,z2,z603,z301,z6]),(0,[z0,z135,z1,z2,z14,z4]),(0,[z882,z1,z2,z3,z4,z6]),(0,[z0,z238,z9,z1,z2,z4]),(0,[z35,z0,z1,z2,z694,z6]),(0,[z0,z78,z1,z469,z4,z6]),(0,[z0,z1,z2,z191,z3,z4])],[(0,[z0,z384,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z4,z883]),(0,[z0,z88,z112,z1,z4,z6]),(0,[z0,z9,z1,z2,z471,z4]),(0,[z140,z0,z2,z3,z275,z4])]],
   [[(0,[z0,z1,z544,z113,z4,z6]),(0,[z0,z1,z2,z14,z3,z250]),(0,[z0,z1,z2,z3,z4,z884]),(0,[z95,z0,z2,z3,z545,z69]),(0,[z0,z1,z36,z113,z4,z252]),(0,[z0,z1,z2,z3,z255,z6]),(0,[z0,z1,z2,z14,z4,z791])],[(0,[z0,z1,z2,z3,z4,z885]),(0,[z0,z1,z113,z813,z4,z6])],[(0,[z0,z1,z886,z3,z4,z6]),(0,[z0,z887,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z888]),(0,[z0,z1,z2,z3,z4,z889]),(0,[z0,z1,z890,z2,z3,z4]),(0,[z0,z891,z2,z3,z4,z6]),(0,[z892,z0,z1,z2,z3,z4]),(0,[z0,z648,z384,z2,z3,z4])],[(0,[z70,z1,z2,z727,z4,z6]),(0,[z0,z1,z67,z2,z71,z4]),(0,[z0,z1,z2,z3,z893,z4]),(0,[z0,z894,z9,z1,z2,z3]),(0,[z0,z1,z2,z3,z895,z6])],[(0,[z0,z1,z896,z3,z4,z6]),(0,[z0,z9,z1,z2,z398,z4]),(0,[z0,z1,z2,z3,z4,z897]),(0,[z0,z1,z2,z3,z394,z64]),(0,[z0,z1,z36,z813,z4,z6]),(0,[z0,z88,z9,z1,z2,z4]),(0,[z0,z9,z1,z2,z4,z253])],[(0,[z0,z898,z1,z2,z3,z4]),(0,[z0,z1,z2,z899,z3,z4]),(0,[z0,z1,z2,z3,z900,z6]),(0,[z0,z345,z2,z66,z4,z6]),(0,[z0,z1,z2,z3,z4,z874]),(0,[z0,z1,z2,z901,z3,z4]),(0,[z0,z1,z2,z902,z4,z6]),(0,[z0,z1,z2,z3,z903,z6]),(0,[z0,z86,z2,z242,z4,z110]),(0,[z0,z643,z2,z3,z62,z6]),(1,[z0,z78,z268,z1,z6]),(0,[z0,z1,z13,z3,z4,z55])],[(0,[z0,z1,z2,z904,z4,z6]),(0,[z81,z1,z2,z28,z4,z6]),(0,[z0,z1,z2,z905,z4,z6]),(1,[z0,z2,z3,z4,z772]),(0,[z0,z45,z1,z2,z3,z404]),(0,[z0,z1,z906,z3,z4,z6]),(0,[z0,z894,z1,z2,z3,z6])],[(0,[z15,z417,z2,z3,z4,z6]),(0,[z0,z146,z236,z1,z3,z4]),(0,[z0,z907,z2,z3,z4,z6]),(0,[z0,z1,z519,z3,z4,z12]),(0,[z274,z1,z2,z3,z4,z188]),(0,[z0,z86,z2,z242,z4,z153]),(0,[z0,z20,z2,z3,z10,z22]),(0,[z0,z1,z36,z113,z4,z6]),(0,[z0,z9,z1,z385,z2,z4]),(0,[z0,z112,z290,z3,z170,z6]),(0,[z0,z1,z2,z908,z3,z4]),(0,[z0,z88,z1,z48,z2,z6])]],
   [[(0,[z0,z2,z124,z3,z4,z6]),(0,[z0,z345,z2,z14,z3,z4]),(0,[z0,z9,z86,z2,z242,z4]),(0,[z95,z0,z2,z3,z4,z69]),(0,[z0,z112,z9,z1,z3,z170])],[(0,[z302,z0,z1,z2,z178,z3]),(0,[z0,z1,z2,z3,z4,z909]),(0,[z0,z241,z770,z3,z4,z6]),(0,[z0,z2,z3,z10,z776,z6]),(0,[z0,z45,z1,z2,z3,z263]),(1,[z0,z1,z2,z4,z791]),(0,[z0,z1,z2,z14,z3,z903])],[(0,[z766,z245,z2,z3,z4,z6]),(0,[z15,z364,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z910,z6]),(0,[z0,z9,z1,z2,z564,z4]),(0,[z0,z1,z2,z3,z4,z911]),(0,[z0,z189,z46,z3,z4,z6]),(0,[z912,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z913,z3,z4]),(0,[z0,z1,z2,z3,z4,z772]),(0,[z0,z9,z1,z36,z113,z4]),(1,[z0,z1,z3,z4,z815]),(0,[z878,z1,z2,z3,z4,z6])],[(0,[z15,z245,z2,z3,z358,z6]),(0,[z1,z749,z186,z3,z4,z6]),(0,[z0,z1,z67,z2,z28,z4]),(0,[z0,z1,z2,z3,z914,z6]),(0,[z0,z1,z87,z3,z250,z6]),(0,[z0,z1,z2,z3,z915,z6]),(0,[z0,z88,z1,z2,z62,z6]),(0,[z0,z1,z2,z3,z916,z6])],[(0,[z0,z1,z2,z917,z4,z6]),(0,[z0,z1,z2,z3,z4,z918]),(0,[z0,z9,z1,z2,z4,z512]),(0,[z274,z1,z2,z261,z3,z4])],[(0,[z0,z1,z2,z3,z4,z919]),(0,[z44,z0,z304,z1,z2,z3]),(0,[z147,z1,z2,z247,z4,z52]),(0,[z0,z88,z112,z1,z3,z6]),(1,[z0,z1,z2,z725,z6]),(0,[z0,z1,z2,z3,z719,z6])],[(0,[z84,z1,z40,z3,z4,z6]),(0,[z70,z236,z1,z2,z71,z4]),(0,[z0,z770,z60,z3,z4,z6]),(0,[z0,z1,z920,z3,z4,z6]),(0,[z0,z112,z1,z339,z3,z6])],[(0,[z0,z1,z2,z3,z358,z460]),(0,[z0,z921,z2,z3,z4,z6]),(0,[z152,z1,z2,z14,z3,z11]),(0,[z0,z1,z87,z14,z3,z4]),(0,[z0,z1,z36,z2,z922,z4])]],
   [[(0,[z0,z923,z1,z2,z3,z4]),(1,[z1,z2,z3,z4,z874])],[(1,[z1,z749,z3,z4,z6]),(0,[z0,z924,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z925]),(0,[z0,z9,z1,z2,z4,z354])],[(0,[z0,z1,z198,z14,z3,z4]),(0,[z59,z1,z186,z3,z4,z6]),(0,[z0,z9,z1,z532,z2,z4]),(0,[z0,z1,z2,z3,z49,z666]),(0,[z0,z9,z1,z2,z3,z394])],[(0,[z0,z1,z2,z3,z926,z6]),(0,[z0,z927,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z928]),(0,[z0,z1,z929,z3,z4,z6]),(0,[z44,z1,z2,z3,z4,z874]),(0,[z0,z1,z2,z3,z930,z6]),(0,[z0,z215,z2,z3,z4,z772])],[(0,[z83,z91,z186,z3,z4,z6]),(0,[z0,z9,z1,z2,z353,z4]),(0,[z0,z20,z2,z14,z3,z10]),(0,[z35,z0,z193,z1,z4,z6]),(0,[z746,z1,z2,z14,z3,z4])],[(0,[z0,z146,z9,z1,z3,z4]),(0,[z302,z0,z236,z1,z2,z3]),(0,[z0,z258,z1,z2,z3,z4]),(0,[z0,z498,z1,z3,z4,z12]),(0,[z0,z552,z9,z1,z2,z4]),(0,[z0,z386,z1,z141,z4,z55])],[(0,[z0,z1,z198,z120,z4,z6]),(0,[z70,z1,z2,z14,z71,z4]),(0,[z59,z241,z2,z3,z4,z6]),(0,[z0,z78,z9,z1,z60,z4]),(0,[z0,z9,z1,z2,z591,z4]),(0,[z0,z1,z2,z3,z4,z931]),(0,[z0,z1,z2,z3,z841,z50])],[(0,[z0,z1,z932,z2,z3,z4]),(0,[z0,z2,z3,z4,z933,z6]),(0,[z0,z9,z1,z2,z4,z180]),(0,[z0,z1,z934,z3,z4,z6]),(0,[z0,z1,z36,z4,z33,z6])]],
   [[(0,[z0,z1,z2,z3,z935,z6]),(0,[z0,z65,z2,z66,z4,z6]),(0,[z0,z1,z115,z3,z4,z110]),(0,[z0,z1,z2,z3,z4,z936]),(0,[z0,z268,z1,z2,z3,z6]),(0,[z0,z9,z1,z2,z4,z372])],[(0,[z0,z1,z16,z14,z3,z4]),(0,[z0,z1,z2,z3,z4,z709]),(0,[z0,z937,z1,z2,z3,z6]),(0,[z0,z938,z1,z2,z3,z4]),(0,[z0,z1,z2,z14,z414,z4]),(0,[z0,z1,z2,z3,z725,z6])],[(0,[z0,z1,z2,z120,z4,z6]),(0,[z38,z766,z2,z3,z4,z6]),(0,[z0,z78,z9,z1,z46,z4]),(0,[z0,z2,z3,z4,z772,z96]),(0,[z0,z1,z2,z3,z4,z273]),(0,[z0,z1,z2,z939,z4,z6])],[(0,[z0,z1,z2,z3,z4,z940]),(0,[z0,z597,z206,z2,z3,z4])],[(0,[z19,z38,z2,z3,z4,z6]),(0,[z0,z88,z1,z2,z14,z4])],[(0,[z0,z185,z16,z3,z4,z6]),(0,[z0,z1,z16,z120,z4,z6]),(0,[z0,z1,z2,z941,z3,z4]),(0,[z0,z2,z770,z3,z4,z6])],[(0,[z0,z1,z942,z3,z4,z6]),(0,[z0,z9,z1,z2,z411,z4]),(0,[z0,z1,z3,z4,z943,z6]),(0,[z0,z1,z2,z94,z3,z10])],[(0,[z0,z2,z3,z944,z4,z6]),(0,[z70,z345,z2,z71,z4,z6]),(1,[z1,z2,z3,z742,z6]),(0,[z0,z112,z1,z3,z694,z6])]],
   [[(0,[z15,z245,z2,z3,z4,z460]),(0,[z0,z345,z9,z2,z3,z4]),(0,[z44,z613,z1,z2,z3,z4]),(0,[z0,z111,z2,z3,z776,z6]),(0,[z0,z368,z1,z2,z14,z4])],[(0,[z0,z1,z945,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z946]),(0,[z0,z1,z2,z727,z4,z6]),(0,[z0,z1,z2,z89,z312,z6]),(0,[z947,z1,z2,z3,z4,z6]),(0,[z0,z1,z36,z2,z4,z182]),(0,[z0,z1,z48,z14,z3,z37]),(0,[z0,z1,z2,z14,z639,z4])],[(0,[z0,z2,z242,z54,z4,z6]),(0,[z0,z1,z2,z3,z4,z948]),(0,[z0,z9,z1,z2,z4,z393]),(0,[z0,z9,z1,z2,z491,z4]),(0,[z0,z241,z60,z3,z4,z461]),(0,[z949,z1,z2,z3,z4,z6]),(0,[z0,z78,z1,z2,z473,z4]),(0,[z0,z950,z2,z3,z4,z6]),(0,[z35,z0,z193,z1,z3,z6])],[(0,[z0,z1,z2,z951,z4,z6]),(0,[z302,z0,z9,z1,z2,z3]),(0,[z179,z524,z1,z2,z3,z6]),(0,[z0,z1,z2,z4,z5,z715])],[(0,[z59,z1,z16,z3,z4,z6]),(0,[z0,z1,z416,z3,z4,z6]),(0,[z0,z86,z2,z242,z250,z6]),(0,[z0,z2,z242,z784,z4,z6]),(0,[z0,z1,z141,z3,z4,z55]),(0,[z0,z1,z2,z14,z3,z255])],[(0,[z59,z46,z2,z3,z4,z6]),(0,[z0,z86,z2,z784,z4,z6])],[(0,[z0,z952,z2,z3,z4,z6]),(0,[z302,z0,z1,z2,z3,z6])],[(0,[z0,z1,z953,z3,z4,z6]),(0,[z179,z1,z2,z14,z3,z21]),(0,[z0,z1,z954,z3,z4,z6]),(0,[z0,z112,z1,z3,z955,z6])]],
   [[(0,[z0,z78,z268,z1,z4,z6]),(0,[z0,z112,z1,z3,z170,z273]),(0,[z0,z1,z2,z3,z4,z956])],[(0,[z0,z898,z1,z2,z120,z4]),(0,[z8,z1,z749,z3,z4,z6]),(0,[z0,z817,z1,z40,z2,z4]),(0,[z957,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z958,z4,z6]),(0,[z0,z1,z2,z959,z4,z6]),(0,[z0,z1,z2,z960,z4,z6]),(0,[z0,z1,z2,z3,z4,z482]),(0,[z0,z1,z2,z4,z253,z6]),(0,[z0,z1,z2,z961,z4,z6]),(0,[z0,z45,z1,z2,z3,z50])],[(0,[z0,z1,z2,z962,z120,z4]),(0,[z0,z9,z1,z2,z3,z358]),(0,[z0,z2,z963,z3,z4,z6]),(0,[z0,z9,z1,z2,z826,z4]),(0,[z0,z1,z2,z3,z964,z6]),(0,[z0,z1,z48,z3,z504,z6]),(0,[z0,z45,z1,z2,z3,z841])],[(0,[z0,z1,z2,z120,z4,z527]),(0,[z0,z1,z965,z3,z4,z6]),(0,[z0,z1,z2,z3,z966,z6]),(0,[z1,z2,z967,z3,z4,z6])],[(0,[z0,z968,z1,z2,z3,z4]),(0,[z0,z236,z2,z124,z3,z4])],[(0,[z70,z1,z2,z71,z4,z6]),(0,[z0,z9,z1,z2,z371,z4]),(0,[z0,z1,z969,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z970]),(0,[z0,z9,z290,z2,z3,z4]),(0,[z0,z9,z1,z971,z3,z4]),(0,[z0,z276,z2,z204,z3,z4])],[(0,[z302,z0,z9,z1,z2,z71]),(0,[z0,z1,z2,z94,z3,z62]),(0,[z0,z1,z2,z972,z3,z4])],[(0,[z15,z333,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z973,z6]),(0,[z1,z2,z974,z3,z4,z6]),(0,[z0,z1,z975,z2,z3,z4]),(0,[z0,z290,z2,z3,z4,z263]),(0,[z0,z976,z1,z2,z3,z4]),(0,[z0,z88,z112,z1,z2,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z977]),(0,[z0,z1,z2,z3,z4,z978]),(0,[z0,z9,z1,z2,z4,z467]),(0,[z0,z268,z1,z2,z191,z3])],[(0,[z0,z979,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z980,z6]),(0,[z0,z440,z2,z3,z4,z69]),(0,[z0,z1,z36,z14,z113,z4]),(0,[z0,z9,z1,z2,z516,z4])],[(0,[z0,z1,z2,z3,z981,z6]),(0,[z0,z1,z2,z982,z4,z6]),(0,[z0,z1,z2,z3,z983,z6]),(0,[z0,z1,z2,z3,z984,z6]),(0,[z0,z1,z2,z473,z3,z4]),(1,[z0,z1,z3,z955,z6]),(0,[z192,z0,z386,z1,z2,z4])],[(0,[z0,z9,z2,z124,z71,z4]),(0,[z0,z1,z2,z985,z3,z4]),(0,[z0,z1,z986,z2,z3,z4]),(0,[z0,z1,z2,z294,z4,z5]),(0,[z0,z2,z987,z3,z4,z6])],[(0,[z0,z988,z1,z2,z3,z6]),(0,[z147,z1,z2,z3,z4,z445]),(0,[z0,z1,z2,z3,z4,z989])],[(0,[z19,z2,z633,z3,z4,z6]),(0,[z0,z990,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z122,z791])],[(0,[z0,z1,z2,z3,z4,z991]),(0,[z0,z9,z1,z416,z3,z4]),(0,[z0,z1,z2,z89,z467,z6]),(0,[z0,z1,z2,z992,z4,z6]),(0,[z53,z0,z9,z1,z2,z4]),(0,[z0,z1,z2,z3,z294,z4]),(0,[z0,z1,z2,z3,z4,z993]),(0,[z994,z0,z1,z2,z3,z4]),(0,[z0,z1,z13,z256,z3,z4])],[(0,[z0,z1,z2,z3,z995,z6]),(0,[z0,z146,z9,z1,z2,z4]),(0,[z0,z2,z477,z3,z62,z6]),(0,[z0,z9,z1,z36,z2,z4]),(0,[z0,z1,z141,z314,z3,z4])]],
   [[(0,[z0,z9,z91,z2,z3,z4]),(0,[z0,z1,z3,z4,z996,z6]),(0,[z0,z1,z2,z3,z4,z997]),(0,[z0,z1,z2,z210,z4,z55]),(0,[z0,z1,z2,z14,z3,z148]),(0,[z0,z1,z2,z14,z3,z545]),(1,[z0,z88,z112,z1,z6]),(0,[z0,z1,z2,z89,z79,z6]),(1,[z0,z1,z2,z3,z841])],[(0,[z0,z324,z2,z3,z4,z6]),(0,[z8,z1,z40,z3,z4,z216]),(0,[z0,z1,z2,z3,z998,z4]),(0,[z0,z78,z1,z106,z4,z6]),(0,[z0,z78,z112,z9,z1,z4]),(0,[z0,z112,z1,z646,z3,z6])],[(0,[z0,z1,z2,z3,z4,z999]),(0,[z0,z1000,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z1001,z6]),(0,[z0,z1,z2,z1002,z4,z6]),(0,[z1003,z1,z2,z14,z3,z4])],[(0,[z0,z9,z1,z198,z3,z4]),(0,[z302,z0,z1,z2,z14,z3]),(0,[z1004,z1,z2,z3,z4,z6]),(0,[z0,z1,z115,z14,z3,z4]),(0,[z0,z2,z3,z4,z69,z772]),(0,[z0,z1,z14,z3,z4,z418]),(0,[z0,z9,z1,z2,z315,z4])],[(0,[z0,z1,z2,z1005,z3,z4]),(0,[z0,z9,z324,z2,z3,z4]),(0,[z0,z9,z1,z2,z3,z219])],[(0,[z0,z1,z2,z3,z358,z6]),(0,[z0,z1,z1006,z3,z4,z6]),(0,[z0,z1,z416,z3,z514,z6]),(0,[z0,z9,z20,z2,z3,z10])],[(0,[z0,z2,z178,z124,z3,z4]),(0,[z0,z1,z2,z3,z1007,z6])],[(0,[z1,z40,z16,z3,z4,z6]),(0,[z70,z1,z2,z178,z71,z4]),(0,[z0,z1,z2,z3,z4,z1008]),(0,[z0,z9,z1,z2,z247,z4]),(0,[z0,z547,z60,z3,z4,z6])]],
   [[(0,[z15,z537,z2,z3,z4,z6]),(0,[z0,z9,z2,z3,z4,z297]),(0,[z0,z1,z2,z3,z394,z461]),(0,[z0,z511,z46,z3,z4,z6]),(0,[z0,z2,z3,z784,z4,z6]),(0,[z0,z1,z1009,z3,z4,z6]),(0,[z0,z78,z1,z191,z181,z4])],[(0,[z0,z1,z2,z1010,z4,z6]),(0,[z0,z9,z1,z2,z165,z4]),(0,[z0,z1,z1011,z3,z4,z6]),(0,[z0,z9,z1,z87,z3,z4]),(0,[z0,z1,z2,z14,z3,z109]),(0,[z0,z45,z1,z2,z3,z656]),(0,[z0,z1,z2,z89,z79,z513])],[(0,[z0,z1,z2,z120,z301,z6]),(0,[z0,z1,z3,z1012,z4,z6]),(0,[z0,z2,z3,z4,z297,z6]),(0,[z0,z1,z2,z826,z71,z4]),(0,[z147,z1,z2,z162,z3,z4]),(0,[z0,z1,z2,z3,z4,z1013]),(0,[z0,z1,z2,z3,z250,z110]),(0,[z0,z112,z1,z674,z3,z6]),(0,[z0,z304,z1,z2,z3,z6])],[(0,[z0,z91,z2,z3,z4,z6]),(0,[z302,z0,z146,z1,z3,z6]),(0,[z0,z1,z48,z3,z955,z6]),(0,[z0,z304,z1,z2,z3,z24]),(0,[z0,z1,z2,z4,z725,z6])],[(0,[z0,z1,z2,z3,z1014,z4]),(0,[z0,z1,z2,z3,z1015,z6]),(0,[z0,z1,z2,z3,z250,z153]),(0,[z0,z26,z2,z3,z10,z6]),(0,[z0,z1016,z2,z3,z4,z6]),(0,[z0,z290,z2,z3,z170,z6]),(0,[z0,z1017,z2,z3,z4,z6])],[(0,[z8,z1,z40,z3,z4,z41]),(0,[z8,z9,z1,z40,z3,z4]),(0,[z0,z1,z1018,z3,z4,z6]),(0,[z0,z9,z1,z2,z4,z252]),(0,[z0,z1,z2,z1019,z3,z4]),(0,[z35,z0,z1,z418,z132,z6])],[(0,[z0,z1,z2,z3,z4,z1020]),(0,[z0,z1021,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z196])],[(0,[z0,z1,z2,z3,z4,z1022]),(0,[z76,z1,z2,z71,z4,z6]),(0,[z81,z9,z1,z2,z28,z4]),(0,[z0,z1,z1023,z3,z4,z6]),(0,[z0,z1,z1024,z2,z3,z4]),(0,[z0,z193,z1,z89,z3,z6]),(0,[z0,z9,z1,z2,z494,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z1025])],[(0,[z0,z1,z2,z962,z3,z4]),(0,[z0,z1,z113,z239,z4,z6]),(0,[z0,z1,z2,z4,z873,z41])],[(0,[z0,z1,z2,z261,z210,z4]),(0,[z1,z2,z3,z4,z52,z874]),(0,[z0,z304,z1,z141,z2,z3])],[(0,[z0,z416,z124,z3,z4,z6]),(0,[z1,z2,z3,z4,z1026,z6]),(0,[z0,z1,z2,z3,z4,z1027]),(0,[z0,z1,z2,z3,z102,z24])],[(0,[z0,z1,z2,z3,z1028,z4]),(0,[z0,z2,z14,z124,z3,z4]),(0,[z0,z1,z2,z1029,z3,z4])],[(0,[z0,z1,z2,z14,z3,z301]),(0,[z0,z1,z2,z3,z4,z1030]),(0,[z0,z146,z1,z3,z4,z6]),(0,[z1031,z1,z2,z3,z4,z6])],[(0,[z15,z245,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z358,z527]),(0,[z0,z1,z2,z3,z1032,z6]),(0,[z0,z185,z2,z3,z868,z6]),(0,[z0,z1,z2,z3,z1033,z6]),(0,[z0,z1,z1034,z3,z4,z6]),(0,[z0,z111,z9,z2,z3,z62]),(0,[z0,z268,z1,z2,z473,z3]),(0,[z0,z1,z2,z3,z6,z1035])],[(0,[z0,z1,z2,z3,z1036,z6]),(0,[z0,z1,z2,z3,z1037,z6]),(0,[z0,z9,z1,z2,z4,z331]),(0,[z0,z241,z60,z3,z394,z6]),(0,[z1,z2,z3,z4,z1038,z6]),(0,[z0,z386,z304,z1,z2,z6])]],
   [[(0,[z0,z1,z2,z603,z358,z6]),(0,[z0,z1,z2,z1039,z4,z6]),(0,[z0,z112,z1,z2,z94,z3])],[(0,[z0,z1,z2,z3,z1040,z6]),(0,[z83,z1,z186,z3,z4,z6]),(0,[z116,z1,z2,z3,z21,z6]),(0,[z152,z1,z2,z3,z540,z6]),(0,[z0,z20,z2,z3,z776,z6]),(0,[z0,z1,z3,z4,z815,z55]),(0,[z0,z1,z2,z3,z4,z1041])],[(0,[z0,z1,z2,z3,z4,z460]),(0,[z0,z9,z1,z2,z120,z4]),(0,[z0,z9,z1,z2,z426,z4]),(0,[z0,z88,z1,z2,z10,z6]),(0,[z0,z1,z2,z3,z4,z1042])],[(0,[z0,z1,z2,z3,z1043,z6]),(0,[z0,z765,z1,z2,z3,z4]),(0,[z0,z2,z3,z4,z1044,z6]),(0,[z0,z1,z2,z1045,z3,z4]),(0,[z0,z1046,z1,z2,z3,z4]),(0,[z0,z1,z2,z4,z6,z1047]),(1,[z35,z0,z193,z1,z6])],[(0,[z0,z1,z2,z3,z1048,z6]),(0,[z0,z697,z2,z3,z62,z6]),(0,[z0,z1049,z1,z2,z3,z6])],[(0,[z0,z345,z236,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1050]),(0,[z0,z286,z2,z3,z4,z96]),(0,[z0,z1,z2,z3,z394,z6]),(0,[z95,z0,z2,z3,z4,z772]),(0,[z0,z88,z1,z2,z294,z4]),(0,[z0,z1,z2,z3,z257,z24])],[(0,[z0,z1,z2,z3,z1051,z6]),(0,[z0,z1,z2,z3,z514,z6]),(0,[z0,z65,z67,z2,z66,z4]),(0,[z0,z193,z1,z3,z4,z6]),(0,[z0,z112,z1,z5,z170,z6])],[(0,[z185,z40,z2,z3,z4,z6]),(0,[z0,z556,z9,z1,z2,z4]),(0,[z0,z1,z2,z1052,z3,z4]),(0,[z0,z304,z1,z2,z14,z3])]],
   [[(0,[z0,z1,z1053,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1054]),(1,[z0,z2,z3,z776,z6]),(0,[z0,z1,z2,z3,z4,z1055]),(0,[z0,z78,z1,z14,z181,z4]),(0,[z0,z1,z2,z3,z4,z815])],[(0,[z0,z1,z2,z773,z3,z4]),(0,[z0,z345,z416,z3,z4,z6])],[(0,[z0,z1,z2,z1056,z4,z6]),(0,[z0,z20,z2,z3,z301,z6]),(0,[z0,z1057,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1058])],[(0,[z0,z1,z2,z1059,z3,z4]),(0,[z0,z1,z2,z3,z4,z1060]),(0,[z0,z1061,z1,z2,z3,z4])],[(0,[z0,z9,z1,z2,z54,z4]),(0,[z0,z1,z2,z1062,z4,z6]),(0,[z0,z1,z2,z3,z4,z1063]),(0,[z35,z0,z1,z2,z725,z6]),(0,[z760,z1,z2,z14,z3,z4])],[(0,[z159,z1,z2,z14,z28,z4]),(0,[z59,z78,z1,z3,z4,z6]),(0,[z0,z1,z240,z3,z37,z6]),(0,[z0,z78,z1,z813,z4,z6]),(0,[z0,z1,z2,z922,z3,z4]),(0,[z0,z1,z2,z3,z764,z6])],[(0,[z0,z1,z3,z4,z6,z1064]),(0,[z658,z125,z1,z2,z3,z4]),(0,[z0,z107,z1,z314,z3,z4])],[(0,[z15,z245,z2,z3,z4,z527]),(0,[z0,z1,z2,z1065,z4,z6]),(0,[z0,z1,z2,z3,z4,z1066]),(0,[z0,z9,z386,z1,z2,z4])]],
   [[(0,[z83,z1,z749,z3,z4,z6]),(0,[z1067,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1068,z4])],[(0,[z0,z1,z2,z3,z4,z1069]),(0,[z15,z245,z2,z603,z4,z6]),(0,[z0,z324,z2,z3,z301,z6]),(0,[z44,z1,z2,z3,z4,z188]),(0,[z0,z1,z2,z3,z1070,z6])],[(0,[z0,z161,z2,z3,z4,z6]),(0,[z0,z1,z1071,z2,z3,z4]),(0,[z590,z0,z9,z1,z2,z4]),(0,[z0,z1072,z1,z2,z3,z4])],[(0,[z83,z1,z16,z3,z4,z6]),(0,[z0,z9,z1,z2,z210,z4]),(0,[z0,z1,z2,z3,z4,z1073]),(0,[z0,z78,z1,z314,z4,z6]),(0,[z0,z193,z1,z79,z4,z6])],[(0,[z0,z1074,z1,z2,z3,z4]),(0,[z0,z9,z1,z2,z312,z4]),(0,[z0,z1,z2,z3,z4,z1075]),(0,[z0,z1,z2,z3,z1076,z6]),(0,[z0,z241,z9,z60,z3,z4]),(0,[z0,z1,z2,z3,z24,z263])],[(0,[z0,z1,z2,z3,z4,z1077]),(0,[z0,z1,z1078,z3,z4,z6]),(0,[z0,z1,z1079,z3,z4,z6]),(0,[z0,z1,z2,z14,z401,z4])],[(0,[z0,z1,z1080,z2,z3,z4]),(0,[z0,z146,z1,z3,z514,z6]),(0,[z0,z1,z2,z247,z4,z6]),(0,[z0,z1,z3,z4,z1081,z6]),(0,[z0,z1,z2,z3,z4,z1082]),(0,[z0,z1083,z1,z2,z3,z6]),(0,[z0,z88,z112,z1,z170,z6]),(0,[z0,z1,z2,z14,z4,z253]),(0,[z0,z9,z1,z2,z1084,z3])],[(0,[z0,z1,z2,z3,z4,z1085]),(0,[z0,z1,z2,z210,z4,z12])]],
   [[(0,[z0,z1,z1086,z3,z4,z6]),(0,[z0,z1,z2,z1087,z4,z6]),(0,[z0,z1,z2,z3,z1088,z6]),(0,[z0,z1,z2,z3,z1089,z4]),(0,[z0,z1,z1090,z2,z3,z4]),(0,[z0,z1091,z2,z3,z4,z6])],[(0,[z0,z1092,z1,z3,z4,z6]),(0,[z179,z258,z1,z2,z3,z21]),(0,[z147,z1,z2,z210,z4,z52]),(0,[z0,z1,z356,z3,z4,z55])],[(0,[z0,z1,z2,z3,z1093,z6]),(0,[z0,z1,z2,z3,z1094,z6]),(0,[z152,z9,z1,z2,z3,z11]),(0,[z0,z1,z2,z3,z1095,z6])],[(0,[z0,z185,z2,z3,z4,z782]),(0,[z0,z1,z2,z3,z4,z461])],[(0,[z0,z1,z2,z3,z1096,z6]),(0,[z15,z9,z245,z2,z3,z4]),(0,[z0,z1,z2,z3,z750,z6]),(0,[z9,z1,z2,z28,z71,z4]),(1,[z0,z146,z9,z1,z4]),(0,[z0,z1,z2,z3,z1097,z6]),(0,[z0,z65,z2,z174,z66,z4]),(0,[z0,z1,z48,z2,z94,z3])],[(0,[z0,z185,z2,z14,z3,z4]),(0,[z0,z1,z2,z3,z4,z1098]),(0,[z0,z111,z2,z3,z62,z6]),(0,[z0,z1,z2,z3,z299,z24]),(0,[z0,z1,z2,z3,z4,z1099]),(0,[z0,z1,z2,z14,z4,z122])],[(0,[z0,z9,z1,z2,z544,z4]),(0,[z0,z316,z2,z3,z4,z96]),(0,[z0,z1,z2,z1084,z3,z6])],[(1,[z1,z2,z727,z4,z6]),(0,[z70,z302,z1,z2,z71,z6]),(0,[z0,z1,z971,z3,z4,z6])]],
   [[],[(0,[z0,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1100]),(0,[z83,z9,z1,z186,z3,z4]),(0,[z0,z1,z2,z1101,z4,z6]),(0,[z0,z1,z2,z3,z1102,z6]),(0,[z0,z768,z88,z1,z2,z4]),(0,[z0,z1,z2,z89,z79,z182])],[(0,[z0,z1,z2,z3,z4,z1103]),(0,[z0,z614,z2,z242,z4,z6]),(0,[z0,z78,z9,z1,z314,z4]),(0,[z192,z0,z304,z1,z2,z3]),(0,[z192,z0,z1,z3,z4,z815])],[(0,[z0,z1104,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1105]),(0,[z0,z9,z1,z2,z922,z4]),(0,[z0,z290,z2,z14,z3,z4]),(0,[z0,z45,z290,z2,z3,z6])],[(0,[z83,z185,z2,z3,z4,z6]),(0,[z0,z817,z1,z2,z4,z6]),(0,[z1,z2,z3,z4,z874,z188]),(0,[z0,z1,z2,z210,z4,z52]),(0,[z0,z1,z2,z14,z3,z394]),(0,[z59,z1,z2,z14,z3,z4]),(0,[z0,z1106,z1,z3,z4,z6]),(0,[z0,z1,z113,z4,z512,z6]),(0,[z192,z0,z1,z3,z4,z246]),(0,[z0,z1,z2,z3,z4,z1107]),(0,[z0,z1,z2,z14,z4,z521])],[(0,[z1,z40,z114,z3,z4,z6]),(0,[z0,z1,z2,z1108,z3,z4]),(0,[z0,z345,z146,z3,z4,z6]),(0,[z0,z377,z1,z3,z170,z6]),(0,[z0,z1,z2,z3,z1109,z6]),(0,[z0,z1,z1110,z3,z4,z6]),(0,[z0,z1,z2,z3,z49,z24])],[(0,[z0,z1,z2,z3,z4,z1111]),(0,[z15,z245,z2,z3,z301,z6]),(0,[z0,z1,z2,z1112,z3,z4]),(0,[z0,z1,z1113,z3,z4,z6]),(0,[z0,z1114,z2,z3,z4,z6]),(0,[z0,z146,z9,z1,z71,z4]),(0,[z0,z1,z2,z3,z43,z4]),(0,[z0,z1115,z1,z2,z4,z6]),(0,[z0,z215,z206,z2,z3,z4]),(0,[z0,z386,z1,z2,z4,z6]),(0,[z0,z290,z2,z3,z37,z6]),(0,[z0,z1,z2,z4,z5,z1027])],[(0,[z159,z1,z2,z28,z4,z6]),(0,[z70,z1,z2,z514,z71,z6]),(0,[z0,z1,z87,z3,z109,z6]),(0,[z0,z290,z2,z3,z4,z273]),(0,[z0,z386,z1,z2,z4,z24])]],
   [[(0,[z0,z20,z16,z3,z4,z6]),(0,[z0,z1,z2,z1116,z4,z6]),(0,[z0,z1,z2,z1117,z3,z4]),(0,[z0,z1,z2,z3,z545,z6]),(0,[z0,z78,z290,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1118]),(0,[z1,z2,z28,z727,z4,z6]),(0,[z0,z1119,z1,z2,z3,z4]),(0,[z0,z1,z87,z3,z4,z6]),(0,[z1120,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z252]),(0,[z0,z78,z268,z1,z3,z6]),(0,[z0,z1,z2,z3,z24,z567]),(0,[z464,z0,z1,z2,z3,z103])],[(0,[z0,z1,z2,z3,z301,z460]),(0,[z673,z1,z2,z28,z4,z6]),(0,[z0,z241,z60,z3,z4,z6]),(0,[z0,z1,z2,z4,z1121,z6]),(0,[z0,z1122,z1,z2,z3,z4]),(0,[z0,z1,z813,z181,z4,z6]),(0,[z0,z78,z1,z2,z4,z182]),(0,[z0,z1,z2,z3,z4,z1123]),(0,[z0,z1,z2,z4,z791,z63]),(0,[z0,z287,z1,z2,z14,z4])],[(0,[z8,z1,z380,z3,z4,z6]),(0,[z0,z1124,z1,z2,z3,z4])],[(0,[z0,z1,z198,z3,z358,z6]),(0,[z0,z1,z2,z1125,z3,z4]),(0,[z0,z2,z3,z4,z1126,z6]),(0,[z0,z1,z2,z3,z4,z1127]),(0,[z0,z88,z1,z37,z4,z6]),(0,[z0,z1,z2,z1128,z3,z4]),(0,[z449,z0,z45,z1,z2,z3])],[(0,[z0,z1,z2,z3,z1129,z6]),(0,[z0,z9,z1,z2,z3,z514]),(0,[z0,z2,z3,z4,z1130,z6]),(0,[z0,z1131,z1,z3,z4,z6]),(0,[z0,z1,z2,z1132,z3,z4]),(0,[z0,z1133,z2,z3,z4,z6])],[(0,[z0,z16,z3,z4,z62,z6]),(0,[z0,z1,z2,z3,z109,z6]),(0,[z0,z1134,z1,z2,z3,z4]),(0,[z0,z45,z1,z2,z3,z163])],[(0,[z1,z40,z749,z3,z4,z6]),(0,[z1135,z1,z2,z3,z4,z6]),(0,[z0,z1,z1136,z3,z4,z6]),(0,[z0,z304,z1,z2,z3,z69]),(0,[z0,z78,z268,z1,z181,z6]),(0,[z0,z9,z1,z1110,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z955,z6])],[(0,[z0,z1,z2,z1137,z4,z6]),(0,[z15,z766,z2,z3,z4,z6]),(0,[z0,z817,z1,z2,z4,z41]),(0,[z0,z1,z2,z3,z4,z1138]),(0,[z0,z1,z2,z3,z4,z1139]),(0,[z0,z1,z3,z4,z12,z815])],[(0,[z35,z0,z1,z2,z491,z6])],[(0,[z0,z1,z16,z3,z358,z6]),(0,[z0,z1,z1140,z3,z4,z6]),(0,[z0,z1,z2,z71,z4,z72]),(0,[z0,z1,z2,z1141,z3,z4]),(0,[z0,z1,z2,z3,z6,z1142]),(0,[z0,z1,z2,z3,z1143,z6])],[(0,[z0,z1,z2,z4,z1144,z6]),(0,[z0,z1,z2,z3,z4,z1145])],[(0,[z0,z185,z9,z2,z3,z4]),(0,[z159,z1,z2,z727,z4,z6]),(0,[z1,z2,z3,z1146,z4,z6]),(0,[z0,z1,z2,z3,z24,z841])],[(0,[z0,z1147,z1,z3,z4,z6]),(0,[z0,z1148,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z1149,z6]),(0,[z0,z1,z2,z1150,z4,z6]),(0,[z0,z1,z3,z4,z418,z6]),(0,[z0,z1,z141,z3,z4,z815]),(0,[z0,z858,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1151]),(0,[z0,z1,z2,z1152,z4,z6]),(0,[z0,z1,z2,z3,z1153,z6]),(0,[z1,z2,z727,z71,z4,z6]),(0,[z302,z0,z2,z124,z3,z6]),(0,[z0,z1,z2,z3,z4,z1154]),(0,[z0,z65,z2,z14,z66,z4]),(0,[z0,z78,z1,z332,z4,z6]),(0,[z0,z1,z2,z3,z4,z1155]),(0,[z35,z0,z1,z2,z132,z6]),(0,[z35,z0,z193,z1,z2,z6])]],
   [[(0,[z0,z1156,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1157]),(0,[z0,z1,z2,z3,z4,z1158]),(0,[z0,z9,z1,z2,z4,z5]),(0,[z0,z1159,z1,z2,z4,z6]),(0,[z0,z9,z1,z2,z4,z638])],[(0,[z0,z1,z3,z4,z1160,z6]),(0,[z0,z9,z1,z2,z3,z495]),(0,[z0,z1,z2,z3,z4,z513]),(0,[z0,z1,z2,z3,z4,z1161])],[(0,[z0,z1,z2,z3,z4,z1162]),(0,[z0,z1163,z2,z3,z4,z6]),(0,[z1164,z0,z1,z2,z3,z4]),(0,[z152,z2,z3,z11,z297,z6]),(1,[z0,z770,z3,z4,z6]),(0,[z0,z539,z2,z3,z10,z6]),(0,[z0,z78,z9,z1,z181,z4]),(0,[z0,z1,z141,z4,z253,z55])],[(0,[z8,z1,z40,z14,z3,z4]),(0,[z0,z345,z2,z3,z514,z6]),(0,[z0,z1165,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1166]),(0,[z0,z1,z2,z3,z4,z1167]),(0,[z0,z1168,z1,z2,z3,z4])],[(0,[z0,z1,z2,z14,z603,z4]),(0,[z0,z1,z2,z14,z3,z358]),(0,[z0,z1169,z1,z2,z3,z4]),(0,[z0,z1,z2,z14,z190,z4]),(0,[z0,z1,z2,z3,z1170,z6]),(0,[z0,z1,z2,z1171,z3,z4])],[(0,[z15,z245,z198,z3,z4,z6]),(0,[z152,z324,z2,z3,z11,z6]),(0,[z325,z0,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z1172,z6]),(0,[z35,z0,z290,z2,z3,z6]),(0,[z0,z1173,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z89,z79])],[(0,[z0,z1,z2,z1174,z4,z6]),(0,[z0,z1,z2,z28,z4,z72]),(0,[z1,z2,z3,z4,z1175,z6]),(0,[z0,z45,z1,z2,z3,z222]),(0,[z0,z9,z1,z2,z265,z4]),(0,[z0,z112,z1,z3,z170,z6]),(0,[z845,z0,z88,z1,z2,z4])],[(0,[z0,z1,z2,z1176,z4,z6]),(0,[z0,z304,z1,z2,z3,z96]),(0,[z0,z1,z2,z94,z3,z4]),(0,[z0,z1,z3,z4,z6,z1177]),(0,[z0,z9,z1,z2,z3,z895])]],
   [[(0,[z0,z236,z1,z416,z3,z4]),(0,[z0,z1,z2,z3,z148,z64]),(0,[z59,z20,z2,z3,z4,z6]),(1,[z0,z1,z813,z4,z6])],[(0,[z0,z1,z2,z3,z4,z527]),(0,[z0,z1,z198,z3,z4,z460]),(0,[z38,z2,z187,z3,z4,z6]),(0,[z152,z1,z2,z3,z11,z6]),(0,[z0,z1178,z1,z2,z3,z4]),(0,[z0,z520,z2,z3,z4,z96]),(0,[z0,z1,z2,z3,z6,z841])],[(0,[z0,z1,z2,z1179,z4,z6]),(0,[z0,z1,z2,z3,z1180,z6]),(0,[z0,z112,z1,z94,z3,z170]),(0,[z0,z45,z1,z356,z2,z3])],[(0,[z0,z1,z2,z1181,z3,z4]),(0,[z0,z1182,z1,z2,z3,z4]),(0,[z0,z9,z1,z2,z3,z148])],[(0,[z15,z245,z16,z3,z4,z6]),(0,[z0,z1,z2,z120,z358,z6]),(0,[z0,z1,z2,z3,z4,z1183]),(0,[z1,z2,z3,z4,z742,z6]),(0,[z0,z1,z2,z3,z4,z1184]),(0,[z0,z304,z1,z2,z3,z263]),(0,[z0,z1,z3,z955,z170,z6]),(0,[z0,z1,z141,z646,z3,z4])],[(0,[z0,z1185,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1186]),(0,[z0,z1,z2,z3,z4,z1187]),(0,[z0,z1188,z1,z2,z3,z4]),(0,[z0,z78,z1,z339,z4,z6]),(0,[z0,z9,z1,z2,z362,z4]),(0,[z35,z0,z193,z1,z132,z6])],[(0,[z0,z91,z2,z14,z3,z4]),(0,[z0,z1,z2,z178,z4,z122]),(0,[z0,z1189,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1190]),(0,[z35,z0,z1,z2,z25,z132])],[(0,[z0,z9,z1,z2,z239,z4]),(0,[z0,z9,z1,z416,z71,z4]),(0,[z0,z9,z1,z2,z178,z4]),(0,[z0,z1,z2,z3,z1191,z6])]],
   [[(0,[z0,z1,z16,z3,z4,z460]),(0,[z1192,z1,z2,z3,z4,z6]),(0,[z35,z0,z1,z668,z2,z6]),(0,[z0,z193,z1,z3,z4,z25])],[(0,[z0,z185,z60,z3,z4,z6]),(0,[z0,z1,z2,z4,z1193,z6]),(0,[z0,z817,z1,z2,z3,z4]),(0,[z0,z345,z2,z242,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z1194]),(0,[z0,z1,z2,z1195,z3,z4]),(0,[z1196,z1,z2,z3,z4,z6]),(0,[z0,z78,z268,z1,z2,z6]),(0,[z0,z1,z2,z14,z3,z1109])],[(0,[z0,z1,z2,z3,z1197,z6]),(0,[z0,z1,z2,z1198,z3,z4]),(0,[z0,z1,z1199,z3,z4,z6]),(0,[z0,z9,z1,z2,z3,z109]),(0,[z0,z1,z3,z37,z955,z6]),(0,[z143,z1,z2,z162,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1200]),(0,[z0,z1201,z1,z2,z3,z4]),(0,[z0,z112,z1,z3,z170,z263]),(0,[z0,z1,z2,z89,z295,z6])],[(0,[z0,z1,z2,z3,z4,z1202]),(0,[z0,z45,z1,z2,z3,z620]),(0,[z0,z1,z2,z1203,z3,z4]),(0,[z0,z9,z1,z2,z3,z250]),(0,[z0,z1,z2,z14,z3,z219]),(0,[z0,z1204,z2,z3,z4,z6]),(0,[z35,z0,z9,z1,z2,z132]),(0,[z0,z483,z1,z2,z3,z4]),(0,[z0,z9,z1,z2,z4,z791])],[(0,[z0,z1,z2,z3,z4,z1205]),(0,[z81,z1,z2,z3,z4,z52]),(0,[z0,z1,z2,z3,z495,z6]),(0,[z0,z1,z2,z3,z776,z6]),(0,[z0,z88,z1,z2,z4,z6])]],
   [[(0,[z0,z1,z178,z416,z3,z4]),(0,[z9,z1,z2,z160,z3,z4]),(0,[z0,z1206,z1,z2,z4,z6]),(0,[z0,z189,z46,z14,z3,z4]),(0,[z0,z1,z2,z1207,z3,z4]),(0,[z0,z1,z2,z4,z1208,z6]),(0,[z1,z2,z14,z974,z3,z4])],[(0,[z15,z245,z2,z14,z3,z4]),(0,[z1,z2,z3,z4,z874,z6]),(0,[z0,z1,z2,z14,z247,z4])],[(0,[z0,z1,z2,z3,z4,z1209]),(0,[z0,z1210,z1,z2,z3,z4]),(0,[z1211,z0,z1,z2,z3,z6]),(0,[z0,z1,z67,z2,z3,z4]),(0,[z0,z20,z2,z3,z10,z6]),(0,[z35,z0,z483,z1,z2,z132])],[(0,[z0,z1,z115,z3,z109,z6]),(0,[z1212,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z1213,z4,z6]),(0,[z0,z766,z2,z3,z4,z6]),(0,[z0,z1214,z1,z3,z4,z6]),(0,[z0,z9,z1,z468,z2,z4]),(0,[z0,z258,z1,z2,z3,z10]),(0,[z0,z9,z1,z2,z92,z4]),(0,[z1003,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1215]),(0,[z0,z1,z2,z3,z1216,z4]),(0,[z0,z1,z141,z3,z255,z55]),(0,[z0,z9,z1,z13,z2,z4])],[(0,[z15,z245,z2,z120,z4,z6]),(0,[z15,z594,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1217]),(0,[z0,z1,z115,z3,z4,z6]),(0,[z0,z1,z2,z1218,z4,z6]),(0,[z0,z9,z1,z2,z575,z4])],[(0,[z0,z78,z9,z1,z2,z4]),(0,[z0,z1,z2,z3,z4,z1219]),(0,[z0,z1,z2,z94,z4,z5]),(0,[z0,z1,z3,z4,z25,z418])],[(0,[z1,z2,z160,z3,z4,z6]),(0,[z8,z0,z78,z9,z1,z4]),(0,[z0,z1,z2,z3,z1220,z6]),(0,[z0,z1,z2,z3,z4,z1221]),(0,[z0,z1222,z1,z2,z3,z4]),(0,[z0,z1,z3,z4,z955,z6])]],
   [[(0,[z0,z1,z2,z3,z301,z6]),(0,[z0,z1,z2,z603,z4,z460]),(0,[z0,z1,z2,z3,z4,z1223]),(0,[z83,z185,z186,z3,z4,z6])],[(0,[z0,z1224,z1,z2,z3,z4]),(0,[z0,z185,z46,z3,z4,z6]),(0,[z0,z1225,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z1226]),(0,[z0,z621,z9,z1,z2,z4]),(0,[z0,z1,z2,z255,z253,z6]),(0,[z0,z193,z1,z14,z3,z4])],[(0,[z0,z1,z2,z3,z1227,z6]),(0,[z0,z1228,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1229]),(0,[z0,z1,z2,z3,z1230,z6]),(0,[z0,z1231,z1,z3,z4,z6]),(0,[z0,z1232,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z1233,z6]),(0,[z0,z1234,z1,z2,z3,z4]),(0,[z0,z20,z2,z3,z10,z196]),(0,[z0,z1,z2,z3,z4,z1235]),(0,[z35,z0,z1,z2,z469,z6]),(0,[z0,z653,z1,z2,z3,z102]),(0,[z0,z9,z1,z283,z2,z4]),(0,[z53,z0,z1,z3,z381,z4])],[(0,[z0,z1,z2,z3,z4,z1236]),(0,[z0,z9,z1,z2,z550,z4]),(0,[z677,z1,z2,z3,z4,z52]),(0,[z0,z1,z2,z3,z4,z1237]),(0,[z0,z1,z2,z3,z1238,z4])],[(0,[z0,z1,z474,z3,z4,z55]),(0,[z0,z9,z161,z2,z3,z4]),(0,[z0,z1239,z1,z2,z3,z4])],[(0,[z0,z1,z14,z416,z3,z4]),(0,[z0,z1,z2,z3,z4,z1240]),(0,[z0,z1,z2,z3,z1241,z6]),(0,[z0,z1,z2,z3,z4,z1242]),(0,[z0,z9,z1,z2,z651,z4])],[(0,[z0,z1,z2,z1243,z3,z4]),(0,[z15,z0,z2,z3,z148,z6]),(0,[z0,z2,z3,z4,z6,z1244]),(0,[z159,z1,z2,z28,z4,z72]),(0,[z0,z1,z2,z3,z49,z366])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 517) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 517).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1038).take 226) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1264)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [517, 521, 226] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 89).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 89).take 93).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 182).take 74).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [89, 93, 74] = true :=
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

end PEqualNP.Outside.L_meta_38239

theorem PEqualNP.Outside.L_meta_38239 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241856 * 2 ^ 32 + 4007700992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241856 * 2 ^ 32 + 4007700992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38239.solve