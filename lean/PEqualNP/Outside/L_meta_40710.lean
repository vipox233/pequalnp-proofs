import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40710

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
  Nat.testBit (4276808362 * 2 ^ 32 + 4240490624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0010a854af1c630c#64 ++ 0x00042a152bc718c3#64 ++ 0xe031f8ffff1c631e#64 ++ 0xf80c7e3fffc718c7#64 : BitVec 256),
   (0x40c66332600dad74#64 ++ 0x103198cc98036b5d#64 ++ 0xf1ce6732601fffff#64 ++ 0x7c7399cc9807ffff#64 : BitVec 256),
   (0x960b85c3836056b8#64 ++ 0x2582e170e0d815ae#64 ++ 0xfe0f87c387e07fff#64 ++ 0xbf83e1f0e1f81fff#64 : BitVec 256),
   (0x0b7006fc05b683c0#64 ++ 0x42dc01bf016da0f0#64 ++ 0xdff007fc07ff83e3#64 ++ 0xf7fc01ff01ffe0f8#64 : BitVec 256),
   (0x3dbdf80006db7800#64 ++ 0x8f6f7e0001b6de00#64 ++ 0x7ffff80007fffc03#64 ++ 0xdffffe0001ffff00#64 : BitVec 256),
   (0x2fef57ab50000001#64 ++ 0x0bfbd5ead4000000#64 ++ 0xaffffffff8000003#64 ++ 0xebfffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [9, 6]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xe031f8ffff1c631e 0xf80c7e3fffc718c7

def z1 : W := mkw 0x0040023000048140 0x0010008c00012050 0xd1c00730001f83e3 0x747001cc0007e0f8

def z2 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0xaffffffff8000003 0xebfffffffe000000

def z3 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x7ffff80007fffc03 0xdffffe0001ffff00

def z4 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xf1ce6732601fffff 0x7c7399cc9807ffff

def z5 : W := mkw 0x940b810382405438 0x2502e040e090150e 0x200f800380007c1c 0x0803e000e0001f07

def z6 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xfe0f87c387e07fff 0xbf83e1f0e1f81fff

def z7 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xdff007fc07ff83e3 0xf7fc01ff01ffe0f8

def z8 : W := mkw 0x40002010200da944 0x1000080408036a51 0x00000000001f8000 0x000000000007e000

def z9 : W := mkw 0x3dadd00002405000 0x0f6b740000901400 0x7ffff80007e07c03 0xdffffe0001f81f00

def z10 : W := mkw 0x748ff90262497c34 0x9d23fe4098925f0d 0x200ff80260007c1c 0x0803fe0098001f07

def z11 : W := mkw 0x7dfffb3266dffd74 0x9f7ffecc99b7ff5d 0xffffff3267ffffff 0xffffffcc99ffffff

def z12 : W := mkw 0x4042033260048574 0x101080cc9801215d 0x80000732600003fc 0x200001cc980000ff

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0xa031f8fff8000002 0xe80c7e3ffe000000

def z14 : W := mkw 0x0000a800aa08600c 0x00002a002a821803 0x2001f803f800601c 0x08007e00fe001807

def z15 : W := mkw 0xbfbffdc387fb7eb8 0xafefff70e1fedfae 0xffffffc387ffffff 0xfffffff0e1ffffff

def z16 : W := mkw 0x90008040836056b8 0x2400201020d815ae 0xf00180c387e07ffe 0xbc006030e1f81fff

def z17 : W := mkw 0x0040023c00048140 0x4010008f00012050 0x0000003c00000000 0x0000000f00000000

def z18 : W := mkw 0x348df80002497800 0x8d237e0000925e00 0x200ff80000007c00 0x0803fe0000001f00

def z19 : W := mkw 0x020004c001200280 0x00800130004800a0 0xde0007c007e003e3 0xb78001f001f800f8

def z20 : W := mkw 0x4086610260092c34 0x1021984098024b0d 0x200e600260007c1c 0x0803980098001f07

def z21 : W := mkw 0x42c667f2612daff4 0x10b199fc984b6bfd 0xffce67f267ffffff 0xfff399fc99ffffff

def z22 : W := mkw 0x3fbffd8306db7800 0x8fefff60c1b6de00 0xffffffc387fffc03 0xfffffff0e1ffff00

def z23 : W := mkw 0x3ffdfefc07fffbc0 0xcfff7fbf01fffef0 0xfffffffc07ffffe3 0xffffffff01fffff8

def z24 : W := mkw 0x024006fc012483c0 0x409001bf004920f0 0x800007fc000003e0 0x200001ff000000f8

def z25 : W := mkw 0x0010a854afbee3cc 0x40042a152befb8f3 0x5000000007ffe3fc 0x1400000001fff8ff

def z26 : W := mkw 0x248f510350000001 0x0923d440d4000000 0xa03ff8fff8000002 0xe80ffe3ffe000000

def z27 : W := mkw 0x0b3004cc05b20280 0x42cc0133016c80a0 0x0e3000cc07e00000 0x838c003301f80000

def z28 : W := mkw 0x960b0583006014b0 0x2582c160c018052c 0x1e0e070000e01ce1 0x078381c000380738

def z29 : W := mkw 0x1b70aefc07fffbc0 0xc6dc2bbf01fffef0 0xdff007fc07ffffe3 0xf7fc01ff01fffff8

def z30 : W := mkw 0x2920100810000001 0x0a48040204000000 0x0030180c18000000 0x000c060306000000

def z31 : W := mkw 0x940b010300401430 0x2502c040c010050c 0x000e000000001c00 0x0003800000000700

def z32 : W := mkw 0x0000000000000000 0x0000000000000000 0x2031f80000000002 0xc80c7e0000000000

def z33 : W := mkw 0x0930000004920000 0x024c000001248000 0x5ff0000007ff8003 0xd7fc000001ffe000

def z34 : W := mkw 0x3dbdf854afdf7b0c 0x8f6f7e152bf7dec3 0xfffff8ffffffff1f 0xfffffe3fffffffc7

def z35 : W := mkw 0x0920000000000000 0x0248000000000000 0x0ff0000000000003 0xc3fc000000000000

def z36 : W := mkw 0x0000000000000000 0x0000000000000000 0x803000fc00000002 0xe00c003f00000000

def z37 : W := mkw 0x00002010200c2104 0x0000080408030841 0xe0006032601c631e 0x7800180c980718c7

def z38 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0x40000000071c631c 0x1000000001c718c7

def z39 : W := mkw 0x3dbdd80006d35800 0x8f6f760001b4d600 0x1fff980007e39c01 0x87ffe60001f8e700

def z40 : W := mkw 0x1409800002405000 0x0502600000901400 0x7e0f800007e07c03 0x9f83e00001f81f00

def z41 : W := mkw 0x9f3984cd87f25288 0x67ce613361fc94a2 0x0e3180cd87e00000 0x838c603361f80000

def z42 : W := mkw 0x9f7b87ff87f6d7f8 0x67dee1ffe1fdb5fe 0xffff87ff87ffffff 0xffffe1ffe1ffffff

def z43 : W := mkw 0x29f47a28549b2801 0x8a7d1e8a1526ca00 0x01f0783c781f8000 0x407c1e0f1e07e000

def z44 : W := mkw 0x0b7207ff55b683c1 0x42dc81ffd56da0f0 0xdff007ffffff83e3 0xf7fc01ffffffe0f8

def z45 : W := mkw 0x060b058300000000 0x0182c160c0000000 0xae0f87c380000003 0xab83e1f0e0000000

def z46 : W := mkw 0x0000804083004208 0x0000201020c01082 0xe031f8ffff00631e 0xf80c7e3fffc018c7

def z47 : W := mkw 0xbfefd7ebd36056b9 0x2ffbf5faf4d815ae 0xffffffffffe07fff 0xfffffffffff81fff

def z48 : W := mkw 0x0010005405140300 0x00040015014500c0 0xc03000fc071c0302 0xf00c003f01c700c0

def z49 : W := mkw 0x0000000000a280c0 0x400000000028a030 0x1000000000e380e0 0x040000000038e038

def z50 : W := mkw 0x2dad500000000000 0x0b6b540000000000 0x2ffff80000000003 0xcbfffe0000000000

def z51 : W := mkw 0x9010a854af7c77bc 0x24042a152bdf1def 0x5000000007fc7ffc 0x1400000001ff1fff

def z52 : W := mkw 0x961badd7af7c77bc 0x2586eb75ebdf1def 0xfe3ffffffffc7fff 0xff8fffffffff1fff

def z53 : W := mkw 0x3fbdfc8916db7801 0x8fef7f2245b6de00 0x7ffff8cd9ffffc03 0xdffffe3367ffff00

def z54 : W := mkw 0x1f7986fc07f6d3c0 0x47de61bf01fdb4f0 0xffff87fc07ffffe3 0xffffe1ff01fffff8

def z55 : W := mkw 0x2dbdf80006186000 0x0b6f7e0001861800 0x6ffff800071c6003 0xdbfffe0001c71800

def z56 : W := mkw 0x024006a800000000 0x009001aa00000000 0x800007fc00000000 0x200001ff00000000

def z57 : W := mkw 0x0b6006a800000000 0x02d801aa00000000 0x8ff007fc00000003 0xe3fc01ff00000000

def z58 : W := mkw 0x2fff57ff55b683c1 0x4bffd5ffd56da0f0 0xffffffffffff83e3 0xffffffffffffe0f8

def z59 : W := mkw 0x0000004001200280 0x00000010004800a0 0x5000000007e003e0 0x1400000001f800f8

def z60 : W := mkw 0x0930000004920000 0x024c000001248000 0x01f00000001f8000 0x407c00000007e000

def z61 : W := mkw 0x40c46230600da944 0x1031188c18036a51 0x01c06030601f8000 0x4070180c1807e000

def z62 : W := mkw 0xbfefd7ebd3605289 0x2ffbf5faf4d814a2 0xafffffffffe00003 0xebfffffffff80000

def z63 : W := mkw 0x0084600000092800 0x0021180000024a00 0x71ce6000001ffc03 0x5c7398000007ff00

def z64 : W := mkw 0x820205c3812006b8 0x20808170e04801ae 0x800007c3800003fc 0x200001f0e00000ff

def z65 : W := mkw 0x4bf466fc65bfabc4 0x52fd19bf196feaf1 0xdff067fc67ff83e3 0xf7fc19ff19ffe0f8

def z66 : W := mkw 0x2fffffffffbee3cd 0x4bffffffffefb8f3 0xffffffffffffe3ff 0xfffffffffffff8ff

def z67 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xf1fffffff81fffff 0xfc7ffffffe07ffff

def z68 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0x51ce0700001ffffd 0x147381c00007ffff

def z69 : W := mkw 0x0000804083004208 0x0000201020c01082 0xe00180c38700631e 0xb8006030e1c018c7

def z70 : W := mkw 0x2f3914cd15b20281 0x4bce4533456c80a0 0x0e3198cd9fe00000 0x838c663367f80000

def z71 : W := mkw 0x00000054012483c0 0x40000015004920f0 0x00000000000003e0 0x00000000000000f8

def z72 : W := mkw 0x40866112600d2d34 0x1021984498034b4d 0xe00e6032601c7f1e 0x7803980c98071fc7

def z73 : W := mkw 0x0b7006fc05140300 0x02dc01bf014500c0 0xcff007fc071c0303 0xf3fc01ff01c700c0

def z74 : W := mkw 0x00000054a904030c 0x000000152a4100c3 0x800000fff800031c 0x2000003ffe0000c7

def z75 : W := mkw 0x0b7006a804b280c0 0x42dc01aa012ca030 0x5ff0070007ff80e3 0xd7fc01c001ffe038

def z76 : W := mkw 0x0960022800828040 0x4258008a0020a010 0x01c0000000038000 0x007000000000e000

def z77 : W := mkw 0x1000a80002497800 0x84002a0000925e00 0x0000000000007c00 0x0000000000001f00

def z78 : W := mkw 0x4bf6effeefbfeffc 0x52fdbbffbbeffbff 0xffffffffffffffff 0xffffffffffffffff

def z79 : W := mkw 0xd6cfe7f3e36dfffc 0x35b3f9fcf8db7fff 0xffcfe7f3e7ffffff 0xfff3f9fcf9ffffff

def z80 : W := mkw 0x2dad500000000000 0x0b6b540000000000 0x0fce000000000001 0x03f3800000000000

def z81 : W := mkw 0x0010a80006186000 0x00042a0001861800 0x6031f800071c6002 0xd80c7e0001c71800

def z82 : W := mkw 0x3dad500000c31800 0x8f6b54000030c600 0x1fce000000e39c01 0x07f380000038e700

def z83 : W := mkw 0x00002010200c2104 0x0000080408030841 0x00006030601c0000 0x4000180c18070000

def z84 : W := mkw 0xbfef57ab506014b1 0x2ffbd5ead418052c 0xbffffffff8e01ce3 0xeffffffffe380738

def z85 : W := mkw 0x348ff90352497801 0x8d23fe40d4925e00 0x200ff803f8007c00 0x0803fe00fe001f00

def z86 : W := mkw 0x3d39980006d25000 0x8f4e660001b49400 0x0e31980007e00000 0x838c660001f80000

def z87 : W := mkw 0x29b47800049b2800 0x8a6d1e000126ca00 0x01f07800001f8000 0x407c1e000007e000

def z88 : W := mkw 0x2f2b158b10000001 0x0bcac562c4000000 0xae3f9fcf98000003 0xab8fe7f3e6000000

def z89 : W := mkw 0x00c66332600c2104 0x003198cc98030841 0xe1ce6732601c631f 0x787399cc980718c7

def z90 : W := mkw 0x49f4623c649fa944 0x527d188f1927ea51 0x01f0603c601f8000 0x407c180f1807e000

def z91 : W := mkw 0x00d6eb76ef1c630c 0x0035baddbbc718c3 0xe1ffffffff1c631f 0xf87fffffffc718c7

def z92 : W := mkw 0x1094e80006db7800 0x84253a0001b6de00 0x71ce600007fffc03 0x5c73980001ffff00

def z93 : W := mkw 0x0002010200000430 0x000080408000010c 0x80000702000003fc 0x200001c0800000ff

def z94 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0x0fce070000000001 0x03f381c000000000

def z95 : W := mkw 0x2dad500000000000 0x0b6b540000000000 0xaffff8fff8000003 0xebfffe3ffe000000

def z96 : W := mkw 0x4002010260000434 0x100080409800010d 0x000000026000001c 0x0000000098000007

def z97 : W := mkw 0x1409800002405000 0x0502600000901400 0x200f800000007c00 0x0803e00000001f00

def z98 : W := mkw 0x0b6006a800000000 0x02d801aa00000000 0xaff1fffff8000003 0xebfc7ffffe000000

def z99 : W := mkw 0x3dbd500004d31800 0x8f6f54000134c600 0x5ffe000007ff9c03 0xd7ff800001ffe700

def z100 : W := mkw 0x40c6632260092c34 0x103198c898024b0d 0xa1ce673260007c1f 0x687399cc98001f07

def z101 : W := mkw 0x7dbdf81026dffd74 0x9f6f7e0409b7ff5d 0x7ffff80007ffffff 0xdffffe0001ffffff

def z102 : W := mkw 0x00008054ab04430c 0x000020152ac110c3 0xe00180ffff00631e 0xb800603fffc018c7

def z103 : W := mkw 0x0b70aefcafbee3cc 0x42dc2bbf2befb8f3 0xfff1ffffffffe3ff 0xfffc7ffffffff8ff

def z104 : W := mkw 0x0970023c04968140 0x425c008f0125a050 0x01f0003c001f8000 0x407c000f0007e000

def z105 : W := mkw 0x0000804083004208 0x0000201020c01082 0x000180c187000000 0x8000603061c00000

def z106 : W := mkw 0xb68fd5c3d36056b9 0x2da3f570f4d815ae 0xfe0fffc3ffe07fff 0xbf83fff0fff81fff

def z107 : W := mkw 0x0b6006a800a280c0 0x42d801aa0028a030 0x1fc0070000e380e1 0x07f001c00038e038

def z108 : W := mkw 0x2fefffabfa08600d 0x0bfbffeafe821803 0xaffffffff800601f 0xebfffffffe001807

def z109 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0x5e0e070007e07ffd 0x178381c001f81fff

def z110 : W := mkw 0x4bf667fe65bfaff4 0x52fd99ff996febfd 0xfffe67fe67ffffff 0xffff99ff99ffffff

def z111 : W := mkw 0x00c6433240048140 0x003190cc90012050 0xf1ce6732601f83e3 0x7c7399cc9807e0f8

def z112 : W := mkw 0x7dbff90266db7c34 0x9f6ffe4099b6df0d 0x7ffff80267fffc1f 0xdffffe0099ffff07

def z113 : W := mkw 0x0042033200048570 0x001080cc8001215c 0xf1ce0732001fffff 0x7c7381cc8007ffff

def z114 : W := mkw 0x4086610260092c34 0x1021984098024b0d 0xf00e670260007fff 0x3c0399c098001fff

def z115 : W := mkw 0x0000000000000000 0x0000000000000000 0x2001f803f8000000 0x08007e00fe000000

def z116 : W := mkw 0x40d6eb76ef1def7c 0x1035baddbbc77bdf 0xf1ffffffff1fffff 0xfc7fffffffc7ffff

def z117 : W := mkw 0x248f510350000001 0x0923d440d4000000 0x200ff803f8000000 0x0803fe00fe000000

def z118 : W := mkw 0x9f6b87eb836056b8 0x27dae1fae0d815ae 0xffff87ff87e07fff 0xffffe1ffe1f81fff

def z119 : W := mkw 0x0b3004c005b20280 0x02cc0130016c80a0 0xdff007c007ff83e3 0xf7fc01f001ffe0f8

def z120 : W := mkw 0x024006f0012483c0 0x009001bc004920f0 0xdfc007f007ff83e3 0xf7f001fc01ffe0f8

def z121 : W := mkw 0xc24207f3e12487fc 0x309081fcf84921ff 0x800007f3e00003fc 0x200001fcf80000ff

def z122 : W := mkw 0x1010a80006db7800 0x84042a0001b6de00 0x5000000007fffc00 0x1400000001ffff00

def z123 : W := mkw 0x3fffffab56db7801 0x8fffffead5b6de00 0xfffffffffffffc03 0xffffffffffffff00

def z124 : W := mkw 0x00002010200c2104 0x0000080408030841 0xe031f8fff81c631e 0xf80c7e3ffe0718c7

def z125 : W := mkw 0x0b6006a800a280c0 0x42d801aa0028a030 0x9ff007fc00e380e3 0xe7fc01ff0038e038

def z126 : W := mkw 0x3dbdf81026df7904 0x8f6f7e0409b7de41 0xfffff83267ffff1f 0xfffffe0c99ffffc7

def z127 : W := mkw 0x7ffffffe67fffff4 0xdfffffff99fffffd 0xfffffffe67ffffff 0xffffffff99ffffff

def z128 : W := mkw 0x960984c183605288 0x2582613060d814a2 0x0e0180c187e00000 0x8380603061f80000

def z129 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0x0ff000fc07ff8000 0xc3fc003f01ffe000

def z130 : W := mkw 0x29e6532a50000001 0x0a7994ca94000000 0xa1fe7f3e78000003 0x687f9fcf9e000000

def z131 : W := mkw 0x024207ab50000001 0x009081ead4000000 0x800007fff8000000 0x200001fffe000000

def z132 : W := mkw 0xbfbffd8306fb7cb0 0xafefff60c1bedf2c 0x7fffff0007fffce3 0xdfffffc001ffff38

def z133 : W := mkw 0x0010005405b683c0 0x40040015016da0f0 0x5000000007ff83e0 0x1400000001ffe0f8

def z134 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x5fce000007fffc01 0x17f3800001ffff00

def z135 : W := mkw 0x960b0583006014b0 0x2582c160c018052c 0xbe0f87c380e01ce3 0xaf83e1f0e0380738

def z136 : W := mkw 0x40c6432240018c70 0x103190c89000631c 0x11ce070000039ce1 0x047381c00000e738

def z137 : W := mkw 0x0b6006a800000000 0x02d801aa00000000 0x0fc0070000000001 0x03f001c000000000

def z138 : W := mkw 0x940ba903aa48743c 0x2502ea40ea921d0f 0x200ff803f8007c1c 0x0803fe00fe001f07

def z139 : W := mkw 0x0010a810261c6104 0x00042a0409871841 0xe031f832671c631e 0xf80c7e0c99c718c7

def z140 : W := mkw 0x00022112200c2534 0x000088448803094d 0xf00e6732601c7fff 0x7c0399cc98071fff

def z141 : W := mkw 0x3fed56a800e398c0 0xcffb55aa0038e630 0x1fce070000e39ce1 0x07f381c00038e738

def z142 : W := mkw 0x2daf510350000001 0x0b6bd440d4000000 0x2ffff803f8000003 0xcbfffe00fe000000

def z143 : W := mkw 0x00000054a904030c 0x000000152a4100c3 0xa031f8fff800031e 0xe80c7e3ffe0000c7

def z144 : W := mkw 0x09702a3c2c9ea144 0x425c0a8f0b27a851 0x01f0783c781f8000 0x407c1e0f1e07e000

def z145 : W := mkw 0x001088448f104208 0x0004221123c41082 0x0000000007000000 0x0000000001c00000

def z146 : W := mkw 0x001028142c1c2104 0x00040a050b070841 0x00000000001c0000 0x0000000000070000

def z147 : W := mkw 0x0010a80006186000 0x00042a0001861800 0xe031f8ffff1c6002 0xf80c7e3fffc71800

def z148 : W := mkw 0x2dad700000092800 0x0b6b5c0000024a00 0x7ffff800001ffc03 0xdffffe000007ff00

def z149 : W := mkw 0x0010a8142e1c6104 0x00042a050b871841 0x6031f83c7f1c6002 0xd80c7e0f1fc71800

def z150 : W := mkw 0x2f6916a910000001 0x0bda45aa44000000 0x8ff19ffd98000003 0xe3fc67ff66000000

def z151 : W := mkw 0x00c6432240000000 0x003190c890000000 0xa1ce673260000003 0x687399cc98000000

def z152 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0x8e3007fc07e003e0 0xa38c01ff01f800f8

def z153 : W := mkw 0x4040023060048144 0x1010008c18012051 0x0000003060000000 0x0000000c18000000

def z154 : W := mkw 0x3dbff90206db7c30 0x8f6ffe4081b6df0c 0xffffff0207ffffff 0xffffffc081ffffff

def z155 : W := mkw 0x2fff57ff55140301 0x0bffd5ffd54500c0 0xefffffffff1c0303 0xfbffffffffc700c0

def z156 : W := mkw 0x248ff903fa08600d 0x0923fe40fe821803 0x200ff803f800601c 0x0803fe00fe001807

def z157 : W := mkw 0x6fef77bb700dad75 0x1bfbddeedc036b5d 0xfffffffff81fffff 0xfffffffffe07ffff

def z158 : W := mkw 0xfffffff3e7fffffc 0xbffffffcf9ffffff 0xfffffff3e7ffffff 0xfffffffcf9ffffff

def z159 : W := mkw 0x9619acd5af7c738c 0x25866b356bdf1ce3 0xee31f8fffffc631e 0xfb8c7e3fffff18c7

def z160 : W := mkw 0x3ffdfea806db7800 0x8fff7faa01b6de00 0xfffffffc07fffc03 0xffffffff01ffff00

def z161 : W := mkw 0x961badd7af7c77bc 0x2586eb75ebdf1def 0xfe0f87c387fc7fff 0xbf83e1f0e1ff1fff

def z162 : W := mkw 0x0b7006bc04b681c0 0x42dc01af012da070 0x1ff0073c00ff80e1 0x47fc01cf003fe038

def z163 : W := mkw 0x74cffb32624dfd74 0x9d33fecc98937f5d 0xf1cfff32601fffff 0x7c73ffcc9807ffff

def z164 : W := mkw 0x06cf47a340000000 0x01b3d1e8d0000000 0xafcfe7f3e0000003 0xebf3f9fcf8000000

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030783c78000000 0x400c1e0f1e000000

def z166 : W := mkw 0x348d500000411800 0x8d23540000104600 0x000e000000001c00 0x0003800000000700

def z167 : W := mkw 0x2fef57ab50a280c1 0x4bfbd5ead428a030 0xbffffffff8e380e3 0xeffffffffe38e038

def z168 : W := mkw 0x1010a854afdf7b0c 0x84042a152bf7dec3 0x5000000007ffff1c 0x1400000001ffffc7

def z169 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0x11ce6730601f9ce1 0x447399cc1807e738

def z170 : W := mkw 0x964b87f38364d7f8 0x2592e1fce0d935fe 0xffcf87f387ffffff 0xfff3e1fce1ffffff

def z171 : W := mkw 0x020205c2012006b0 0x00808170804801ac 0xfe0e07c207e07fff 0xbf8381f081f81fff

def z172 : W := mkw 0x4042032240008470 0x101080c89000211c 0x00000700000000e0 0x000001c000000038

def z173 : W := mkw 0x1419a80006587000 0x05066a0001961c00 0x7e3ff80007fc7c03 0xdf8ffe0001ff1f00

def z174 : W := mkw 0x00846010200d2904 0x0021180408034a41 0xf1ce6032601fff1f 0x7c73980c9807ffc7

def z175 : W := mkw 0x0094e854af1d6b0c 0x00253a152bc75ac3 0xf1fff8ffff1fff1f 0xfc7ffe3fffc7ffc7

def z176 : W := mkw 0x90000000006014b0 0x240000000018052c 0x1000000000e01ce0 0x0400000000380738

def z177 : W := mkw 0x4010205425bfaff4 0x50040815096febfd 0x5000000007fffffc 0x1400000001ffffff

def z178 : W := mkw 0x960984c183605288 0x2582613060d814a2 0xde0187c187e003e3 0xb78061f061f800f8

def z179 : W := mkw 0x0930005405b683c0 0x424c0015016da0f0 0x5ff0000007ff83e3 0xd7fc000001ffe0f8

def z180 : W := mkw 0x0202058300000000 0x00808160c0000000 0x800007c380000000 0x200001f0e0000000

def z181 : W := mkw 0x1010a854afdf7b0c 0x84042a152bf7dec3 0xf031f8ffffffff1e 0xfc0c7e3fffffffc7

def z182 : W := mkw 0x024006fc012483c0 0x409001bf004920f0 0xde0007fc07e003e3 0xb78001ff01f800f8

def z183 : W := mkw 0x424207fe612487f4 0x509081ff984921fd 0x800007fe600003fc 0x200001ff980000ff

def z184 : W := mkw 0x50d6eb3266dffd74 0x9435bacc99b7ff5d 0xf1ce673267ffffff 0x7c7399cc99ffffff

def z185 : W := mkw 0x2ded522850000001 0x0b7b548a14000000 0x2ffff83c78000003 0xcbfffe0f1e000000

def z186 : W := mkw 0x40d4ea74ef1deb4c 0x10353a9d3bc77ad3 0xe1f1f8ffff1fe31e 0xf87c7e3fffc7f8c7

def z187 : W := mkw 0x7fffffbb76dffd75 0x9fffffeeddb7ff5d 0xffffffffffffffff 0xffffffffffffffff

def z188 : W := mkw 0x1409000000401000 0x0502400000100400 0x1e0e000000e01c01 0x0783800000380700

def z189 : W := mkw 0x025006fc05b683c0 0x409401bf016da0f0 0xd00007fc07ff83e0 0x340001ff01ffe0f8

def z190 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0x6031f800071c631e 0xd80c7e0001c718c7

def z191 : W := mkw 0xbf2994c993605289 0x2fca653264d814a2 0x0e3198cd9fe00000 0x838c663367f80000

def z192 : W := mkw 0x0010a84087186208 0x00042a1021c61882 0xe031f8c3871c631e 0xf80c7e30e1c718c7

def z193 : W := mkw 0x0b70aefcafbee3cc 0x42dc2bbf2befb8f3 0xdff007fc07ffe3ff 0xf7fc01ff01fff8ff

def z194 : W := mkw 0x0000001020040104 0x0000000408010041 0x800000326000031c 0x2000000c980000c7

def z195 : W := mkw 0x0000a800aa08600c 0x00002a002a821803 0xa031f8fff800601e 0xe80c7e3ffe001807

def z196 : W := mkw 0x1000800002405000 0x0400200000901400 0x5000000007e07c00 0x1400000001f81f00

def z197 : W := mkw 0x29e4522850000001 0x0a79148a14000000 0x01f0783c78000000 0x407c1e0f1e000000

def z198 : W := mkw 0x2f29148910000001 0x0bca452244000000 0x0e3198cd98000000 0x838c663366000000

def z199 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xfff1ffffffff83e3 0xfffc7fffffffe0f8

def z200 : W := mkw 0x060b058300000000 0x0182c160c0000000 0xae3ffffff8000003 0xeb8ffffffe000000

def z201 : W := mkw 0x0010a844af18620c 0x00042a112bc61883 0x2031f8cfff00601c 0x880c7e33ffc01807

def z202 : W := mkw 0x3dfdfa3006dff940 0x8f7f7e8c01b7fe50 0xffffff3007ffffe3 0xffffffcc01fffff8

def z203 : W := mkw 0x9409800182405008 0x2502600060901402 0x0001800180000000 0x0000600060000000

def z204 : W := mkw 0xbfffffebd7fb7eb9 0xaffffffaf5fedfae 0xffffffffffffffff 0xffffffffffffffff

def z205 : W := mkw 0x40002010200dad74 0x1000080408036b5d 0x50000000001ffffc 0x140000000007ffff

def z206 : W := mkw 0x29b4f800069b6800 0x8a6d3e0001a6da00 0x61f1f800071fe002 0xd87c7e0001c7f800

def z207 : W := mkw 0x6fef57ab50018c71 0x1bfbd5ead400631c 0x1fce070000039ce1 0x07f381c00000e738

def z208 : W := mkw 0x4010a854af1def7c 0x10042a152bc77bdf 0xf031f8ffff1ffffe 0xfc0c7e3fffc7ffff

def z209 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0x4030783c7f1c631c 0x500c1e0f1fc718c7

def z210 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0xfffff8fffffffc03 0xfffffe3fffffff00

def z211 : W := mkw 0x00c6432240000000 0x003190c890000000 0xa1fffffff8000003 0xe87ffffffe000000

def z212 : W := mkw 0x0960022800000000 0x0258008a00000000 0x01f0003c00000000 0x407c000f00000000

def z213 : W := mkw 0x0084400000000000 0x0021100000000000 0x21ce600000000003 0x4873980000000000

def z214 : W := mkw 0x024207fff904030d 0x009081fffe4100c3 0x800007fff800031c 0x200001fffe0000c7

def z215 : W := mkw 0x001028142c1c2104 0x00040a050b070841 0x0030783c781c0000 0x400c1e0f1e070000

def z216 : W := mkw 0x3fef57ab50c31801 0x8ffbd5ead430c600 0xbffffffff8e39c03 0xeffffffffe38e700

def z217 : W := mkw 0x2be456a850000001 0x0af915aa14000000 0x8ff07ffc78000003 0xe3fc1fff1e000000

def z218 : W := mkw 0x3d3998448fd25208 0x8f4e661123f49482 0x0e3198cd9fe00000 0x838c663367f80000

def z219 : W := mkw 0x3d29100000c21000 0x8f4a440000308400 0x0e00000000e00000 0x0380000000380000

def z220 : W := mkw 0x0b6006e801a282c0 0x42d801ba0068a0b0 0xdfc007c007e383e3 0xb7f001f001f8e0f8

def z221 : W := mkw 0x40c6432240018c70 0x103190c89000631c 0xf1ce07020003ffff 0x3c7381c08000ffff

def z222 : W := mkw 0x941ba957af5c773c 0x2506ea55ebd71dcf 0xe03ff8ffff1c7f1e 0xf80ffe3fffc71fc7

def z223 : W := mkw 0x94098040836056b8 0x2502601020d815ae 0x7e0f800007e07fff 0x9f83e00001f81fff

def z224 : W := mkw 0x40d6eb76ef1def7c 0x1035baddbbc77bdf 0xf1ce6732671fffff 0x7c7399cc99c7ffff

def z225 : W := mkw 0x29a4500000830800 0x8a6914000020c200 0x01c0000000038000 0x007000000000e000

def z226 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xfe3fffffffe07fff 0xff8ffffffff81fff

def z227 : W := mkw 0x3dad700000cb3800 0x8f6b5c000032ce00 0x7fce600000fffc03 0x5ff39800003fff00

def z228 : W := mkw 0x249ff957ff1c630d 0x0927fe55ffc718c3 0xe03ff8ffff1c631e 0xf80ffe3fffc718c7

def z229 : W := mkw 0x0010a854071c6300 0x00042a1501c718c0 0xe031f8fc071c6302 0xf80c7e3f01c718c0

def z230 : W := mkw 0x001088448f104208 0x0004221123c41082 0x003198cd9f000000 0x800c663367c00000

def z231 : W := mkw 0x3dbdf800aedb780c 0x8f6f7e002bb6de03 0x7ffff803fffffc1f 0xdffffe00ffffff07

def z232 : W := mkw 0x0002010200000430 0x000080408000010c 0xf00e070200007fff 0x3c0381c080001fff

def z233 : W := mkw 0x0b3004dc05b60380 0x42cc0137016d80e0 0xce3000fc07fc0302 0xf38c003f01ff00c0

def z234 : W := mkw 0x0be647aa40000000 0x02f991ea90000000 0xaffe67fe60000003 0xebff99ff98000000

def z235 : W := mkw 0x46cf67b3600dad74 0x11b3d9ecd8036b5d 0xffcfe7f3e01fffff 0xfff3f9fcf807ffff

def z236 : W := mkw 0xbfef57ab506014b1 0x2ffbd5ead418052c 0x1fce070000e01ce1 0x07f381c000380738

def z237 : W := mkw 0x2fffffffff1c630d 0x0bffffffffc718c3 0xefffffffff1c631f 0xfbffffffffc718c7

def z238 : W := mkw 0xbfffffffff7c77bd 0x2fffffffffdf1def 0xfffffffffffc7fff 0xffffffffffff1fff

def z239 : W := mkw 0x29f4523c54968141 0x4a7d148f1525a050 0x01f0783c781f8000 0x407c1e0f1e07e000

def z240 : W := mkw 0x90028142836056b8 0x2400a050a0d815ae 0xf00e070207e07fff 0x3c0381c081f81fff

def z241 : W := mkw 0x00108854af14430c 0x000422152bc510c3 0x803198ffff00031c 0xa00c663fffc000c7

def z242 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x0ff1f80007ff8000 0xc3fc7e0001ffe000

def z243 : W := mkw 0x3dbdf854afdf7b0c 0x8f6f7e152bf7dec3 0x7ffff80007ffff1f 0xdffffe0001ffffc7

def z244 : W := mkw 0x001088548f144308 0x0004221523c510c2 0xc03198fd9f1c0302 0xf00c663f67c700c0

def z245 : W := mkw 0x2fff7fab549b2801 0x8bffdfead526ca00 0xaffffffff81f8003 0xebfffffffe07e000

def z246 : W := mkw 0x3dbdf8142edf7904 0x8f6f7e050bb7de41 0x7ffff83c7ffffc03 0xdffffe0f1fffff00

def z247 : W := mkw 0xbfefd7abd2405439 0x2ffbf5eaf490150e 0xaffffffff8007c1f 0xebfffffffe001f07

def z248 : W := mkw 0x648f710370092c35 0x1923dc40dc024b0d 0x200ff803f8007c1c 0x0803fe00fe001f07

def z249 : W := mkw 0x0040023000048140 0x0010008c00012050 0x80000730000003e0 0x200001cc000000f8

def z250 : W := mkw 0x6def7332600dad74 0x1b7bdccc98036b5d 0xffffff32601fffff 0xffffffcc9807ffff

def z251 : W := mkw 0x0042032240000000 0x001080c890000000 0x8000073260000000 0x200001cc98000000

def z252 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0x5fc0070007ff83e1 0x17f001c001ffe0f8

def z253 : W := mkw 0x0010880006104000 0x0004220001841000 0x0031980007000000 0x800c660001c00000

def z254 : W := mkw 0x025006fc053483c0 0x409401bf014d20f0 0xc03007fc071c03e2 0xf00c01ff01c700f8

def z255 : W := mkw 0x0002010200000430 0x000080408000010c 0x100e070000001ce1 0x040381c000000738

def z256 : W := mkw 0x0970023004968140 0x025c008c0125a050 0xdff0073007ff83e3 0xf7fc01cc01ffe0f8

def z257 : W := mkw 0x064b07ab50000001 0x0192c1ead4000000 0xae0f87fff8000003 0xab83e1fffe000000

def z258 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0x0fff9fcd98000001 0x83ffe7f366000000

def z259 : W := mkw 0x0000200000092800 0x0000080000024a00 0x50000000001ffc00 0x140000000007ff00

def z260 : W := mkw 0x80000040812006b8 0x20000010204801ae 0x00000000000003fc 0x00000000000000ff

def z261 : W := mkw 0x0010005405140300 0x00040015014500c0 0x40000000071c0300 0x1000000001c700c0

def z262 : W := mkw 0x02c647ab50000001 0x00b191ead4000000 0xa1ce67fff8000003 0x687399fffe000000

def z263 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0x1e0f87c187e01ce1 0x8783e1f061f80738

def z264 : W := mkw 0x49f66332649fad74 0x127d98cc9927eb5d 0xfffe673267ffffff 0xffff99cc99ffffff

def z265 : W := mkw 0xbf3b9dc387f256b8 0xafcee770e1fc95ae 0xfe3f9fc387e07fff 0xbf8fe7f0e1f81fff

def z266 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0x0ffe7f3c78000001 0x43ff9fcf1e000000

def z267 : W := mkw 0x960b858382405438 0x2582e160e090150e 0xae0f87c380007c1f 0xab83e1f0e0001f07

def z268 : W := mkw 0x4086610260092c34 0x1021984098024b0d 0x71ce6002601ffc1f 0x5c7398009807ff07

def z269 : W := mkw 0x001028542d1c2304 0x00040a150b4708c1 0xc03078fc7f1c0302 0xf00c1e3f1fc700c0

def z270 : W := mkw 0x0b308ccc8fb24288 0x42cc233323ec90a2 0x0e3198cd9fe00000 0x838c663367f80000

def z271 : W := mkw 0x0b20048800a20080 0x42c8012200288020 0x0e00000000e00000 0x0380000000380000

def z272 : W := mkw 0x6fef57ab50018c71 0x1bfbd5ead400631c 0xbffffffff8039ce3 0xeffffffffe00e738

def z273 : W := mkw 0x0930000004920000 0x024c000001248000 0x0e30000007e00000 0x838c000001f80000

def z274 : W := mkw 0x024006fca92483cc 0x409001bf2a4920f3 0x800007fff80003fc 0x200001fffe0000ff

def z275 : W := mkw 0x0000a840ab08620c 0x00002a102ac21883 0xe001f8c3ff00631e 0xb8007e30ffc018c7

def z276 : W := mkw 0x0b20048800000000 0x02c8012200000000 0x0e3000cc00000000 0x838c003300000000

def z277 : W := mkw 0x29b47800049b2800 0x8a6d1e000126ca00 0x5ff0780007ff8003 0xd7fc1e0001ffe000

def z278 : W := mkw 0x00100054ad14030c 0x000400152b4500c3 0xc03000ffff1c031e 0xf00c003fffc700c7

def z279 : W := mkw 0x2fef57bb50048141 0x0bfbd5eed4012050 0xfffffffff81f83e3 0xfffffffffe07e0f8

def z280 : W := mkw 0x2d29100000000000 0x0b4a440000000000 0x0e31980000000000 0x838c660000000000

def z281 : W := mkw 0x1010a80006db7800 0x84042a0001b6de00 0x7031f80007fffc02 0xdc0c7e0001ffff00

def z282 : W := mkw 0x2fef57ff512483c1 0x4bfbd5ffd44920f0 0xaffffffff80003e3 0xebfffffffe0000f8

def z283 : W := mkw 0x6fef57bb70048575 0x1bfbd5eedc01215d 0xaffffffff80003ff 0xebfffffffe0000ff

def z284 : W := mkw 0x024006a8002080c0 0x409001aa00082030 0x00000700000000e0 0x000001c000000038

def z285 : W := mkw 0x90008040836056b8 0x2400201020d815ae 0x5000000007e07ffc 0x1400000001f81fff

def z286 : W := mkw 0x2dbd500004920000 0x0b6f540001248000 0x7ffff80007ff8003 0xdffffe0001ffe000

def z287 : W := mkw 0x3d39980006d25000 0x8f4e660001b49400 0x7e3f980007e07c03 0x9f8fe60001f81f00

def z288 : W := mkw 0x4086410240010c30 0x102190409000430c 0x000e000000001c00 0x0003800000000700

def z289 : W := mkw 0x0010000004100000 0x0004000001040000 0x40300000071c0002 0xd00c000001c70000

def z290 : W := mkw 0x40d46a346c1da944 0x10351a8d1b076a51 0x01f0783c781f8000 0x407c1e0f1e07e000

def z291 : W := mkw 0x49f6633e649fad74 0x527d98cf9927eb5d 0xf1fe673e601fffff 0x7c7f99cf9807ffff

def z292 : W := mkw 0x0970023c04968140 0x425c008f0125a050 0xd1f0073c001f83e3 0x747c01cf0007e0f8

def z293 : W := mkw 0x0010a854afbee3cc 0x40042a152befb8f3 0xf031f8ffffffe3fe 0xfc0c7e3ffffff8ff

def z294 : W := mkw 0x148de00002497800 0x0523780000925e00 0x7fcfe00007fffc03 0xdff3f80001ffff00

def z295 : W := mkw 0x1000000000c31800 0x840000000030c600 0x1000000000e39c00 0x040000000038e700

def z296 : W := mkw 0x00000054a904030c 0x000000152a4100c3 0x000000000000031c 0x00000000000000c7

def z297 : W := mkw 0xbfefd7ebd36056b9 0x2ffbf5faf4d815ae 0xffcf87c387e07fff 0xbff3e1f0e1f81fff

def z298 : W := mkw 0x0bf466fc05bfabc0 0x42fd19bf016feaf0 0xfffe67fc07ffffe3 0xffff99ff01fffff8

def z299 : W := mkw 0x0000a854ab0c630c 0x00002a152ac318c3 0xa001f8fff800631c 0x28007e3ffe0018c7

def z300 : W := mkw 0x3dbdf85407df7b00 0x8f6f7e1501f7dec0 0xfffff8fc07ffff03 0xfffffe3f01ffffc0

def z301 : W := mkw 0x0970027c05b683c0 0x425c009f016da0f0 0x51f0003c07ff83e0 0x547c000f01ffe0f8

def z302 : W := mkw 0x40c46230600da944 0x1031188c18036a51 0x71ce6030601ffc03 0x5c73980c1807ff00

def z303 : W := mkw 0x9010a854af7c77bc 0x24042a152bdf1def 0xf031f8fffffc7ffe 0xfc0c7e3fffff1fff

def z304 : W := mkw 0x2bf47efc05bfabc0 0xcafd1fbf016feaf0 0xdff07ffc07ff83e3 0xf7fc1fff01ffe0f8

def z305 : W := mkw 0x0b6006e801200280 0x02d801ba004800a0 0xdff007fc07e003e3 0xf7fc01ff01f800f8

def z306 : W := mkw 0x3ffdfea806fbf8c0 0xcfff7faa01befe30 0x7fffff0007fffce3 0xdfffffc001ffff38

def z307 : W := mkw 0x348df800aa49780c 0x8d237e002a925e03 0x200ff803f8007c1c 0x0803fe00fe001f07

def z308 : W := mkw 0x29e4522850000001 0x0a79148a14000000 0xa1f1f8fff8000002 0xe87c7e3ffe000000

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00180c380000002 0xa8006030e0000000

def z310 : W := mkw 0x4010a854af1def7c 0x10042a152bc77bdf 0x50000000071ffffc 0x1400000001c7ffff

def z311 : W := mkw 0x0010001404140100 0x0004000501050040 0x0030003c001c0000 0x400c000f00070000

def z312 : W := mkw 0x3409980002405000 0x8d02660000901400 0x0001980000000000 0x0000660000000000

def z313 : W := mkw 0x9f7986fd87f6d3c8 0x67de61bf61fdb4f2 0xdff187fd87ff83e3 0xf7fc61ff61ffe0f8

def z314 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0x2fcfff03f8000001 0x0bf3ffc0fe000000

def z315 : W := mkw 0x40c663224009ac70 0x103198c890026b1c 0x71ce6700001ffce3 0x5c7399c00007ff38

def z316 : W := mkw 0x920084c0836056b8 0x2480213020d815ae 0xde0007c007e07fff 0xb78001f001f81fff

def z317 : W := mkw 0x0010a800ae18600c 0x00042a002b861803 0x6031f803ff1c601e 0xd80c7e00ffc71807

def z318 : W := mkw 0x824207ebd12006b9 0x209081faf44801ae 0x800007fff80003fc 0x200001fffe0000ff

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000fff8000000 0x2000003ffe000000

def z320 : W := mkw 0x0000800002004000 0x0000200000801000 0x6001800007006002 0x9800600001c01800

def z321 : W := mkw 0x0002010200000000 0x0000804080000000 0xa00e070200000003 0x280381c080000000

def z322 : W := mkw 0x8b7207ff85b687f8 0x62dc81ffe16da1fe 0xdff007ff87ff83ff 0xf7fc01ffe1ffe0ff

def z323 : W := mkw 0x0000800082004008 0x0000200020801002 0x200180038000601c 0x08006000e0001807

def z324 : W := mkw 0x024207ab50000001 0x009081ead4000000 0xa031fffff8000002 0xe80c7ffffe000000

def z325 : W := mkw 0xd000a050a36dfffc 0x3400281428db7fff 0x5000000007fffffc 0x1400000001ffffff

def z326 : W := mkw 0x00c6432240000000 0x003190c890000000 0x01ce070000000001 0x007381c000000000

def z327 : W := mkw 0x2084780000092800 0x88211e0000024a00 0x0000780000000000 0x00001e0000000000

def z328 : W := mkw 0x2def532240000000 0x0b7bd4c890000000 0xafffff3260000003 0xebffffcc98000000

def z329 : W := mkw 0x4052ab76ef1ce77c 0x1014aaddbbc739df 0xe031ffffff1c63fe 0xf80c7fffffc718ff

def z330 : W := mkw 0x2fff7fbf7c1c2105 0x0bffdfefdf070841 0xaffffffff81c0003 0xebfffffffe070000

def z331 : W := mkw 0x9000800082405438 0x240020002090150e 0x0000000000007c1c 0x0000000000001f07

def z332 : W := mkw 0x09b46000049b2800 0x026d18000126ca00 0x7ffe600007fffc03 0xdfff980001ffff00

def z333 : W := mkw 0x248d500000000000 0x0923540000000000 0x200ff80000000000 0x0803fe0000000000

def z334 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0x2e0f80c387e07c1c 0x8b83e030e1f81f07

def z335 : W := mkw 0x40422332600dad74 0x101088cc98036b5d 0xd0000732601ffffc 0x340001cc9807ffff

def z336 : W := mkw 0x0086610200092c30 0x0021984080024b0c 0xf1ce6702001fffff 0x7c7399c08007ffff

def z337 : W := mkw 0xc2c667f3e12daffc 0x30b199fcf84b6bff 0xf1ce67f3e01fffff 0x7c7399fcf807ffff

def z338 : W := mkw 0x00002054a90c230c 0x000008152a4308c3 0xe00060fff81c631e 0x7800183ffe0718c7

def z339 : W := mkw 0x0b70aefcaf1c630c 0x02dc2bbf2bc718c3 0xeff1ffffff1c631f 0xfbfc7fffffc718c7

def z340 : W := mkw 0x0010a814ae1c610c 0x00042a052b871843 0x2031f83ff81c601c 0x480c7e0ffe071807

def z341 : W := mkw 0xbdbff90386db7c38 0xaf6ffe40e1b6df0e 0x7ffff80387fffc1f 0xdffffe00e1ffff07

def z342 : W := mkw 0x960b0583006014b0 0x2582c160c018052c 0xfe0e070200e07fff 0x3f8381c080381fff

def z343 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0x8ffe07fc00000003 0xe3ff81ff00000000

def z344 : W := mkw 0x0000200020082004 0x0000080008020801 0x200060026000601c 0x0800180098001807

def z345 : W := mkw 0x0010004405100200 0x0004001101440080 0x003000cc07000000 0x800c003301c00000

def z346 : W := mkw 0x40420376e904877c 0x101080ddba4121df 0x800007fff80003fc 0x200001fffe0000ff

def z347 : W := mkw 0x4000200020092c34 0x1000080008024b0d 0x0000000000007c1c 0x0000000000001f07

def z348 : W := mkw 0x96cfc7e3c36056b8 0x25b3f1f8f0d815ae 0xffcfe7f3e7e07fff 0xfff3f9fcf9f81fff

def z349 : W := mkw 0x00c4422040000000 0x0031108810000000 0x01c0603060000000 0x4070180c18000000

def z350 : W := mkw 0x40c66376e90daf7c 0x103198ddba436bdf 0xf1ce67fff81fffff 0x7c7399fffe07ffff

def z351 : W := mkw 0x0f6b07ab00000000 0x03dac1eac0000000 0xafff87ff80000003 0xebffe1ffe0000000

def z352 : W := mkw 0x424207bb70048575 0x109081eedc01215d 0x800007fff80003fc 0x200001fffe0000ff

def z353 : W := mkw 0x0b3004dc05b683c0 0x42cc0137016da0f0 0x5e3000cc07ff83e0 0x978c003301ffe0f8

def z354 : W := mkw 0x0000804083004208 0x0000201020c01082 0x400000000700631c 0x1000000001c018c7

def z355 : W := mkw 0x9609048100601080 0x2582412040180420 0x0e00000000e00000 0x0380000000380000

def z356 : W := mkw 0xbfffffff87fffff8 0xefffffffe1fffffe 0xffffffff87ffffff 0xffffffffe1ffffff

def z357 : W := mkw 0x940b810382405438 0x2502e040e090150e 0xf00f870380007fff 0x3c03e1c0e0001fff

def z358 : W := mkw 0xdfffe7ffe7fffffc 0x77fff9fff9ffffff 0xffffe7ffe7ffffff 0xfffff9fff9ffffff

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z360 : W := mkw 0x2f29148910000001 0x0bca452244000000 0x0e00000000000000 0x0380000000000000

def z361 : W := mkw 0x0930a800069a6000 0x024c2a0001a69800 0x7ff1f80007ffe003 0xdffc7e0001fff800

def z362 : W := mkw 0x060b85c383004208 0x0182e170e0c01082 0xee0f87c38700631f 0xbb83e1f0e1c018c7

def z363 : W := mkw 0x3fffffff57fffbc1 0xcfffffffd5fffef0 0xffffffffffffffe3 0xfffffffffffffff8

def z364 : W := mkw 0x40866112600dad74 0x1021984498036b5d 0x700e6002601ffffc 0x1c0398009807ffff

def z365 : W := mkw 0x0010000004920000 0x0004000001248000 0x5000000007ff8000 0x1400000001ffe000

def z366 : W := mkw 0x160984c003605280 0x0582613000d814a0 0xfe0f87c007e07fe3 0xbf83e1f001f81ff8

def z367 : W := mkw 0x0200048910000001 0x0080012244000000 0x000000cd98000000 0x0000003366000000

def z368 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xc03000fc071c631e 0xf00c003f01c718c7

def z369 : W := mkw 0x2fff57bf54968141 0x4bffd5efd525a050 0xaffffffff81f8003 0xebfffffffe07e000

def z370 : W := mkw 0x0409000000000000 0x0102400000000000 0x2e0f800000000003 0x8b83e00000000000

def z371 : W := mkw 0x0000001000040100 0x0000000400010040 0xc0000030001c0302 0x7000000c000700c0

def z372 : W := mkw 0x29e4522850000001 0x0a79148a14000000 0x01c0000000000000 0x0070000000000000

def z373 : W := mkw 0x3ffd56fc05f79bc0 0xcfff55bf017de6f0 0xdffe07fc07ff9fe3 0xf7ff81ff01ffe7f8

def z374 : W := mkw 0x4086e902ea096c3c 0x1021ba40ba825b0f 0x200ff803f8007c1c 0x0803fe00fe001f07

def z375 : W := mkw 0x2dbd7800049b2800 0x8b6f5e000126ca00 0x2ffff800001f8003 0xcbfffe000007e000

def z376 : W := mkw 0x29b478142c9f2904 0x8a6d1e050b27ca41 0x01f0783c781f8000 0x407c1e0f1e07e000

def z377 : W := mkw 0x40c46230600da944 0x1031188c18036a51 0xe1c06032601fe31e 0x7870180c9807f8c7

def z378 : W := mkw 0x1010a85407fffbc0 0xc4042a1501fffef0 0x5000000007ffffe0 0x1400000001fffff8

def z379 : W := mkw 0x0010a8448f186208 0x00042a1123c61882 0x6031f8cd9f1c6002 0xd80c7e3367c71800

def z380 : W := mkw 0x0000001428040104 0x000000050a010041 0x0000003c78000000 0x0000000f1e000000

def z381 : W := mkw 0x0084400000010800 0x0021100000004200 0x11ce000000039c01 0x047380000000e700

def z382 : W := mkw 0x060b058300000430 0x0182c160c000010c 0xfe0f87c380007fff 0xbf83e1f0e0001fff

def z383 : W := mkw 0x40c663226009ac74 0x103198c898026b1d 0x31ce67026003fcfd 0x0c7399c09800ff3f

def z384 : W := mkw 0x0000000000000000 0x0000000000000000 0x5e00000007e00003 0x9780000001f80000

def z385 : W := mkw 0xbfaf558300e31cb0 0xafebd560c038c72c 0x1fce070000e39ce1 0x07f381c00038e738

def z386 : W := mkw 0xbfbffdd7afff7fbc 0xafefff75ebffdfef 0xffffffffffffffff 0xffffffffffffffff

def z387 : W := mkw 0x0b6006b800a681c0 0x42d801ae0029a070 0xdfc0073000ff83e3 0x77f001cc003fe0f8

def z388 : W := mkw 0x2dbdf854af1c630c 0x0b6f7e152bc718c3 0xeffff8ffff1c631f 0xfbfffe3fffc718c7

def z389 : W := mkw 0x4be667ba600dad74 0x12f999ee98036b5d 0xfffe67fe601fffff 0xffff99ff9807ffff

def z390 : W := mkw 0x2def532b50000001 0x0b7bd4cad4000000 0x21fff83ff8000000 0x487ffe0ffe000000

def z391 : W := mkw 0x0b7006fcadb683cc 0x42dc01bf2b6da0f3 0xdff007ffffff83ff 0xf7fc01ffffffe0ff

def z392 : W := mkw 0x0b6006b800048140 0x02d801ae00012050 0xdff007fc001f83e3 0xf7fc01ff0007e0f8

def z393 : W := mkw 0x001028142c1c2104 0x00040a050b070841 0xa031f8fff81c0002 0xe80c7e3ffe070000

def z394 : W := mkw 0xd6cf47a340619cf0 0x35b3d1e8d018673c 0x1fce070000e39ce1 0x07f381c00038e738

def z395 : W := mkw 0xd6dfeff7ef7dfffc 0x35b7fbfdfbdf7fff 0xffffffffffffffff 0xffffffffffffffff

def z396 : W := mkw 0x961badc3877876b8 0x2586eb70e1de1dae 0xfe3fffc387fc7fff 0xff8ffff0e1ff1fff

def z397 : W := mkw 0x2fef57fff904030d 0x0bfbd5fffe4100c3 0xaffffffff800031f 0xebfffffffe0000c7

def z398 : W := mkw 0x7def733260cfbd74 0x9f7bdccc9833ef5d 0xffce673260ffffff 0x7ff399cc983fffff

def z399 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0xafcf87c380000003 0xabf3e1f0e0000000

def z400 : W := mkw 0x0002010200000430 0x000080408000010c 0x200e000200007c1c 0x0803800080001f07

def z401 : W := mkw 0x024207ff512483c1 0x409081ffd44920f0 0x800007fff80003e0 0x200001fffe0000f8

def z402 : W := mkw 0x3d39b80006da7000 0x8f4e6e0001b69c00 0x6e31f80007fc6002 0xdb8c7e0001ff1800

def z403 : W := mkw 0x020004cc01200280 0x40800133004800a0 0x000000cc00000000 0x0000003300000000

def z404 : W := mkw 0x0000a810aa0c610c 0x00002a042a831843 0xe001f833f81c631e 0x78007e0cfe0718c7

def z405 : W := mkw 0x40d66376651daf74 0x103598dd99476bdd 0xf1fe67fe671fffff 0xfc7f99ff99c7ffff

def z406 : W := mkw 0x3dbd780004db3800 0x8f6f5e000136ce00 0x1ffe780000ff9c01 0x47ff9e00003fe700

def z407 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0x6001f803ff1c631c 0x18007e00ffc718c7

def z408 : W := mkw 0x349df854af5d7b0c 0x8d277e152bd75ec3 0xe03ff8ffff1c7f1e 0xf80ffe3fffc71fc7

def z409 : W := mkw 0xb68ffdc383697eb8 0xada3ff70e0da5fae 0xfe0fffc387e07fff 0xbf83fff0e1f81fff

def z410 : W := mkw 0x2fef57eb51200281 0x0bfbd5fad44800a0 0xffffffffffe003e3 0xfffffffffff800f8

def z411 : W := mkw 0x061badd7af1c630c 0x0186eb75ebc718c3 0xee3fffffff1c631f 0xfb8fffffffc718c7

def z412 : W := mkw 0x1419a80006db7800 0x85066a0001b6de00 0x7e0f800007fffc03 0x9f83e00001ffff00

def z413 : W := mkw 0xd0c6e372e36dfffc 0x3431b8dcb8db7fff 0xf1ce673267ffffff 0x7c7399cc99ffffff

def z414 : W := mkw 0xd68fe5c3e3697ebc 0x35a3f970f8da5faf 0xfe0fe7c3e7e07fff 0xbf83f9f0f9f81fff

def z415 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xc00000ffff1c631c 0x3000003fffc718c7

def z416 : W := mkw 0x0000004001000200 0x0000001000400080 0xc00000c007000302 0xb000003001c000c0

def z417 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0xafce673260000003 0x6bf399cc98000000

def z418 : W := mkw 0x0000001000048140 0x0000000400012050 0x50000000001f83e0 0x140000000007e0f8

def z419 : W := mkw 0x1010880006d25000 0x8404220001b49400 0x0000000007e00000 0x0000000001f80000

def z420 : W := mkw 0x2be657ab50000001 0x0af995ead4000000 0x81f07ffff8000000 0x607c1ffffe000000

def z421 : W := mkw 0x0000004081000208 0x0000001020400082 0x800000c38000031c 0x20000030e00000c7

def z422 : W := mkw 0x2faf558b50000001 0x0bebd562d4000000 0x2e3ff8cff8000000 0x8b8ffe33fe000000

def z423 : W := mkw 0xd4cfe333e24dfd7c 0x3533f8ccf8937f5f 0xf1cfe733e01fffff 0x7c73f9ccf807ffff

def z424 : W := mkw 0xbfafd5c3836056b8 0x2febf570e0d815ae 0xffffffc387e07fff 0xfffffff0e1f81fff

def z425 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xa00e673260007ffc 0x280399cc98001fff

def z426 : W := mkw 0x0970023c04968140 0x425c008f0125a050 0x5ff0003c07ff8003 0xd7fc000f01ffe000

def z427 : W := mkw 0x3dad500000c31800 0x8f6b54000030c600 0x3ffff80000e39c03 0xcffffe000038e700

def z428 : W := mkw 0x4096e956ef1d6f3c 0x1025ba55bbc75bcf 0xe03ff8ffff1c7f1e 0xf80ffe3fffc71fc7

def z429 : W := mkw 0x29b47800049b2800 0x8a6d1e000126ca00 0x71fe7800001ffc03 0x5c7f9e000007ff00

def z430 : W := mkw 0x2f399ccd9f104209 0x0bce673367c41082 0x0e3198cd9f000000 0x838c663367c00000

def z431 : W := mkw 0x00102800049b2800 0x80040a000126ca00 0x00000000001f8000 0x000000000007e000

def z432 : W := mkw 0x9b7086fc87f6d7f8 0x66dc21bf21fdb5fe 0xdff007fc07ffffff 0xf7fc01ff01ffffff

def z433 : W := mkw 0x140b810202405430 0x0502e0408090150c 0xfe0f870207e07fff 0xbf83e1c081f81fff

def z434 : W := mkw 0x3dbdf85407fffbc0 0xcf6f7e1501fffef0 0x7ffff80007ffffe3 0xdffffe0001fffff8

def z435 : W := mkw 0x40022112200dad74 0x1000884488036b5d 0xf00e0702001fffff 0x3c0381c08007ffff

def z436 : W := mkw 0x2fef77ab50092801 0x0bfbddead4024a00 0xfffffffff81ffc03 0xfffffffffe07ff00

def z437 : W := mkw 0x940b8143836056b8 0x2502e050e0d815ae 0x700f800387e07ffc 0x1c03e000e1f81fff

def z438 : W := mkw 0x3d39980006d25000 0x8f4e660001b49400 0x5ff1980007ff8003 0xd7fc660001ffe000

def z439 : W := mkw 0x0b7006a804920000 0x02dc01aa01248000 0xdff007fc07ff8003 0xf7fc01ff01ffe000

def z440 : W := mkw 0x961badc387fb7eb8 0xa586eb70e1fedfae 0xfe0f87c387ffffff 0xbf83e1f0e1ffffff

def z441 : W := mkw 0x40c6433260048574 0x103190cc9801215d 0xa1ce6732600003ff 0x687399cc980000ff

def z442 : W := mkw 0x00102854ad1c230c 0x00040a152b4708c3 0x803078fff81c031c 0x600c1e3ffe0700c7

def z443 : W := mkw 0x0000005401040300 0x00000015004100c0 0x800000fc00000300 0x2000003f000000c0

def z444 : W := mkw 0x2fffdfefdf104209 0x0bfff7fbf7c41082 0xafffffffff000003 0xebffffffffc00000

def z445 : W := mkw 0x7def532240c39c70 0x9f7bd4c89030e71c 0x1fce070000e39ce1 0x07f381c00038e738

def z446 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0x81c06732601f83fc 0x607019cc9807e0ff

def z447 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0000700000003e3 0x340001c0000000f8

def z448 : W := mkw 0x00c6432240000430 0x003190c89000010c 0xf1ce673260007fff 0x7c7399cc98001fff

def z449 : W := mkw 0x40d66b366c1dad74 0x10359acd9b076b5d 0xf1fe7f3e781fffff 0x7c7f9fcf9e07ffff

def z450 : W := mkw 0x3f399ccc07f25280 0xcfce673301fc94a0 0x0e3198cc07e00000 0x838c663301f80000

def z451 : W := mkw 0x3d39b854afde730c 0x8f4e6e152bf79cc3 0xee31f8fffffc631e 0xfb8c7e3fffff18c7

def z452 : W := mkw 0x001028142c1c2104 0x00040a050b070841 0xe030783e781c631e 0x780c1e0f9e0718c7

def z453 : W := mkw 0x0010280004182000 0x00040a0001060800 0x00307800001c0000 0x400c1e0000070000

def z454 : W := mkw 0x7dfdfa3066dff944 0x9f7f7e8c19b7fe51 0x7ffff83067fffc03 0xdffffe0c19ffff00

def z455 : W := mkw 0xbfafd5c383e35eb8 0xafebf570e0f8d7ae 0xffcf87c387e3ffff 0xbff3e1f0e1f8ffff

def z456 : W := mkw 0x6fef77ab70092c35 0x1bfbddeadc024b0d 0xaffffffff8007c1f 0xebfffffffe001f07

def z457 : W := mkw 0x6fef77bb700da945 0x1bfbddeedc036a51 0xaffffffff81f8003 0xebfffffffe07e000

def z458 : W := mkw 0x9f3b85cf87f256b8 0x67cee173e1fc95ae 0xfe3f87cf87e07fff 0xbf8fe1f3e1f81fff

def z459 : W := mkw 0xd48fe103e2497c3c 0x3523f840f8925f0f 0x200fe003e0007c1c 0x0803f800f8001f07

def z460 : W := mkw 0x54cfe332624dfd74 0x1533f8cc98937f5d 0xffcfe73267ffffff 0xfff3f9cc99ffffff

def z461 : W := mkw 0x001088448f104208 0x0004221123c41082 0xe03198cf9f00631e 0xb80c6633e7c018c7

def z462 : W := mkw 0x3dbff90356db7801 0x8f6ffe40d5b6de00 0x7ffff803fffffc03 0xdffffe00ffffff00

def z463 : W := mkw 0x824207ff812487f8 0x609081ffe04921fe 0x800007ff800003fc 0x200001ffe00000ff

def z464 : W := mkw 0xd6cfc7e3c361def8 0x35b3f1f8f0d877be 0xffcf87c387e3ffff 0xbff3e1f0e1f8ffff

def z465 : W := mkw 0x9f6b07ab00e294f0 0x67dac1eac038a53c 0x1fce070000e39ce1 0x07f381c00038e738

def z466 : W := mkw 0x1419a854af5c730c 0x05066a152bd71cc3 0xfe3ff8fffffc7f1f 0xff8ffe3fffff1fc7

def z467 : W := mkw 0x9f7bafffaffef7fc 0x67deebffebffbdff 0xffffffffffffffff 0xffffffffffffffff

def z468 : W := mkw 0x820285c3832046b8 0x2080a170e0c811ae 0xe00187c3870063fe 0xb80061f0e1c018ff

def z469 : W := mkw 0x4084600060092804 0x1021180018024a01 0x0000600060000000 0x0000180018000000

def z470 : W := mkw 0x0609048100000000 0x0182412040000000 0x0e0180c180000000 0x8380603060000000

def z471 : W := mkw 0xbf399cc187f25288 0xafce673061fc94a2 0x0e3198c187e00000 0x838c663061f80000

def z472 : W := mkw 0x3ffdfefcaffffbcc 0xcfff7fbf2bfffef3 0xffffffffffffffff 0xffffffffffffffff

def z473 : W := mkw 0x0010a80006186000 0x00042a0001861800 0x40000000071c6000 0x1000000001c71800

def z474 : W := mkw 0x020084c083204288 0x0080213020c810a2 0xfe0187c387e063ff 0xbf8061f0e1f818ff

def z475 : W := mkw 0x1409804083405208 0x0502601020d01482 0xfe0f80c387e07f1f 0xbf83e030e1f81fc7

def z476 : W := mkw 0xd6cf67b3606dbdf4 0x35b3d9ecd81b6f7d 0xffce673260ffffff 0x7ff399cc983fffff

def z477 : W := mkw 0x960984c183605288 0x2582613060d814a2 0x7e0f80c187e07c03 0x9f83e03061f81f00

def z478 : W := mkw 0x0000a80002086000 0x00002a0000821800 0x2001f80000006000 0x08007e0000001800

def z479 : W := mkw 0x4000001020048574 0x100000040801215d 0x00000000000003fc 0x00000000000000ff

def z480 : W := mkw 0x40d6637665bfaff4 0x503598dd996febfd 0xf1ce673267ffffff 0x7c7399cc99ffffff

def z481 : W := mkw 0x0000000000000000 0x0000000000000000 0x51c00000001f8003 0x547000000007e000

def z482 : W := mkw 0x29b4f854af9f6b0c 0x8a6d3e152be7dac3 0xe1f1f8ffff1fe31e 0xf87c7e3fffc7f8c7

def z483 : W := mkw 0x2f29148910000001 0x0bca452244000000 0xae31f8fff8000002 0xeb8c7e3ffe000000

def z484 : W := mkw 0x6fff77ff75bfaff5 0x5bffddffdd6febfd 0xffffffffffffffff 0xffffffffffffffff

def z485 : W := mkw 0x69f47a30649fa944 0x9a7d1e8c1927ea51 0x01f07830601f8000 0x407c1e0c1807e000

def z486 : W := mkw 0x961b8dc78f7056b8 0x2586e371e3dc15ae 0xfe3f9fcf9fe07fff 0xbf8fe7f3e7f81fff

def z487 : W := mkw 0xafef57ebd12006b9 0x2bfbd5faf44801ae 0xaffffffff80003ff 0xebfffffffe0000ff

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0x003198cd98000000 0x800c663366000000

def z489 : W := mkw 0x3dadf80002497800 0x8f6b7e0000925e00 0x2ffff80000007c03 0xcbfffe0000001f00

def z490 : W := mkw 0x24cf532350000001 0x0933d4c8d4000000 0xa1cfff33f8000003 0x6873ffccfe000000

def z491 : W := mkw 0x348df80002497800 0x8d237e0000925e00 0x71cff800001ffc03 0x5c73fe000007ff00

def z492 : W := mkw 0xd64b87f3e364d7fc 0x3592e1fcf8d935ff 0xfe0f87f3e7e07fff 0xbf83e1fcf9f81fff

def z493 : W := mkw 0x961b85d787f6d7f8 0x6586e175e1fdb5fe 0xfe0f87c387ffffff 0xbf83e1f0e1ffffff

def z494 : W := mkw 0x3fef57ab50c31801 0x8ffbd5ead430c600 0x1fce070000e39c01 0x07f381c00038e700

def z495 : W := mkw 0x820205c3812006b8 0x20808170e04801ae 0xf00e07c380007fff 0x3c0381f0e0001fff

def z496 : W := mkw 0x0200048000000000 0x0080012000000000 0x8e0007c000000003 0xa38001f000000000

def z497 : W := mkw 0x40c6433240058d70 0x103190cc9001635c 0xd1ce0730001f9fe3 0x747381cc0007e7f8

def z498 : W := mkw 0x2fff57ab54920001 0x0bffd5ead5248000 0xffffffffffff8003 0xffffffffffffe000

def z499 : W := mkw 0xffeff7fbf36dfffd 0x3ffbfdfefcdb7fff 0xffffffffffffffff 0xffffffffffffffff

def z500 : W := mkw 0xbdbdf84087fb7eb8 0xaf6f7e1021fedfae 0x7ffff80007ffffff 0xdffffe0001ffffff

def z501 : W := mkw 0x4042033260048574 0x101080cc9801215d 0xf00e073260007fff 0x3c0381cc98001fff

def z502 : W := mkw 0x2fef57ab50000431 0x0bfbd5ead400010c 0xfffffffff8007fff 0xfffffffffe001fff

def z503 : W := mkw 0x0000a800aa08600c 0x00002a002a821803 0x000000000000601c 0x0000000000001807

def z504 : W := mkw 0x2fff57ef55b20281 0x4bffd5fbd56c80a0 0xafffffffffe00003 0xebfffffffff80000

def z505 : W := mkw 0x960badc3ab6876bc 0x2582eb70eada1daf 0xfe0fffc3ffe07fff 0xbf83fff0fff81fff

def z506 : W := mkw 0x64cf7333700dad75 0x1933dcccdc036b5d 0xf1cfff33f81fffff 0x7c73ffccfe07ffff

def z507 : W := mkw 0x820004c181200288 0x20800130604800a2 0x000000c180000000 0x0000003060000000

def z508 : W := mkw 0x0210acd4af3c638c 0x00842b352bcf18e3 0xfe31fffffffc63ff 0xff8c7fffffff18ff

def z509 : W := mkw 0x268f558350000001 0x09a3d560d4000000 0xae0fffc3f8000003 0xab83fff0fe000000

def z510 : W := mkw 0x3dadf80002cb7800 0x8f6b7e0000b2de00 0x3fcff80000e3fc01 0x0ff3fe000038ff00

def z511 : W := mkw 0x0000280028082004 0x00000a000a020801 0x0000780078000000 0x00001e001e000000

def z512 : W := mkw 0x40c6432240018c70 0x103190c89000631c 0xb1ce673260039ce3 0x6c7399cc9800e738

def z513 : W := mkw 0x0010005405b683c0 0x40040015016da0f0 0xd03000fc07ff83e2 0xf40c003f01ffe0f8

def z514 : W := mkw 0x960984c1836056b8 0x2582613060d815ae 0x5e0180c187e07ffc 0x9780603061f81fff

def z515 : W := mkw 0x960b8583026054b0 0x2582e160c098152c 0x7e0f870007e07ce3 0x9f83e1c001f81f38

def z516 : W := mkw 0x3dfffb2246db7800 0x8f7ffec891b6de00 0xffffff3267fffc03 0xffffffcc99ffff00

def z517 : W := mkw 0x001088448f104208 0x0004221123c41082 0xa031f8ffff000002 0xe80c7e3fffc00000

def z518 : W := mkw 0x0000200000082000 0x0000080000020800 0x60006000001c6002 0x5800180000071800

def z519 : W := mkw 0x9f6b87eb83e2d6f8 0x67dae1fae0f8b5be 0xffcf87c387e3ffff 0xbff3e1f0e1f8ffff

def z520 : W := mkw 0x0002010350000001 0x00008040d4000000 0x00000003f8000000 0x00000000fe000000

def z521 : W := mkw 0x940b810382405438 0x2502e040e090150e 0x7e0f800387e07c1f 0x9f83e000e1f81f07

def z522 : W := mkw 0x4042033260048574 0x101080cc9801215d 0xd1c00732601f83ff 0x747001cc9807e0ff

def z523 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x21fff800001ffc00 0x487ffe000007ff00

def z524 : W := mkw 0x0252afffff1c630d 0x0094abffffc718c3 0xe031ffffff1c631e 0xf80c7fffffc718c7

def z525 : W := mkw 0x964b87ebd36056b9 0x2592e1faf4d815ae 0xfe0f87ffffe07fff 0xbf83e1fffff81fff

def z526 : W := mkw 0x0930a854af9e630c 0x024c2a152be798c3 0xfff1f8ffffffe31f 0xfffc7e3ffffff8c7

def z527 : W := mkw 0x3fefffab52497801 0x8ffbffead4925e00 0xaffffffff8007c03 0xebfffffffe001f00

def z528 : W := mkw 0x6fef77bb700dad75 0x1bfbddeedc036b5d 0xffce6732601fffff 0x7ff399cc9807ffff

def z529 : W := mkw 0x024006fc012483c0 0x409001bf004920f0 0xd1c007fc001f83e3 0x747001ff0007e0f8

def z530 : W := mkw 0x00000000a800000c 0x000000002a000003 0x00000003f800001c 0x00000000fe000007

def z531 : W := mkw 0x2fef77bb700c2105 0x0bfbddeedc030841 0xeffffffff81c631f 0xfbfffffffe0718c7

def z532 : W := mkw 0x3dbdf8448fdb7a08 0x8f6f7e1123f6de82 0x7ffff8cd9ffffc03 0xdffffe3367ffff00

def z533 : W := mkw 0x920285c3836056b8 0x2480a170e0d815ae 0xd00007c387e07ffc 0x340001f0e1f81fff

def z534 : W := mkw 0x3dfdfa2856db7801 0x8f7f7e8a15b6de00 0x7ffff83c7ffffc03 0xdffffe0f1fffff00

def z535 : W := mkw 0x9010805487f6d7f8 0x6404201521fdb5fe 0x5000000007fffffc 0x1400000001ffffff

def z536 : W := mkw 0x348df80002497800 0x8d237e0000925e00 0x7e0ff80007e07c03 0x9f83fe0001f81f00

def z537 : W := mkw 0x2930180004920000 0x8a4c060001248000 0x0030180000000000 0x000c060000000000

def z538 : W := mkw 0x29f47a3c7c1c2105 0x0a7d1e8f1f070841 0x01f0783c781c0000 0x407c1e0f1e070000

def z539 : W := mkw 0x820205d7a92407bc 0x20808175ea4901ef 0x800007fff80003fc 0x200001fffe0000ff

def z540 : W := mkw 0x0b7006ec05b20280 0x42dc01bb016c80a0 0x8ff007fc07e00003 0xe3fc01ff01f80000

def z541 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0x21ce6032601ffc1c 0x4873980c9807ff07

def z542 : W := mkw 0x0000a050a30c630c 0x0000281428c318c3 0xe001e0f3e71c631e 0xf800783cf9c718c7

def z543 : W := mkw 0x349df80006597800 0x8d277e0001965e00 0x603ff800071c7c02 0xd80ffe0001c71f00

def z544 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0x8fce07fff8000001 0x23f381fffe000000

def z545 : W := mkw 0x40c4422040018840 0x1031108810006210 0x01c0000000038000 0x007000000000e000

def z546 : W := mkw 0x40c66332600da944 0x103198cc98036a51 0xa1ce6732601f8003 0x687399cc9807e000

def z547 : W := mkw 0x00402230200ca144 0x0010088c08032851 0xf1c06732601fe3ff 0x7c7019cc9807f8ff

def z548 : W := mkw 0x0050aa74af1ce34c 0x00142a9d2bc738d3 0xf1f1ffffff1fe3ff 0xfc7c7fffffc7f8ff

def z549 : W := mkw 0x020004c001200280 0x00800130004800a0 0x800007c0000003e0 0x200001f0000000f8

def z550 : W := mkw 0x820205c3812006b8 0x20808170e04801ae 0xde0007c387e003ff 0xb78001f0e1f800ff

def z551 : W := mkw 0xbfbdfcc187fb7a88 0xafef7f3061fedea2 0x7ffff8c187fffc03 0xdffffe3061ffff00

def z552 : W := mkw 0x7dfffb76efdfff7c 0x9f7ffeddbbf7ffdf 0xffffffffffffffff 0xffffffffffffffff

def z553 : W := mkw 0x0010001404968140 0x400400050125a050 0x00000000001f8000 0x000000000007e000

def z554 : W := mkw 0xb48fd103d2405439 0x2d23f440f490150e 0x200ff803f8007c1c 0x0803fe00fe001f07

def z555 : W := mkw 0x2fef57ab50a280c1 0x4bfbd5ead428a030 0x1fce070000e380e1 0x07f381c00038e038

def z556 : W := mkw 0x82020583002004b0 0x20808160c008012c 0x00000700000000e0 0x000001c000000038

def z557 : W := mkw 0x3dfdfa3c06dff940 0xcf7f7e8f01b7fe50 0x7ffff83c07fffc03 0xdffffe0f01ffff00

def z558 : W := mkw 0x040b010300000000 0x0102c040c0000000 0x200f800380000000 0x0803e000e0000000

def z559 : W := mkw 0x0b7026fc25bea3c4 0x42dc09bf096fa8f1 0xfff067fe67ffe3ff 0xfffc19ff99fff8ff

def z560 : W := mkw 0x8002010380000438 0x20008040e000010e 0x000000038000001c 0x00000000e0000007

def z561 : W := mkw 0x3dbdd80006d25000 0x8f6f760001b49400 0x2ffff80007e00003 0xcbfffe0001f80000

def z562 : W := mkw 0x40002010200dad74 0x1000080408036b5d 0xf0006032601ffffe 0x7c00180c9807ffff

def z563 : W := mkw 0x7dfffb2246dbfc70 0x9f7ffec891b6ff1c 0x7fffff0007fffce3 0xdfffffc001ffff38

def z564 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x2e3ff80007e07c00 0x8b8ffe0001f81f00

def z565 : W := mkw 0x2fffffab56186001 0x0bffffead5861800 0xefffffffff1c6003 0xfbffffffffc71800

def z566 : W := mkw 0x349df80006db7800 0x8d277e0001b6de00 0x700ff80007fffc00 0x1c03fe0001ffff00

def z567 : W := mkw 0x3fbdfccc07fb7a80 0xcfef7f3301fedea0 0x7ffff8cc07fffc03 0xdffffe3301ffff00

def z568 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xe00180c3871c631e 0xb8006030e1c718c7

def z569 : W := mkw 0x0084600000092800 0x0021180000024a00 0x200e600000007c00 0x0803980000001f00

def z570 : W := mkw 0x021004d405b683c0 0x40840135016da0f0 0xde0007c007ff83e3 0xb78001f001ffe0f8

def z571 : W := mkw 0x3dadd00002c35800 0x8f6b740000b0d600 0x7fcf800007e3fc03 0x9ff3e00001f8ff00

def z572 : W := mkw 0x0970aa7caf9ee34c 0x425c2a9f2be7b8d3 0xe1f1f8ffff1fe31e 0xf87c7e3fffc7f8c7

def z573 : W := mkw 0xbf2b95cb936056b9 0x2fcae572e4d815ae 0xfe3f9fcf9fe07fff 0xbf8fe7f3e7f81fff

def z574 : W := mkw 0x968fe5c383697eb8 0x25a3f970e0da5fae 0xffcfe7c387ffffff 0xfff3f9f0e1ffffff

def z575 : W := mkw 0x0040022850000001 0x0010008a14000000 0x0000003c78000000 0x0000000f1e000000

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000603260000002 0x6800180c98000000

def z577 : W := mkw 0x0000004489000208 0x0000001122400082 0x000000cd98000000 0x0000003366000000

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00000020000631e 0x38000000800018c7

def z579 : W := mkw 0x2f7916fd15b683c1 0x4bde45bf456da0f0 0xdff19ffd9fff83e3 0xf7fc67ff67ffe0f8

def z580 : W := mkw 0x961b85d7877457b8 0x2586e175e1dd15ee 0xfe3f87ff87fc7fff 0xff8fe1ffe1ff1fff

def z581 : W := mkw 0x00002010200c2104 0x0000080408030841 0x40000000001c631c 0x10000000000718c7

def z582 : W := mkw 0x0b7086fc87b6c3c8 0x42dc21bf21edb0f2 0xfff187ff87ffe3ff 0xfffc61ffe1fff8ff

def z583 : W := mkw 0x0b7207fe05b687f0 0x42dc81ff816da1fc 0xfffe07fe07ffffff 0xffff81ff81ffffff

def z584 : W := mkw 0x060b058300000000 0x0182c160c0000000 0x0e0e070000000001 0x038381c000000000

def z585 : W := mkw 0x3fffdfab56d25001 0x8ffff7ead5b49400 0xafffffffffe00003 0xebfffffffff80000

def z586 : W := mkw 0x40c6e372e30def7c 0x1031b8dcb8c37bdf 0xf1cfe7f3e71fffff 0xfc73f9fcf9c7ffff

def z587 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0x2fffff0000000003 0xcbffffc000000000

def z588 : W := mkw 0x9f7b07ff05f697f0 0x67dec1ffc17da5fc 0xdffe07fc07ff9fe3 0xf7ff81ff01ffe7f8

def z589 : W := mkw 0x40846010200dad74 0x1021180408036b5d 0x71ce6000001fffff 0x5c7398000007ffff

def z590 : W := mkw 0x0040022000000000 0x0010008800000000 0x81c0073000000003 0x607001cc00000000

def z591 : W := mkw 0x0f7b07ff05b683c0 0x43dec1ffc16da0f0 0xffff87ff87ff83e3 0xffffe1ffe1ffe0f8

def z592 : W := mkw 0x0010005405140300 0x00040015014500c0 0xe031f8ffff1c0302 0xf80c7e3fffc700c0

def z593 : W := mkw 0x9f3b85c387f256b8 0x27cee170e1fc95ae 0xffff87c387ffffff 0xffffe1f0e1ffffff

def z594 : W := mkw 0x42c667fe612daff4 0x50b199ff984b6bfd 0xf1ce67fe601fffff 0x7c7399ff9807ffff

def z595 : W := mkw 0x3d39b80006db7800 0x8f4e6e0001b6de00 0x5e31980007fffc00 0x978c660001ffff00

def z596 : W := mkw 0x3dbdf84087db7a08 0x8f6f7e1021f6de82 0xfffff8c387ffff1f 0xfffffe30e1ffffc7

def z597 : W := mkw 0x2409100110000001 0x0902440044000000 0x0001980198000000 0x0000660066000000

def z598 : W := mkw 0x248f510350000001 0x0923d440d4000000 0x000e000000000000 0x0003800000000000

def z599 : W := mkw 0x960ba5d3a36c77bc 0x2582e974e8db1def 0xfe0fe7f3e7fc7fff 0xff83f9fcf9ff1fff

def z600 : W := mkw 0x39b4f80006db7800 0x8e6d3e0001b6de00 0x51f0780007fffc00 0x547c1e0001ffff00

def z601 : W := mkw 0x0b6006fc01a683c0 0x42d801bf0069a0f0 0x9fc007fc00e383e1 0x27f001ff0038e0f8

def z602 : W := mkw 0x0b702efc2dbea3c4 0x42dc0bbf0b6fa8f1 0xdff07ffc7fff83e3 0xf7fc1fff1fffe0f8

def z603 : W := mkw 0x2f39bcddbf1c630d 0x0bce6f376fc718c3 0xee31f8ffff1c631e 0xfb8c7e3fffc718c7

def z604 : W := mkw 0x0b7006bc04968140 0x42dc01af0125a050 0x8ff007fc001f8003 0xe3fc01ff0007e000

def z605 : W := mkw 0xb48ff90382497c38 0xad23fe40e0925f0e 0x200ff80380007c1c 0x0803fe00e0001f07

def z606 : W := mkw 0x3fffffffffdf7b0d 0x8ffffffffff7dec3 0xffffffffffffff1f 0xffffffffffffffc7

def z607 : W := mkw 0x0b70aefc07bee3c0 0x42dc2bbf01efb8f0 0xfff1fffc07ffe3e3 0xfffc7fff01fff8f8

def z608 : W := mkw 0x2fed56a950000001 0x0bfb55aa54000000 0x0ff1f8fdf8000000 0xc3fc7e3f7e000000

def z609 : W := mkw 0x4be667ba60afadf4 0x52f999ee982beb7d 0xffce673260ffffff 0x7ff399cc983fffff

def z610 : W := mkw 0x0b6207ab50000001 0x02d881ead4000000 0x8ff007fff8000003 0xe3fc01fffe000000

def z611 : W := mkw 0x29f4fa7cff1c630d 0x0a7d3e9f3fc718c3 0xe1f1f8ffff1c631e 0xf87c7e3fffc718c7

def z612 : W := mkw 0x40c6eb32ea0ded7c 0x1031baccba837b5f 0xf1cfff33f81fffff 0x7c73ffccfe07ffff

def z613 : W := mkw 0x3fffffab56db7801 0x8fffffead5b6de00 0x7fffff0007fffc03 0xdfffffc001ffff00

def z614 : W := mkw 0x69f67b32649fad74 0x9a7d9ecc9927eb5d 0xf1fe7f32601fffff 0x7c7f9fcc9807ffff

def z615 : W := mkw 0x2fefd7ebd3004209 0x0bfbf5faf4c01082 0xefffffffff00631f 0xfbffffffffc018c7

def z616 : W := mkw 0x3f399c8916d25001 0x8fce672245b49400 0x0e3198cd9fe00000 0x838c663367f80000

def z617 : W := mkw 0x2bf456fc55b683c1 0x4afd15bf156da0f0 0xdff07ffc7fff83e3 0xf7fc1fff1fffe0f8

def z618 : W := mkw 0x1409800002405000 0x0502600000901400 0x0e01800007e00000 0x8380600001f80000

def z619 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0x0031f8fdff1c0000 0xc00c7e3f7fc70000

def z620 : W := mkw 0x060b05c301200280 0x0182c170c04800a0 0xfe0f87c387e003e3 0xbf83e1f0e1f800f8

def z621 : W := mkw 0x0930000c04920000 0x424c000301248000 0x0030000c00000000 0x000c000300000000

def z622 : W := mkw 0x2fff57ff55b683c1 0x4bffd5ffd56da0f0 0xdffe07fc07ff83e3 0xf7ff81ff01ffe0f8

def z623 : W := mkw 0x0bf647fe45b683c0 0x42fd91ff916da0f0 0xfffe67fe67ff83e3 0xffff99ff99ffe0f8

def z624 : W := mkw 0x0002814283004638 0x0000a050a0c0118e 0xf00f87c387007fff 0xbc03e1f0e1c01fff

def z625 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xa00f87c380007ffc 0x2803e1f0e0001fff

def z626 : W := mkw 0x29a4500000000000 0x0a69140000000000 0x01f0780000000000 0x407c1e0000000000

def z627 : W := mkw 0x9010a84087fb7eb8 0xa4042a1021fedfae 0x5000000007fffffc 0x1400000001ffffff

def z628 : W := mkw 0x42c667bb700dad75 0x10b199eedc036b5d 0xf1ce67fff81fffff 0x7c7399fffe07ffff

def z629 : W := mkw 0x000088008a004008 0x0000220022801002 0x0001980198000000 0x0000660066000000

def z630 : W := mkw 0x2084500050000001 0x0821140014000000 0x0000780078000000 0x00001e001e000000

def z631 : W := mkw 0x3f799efc07f6d3c0 0xcfde67bf01fdb4f0 0xdff19ffc07ff83e3 0xf7fc67ff01ffe0f8

def z632 : W := mkw 0x0b7006ec05b282c0 0x42dc01bb016ca0b0 0x1ff007cc07e380e1 0x87fc01f301f8e038

def z633 : W := mkw 0x0b708efc8fb6c3c8 0x42dc23bf23edb0f2 0xdff19ffd9fff83e3 0xf7fc67ff67ffe0f8

def z634 : W := mkw 0x8212add7af3c67bc 0x2084ab75ebcf19ef 0xe031ffffff1c63fe 0xf80c7fffffc718ff

def z635 : W := mkw 0x021004d405340380 0x00840135014d00e0 0xde3007fc07fc03e3 0xf78c01ff01ff00f8

def z636 : W := mkw 0x960b85c383605288 0x2582e170e0d814a2 0xae0f87c387e00003 0xab83e1f0e1f80000

def z637 : W := mkw 0x0b6006fc012483c0 0x42d801bf004920f0 0x8ff007fc000003e3 0xe3fc01ff000000f8

def z638 : W := mkw 0x940b814383405638 0x2502e050e0d0158e 0xe00f80c387007f1e 0xb803e030e1c01fc7

def z639 : W := mkw 0x860b05c3812006b8 0x2182c170e04801ae 0xae0f87c3800003ff 0xab83e1f0e00000ff

def z640 : W := mkw 0x69e6733a700dad75 0x1a799cce9c036b5d 0xf1fe7f3e781fffff 0x7c7f9fcf9e07ffff

def z641 : W := mkw 0x0012a956af1c673c 0x0004aa55abc719cf 0xf03fffffff1c7fff 0xfc0fffffffc71fff

def z642 : W := mkw 0x0086410240000000 0x0021904090000000 0x200e600260000000 0x0803980098000000

def z643 : W := mkw 0x4be647aa40a38cf0 0x52f991ea9028e33c 0x1fce070000e39ce1 0x07f381c00038e738

def z644 : W := mkw 0x6fffffffff1def7d 0x1bffffffffc77bdf 0xffffffffff1fffff 0xffffffffffc7ffff

def z645 : W := mkw 0x020004c001200280 0x00800130004800a0 0x0e0000c007e00000 0x8380003001f80000

def z646 : W := mkw 0x0084600000092800 0x0021180000024a00 0x01c06000001f8000 0x407018000007e000

def z647 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0x81f007fc001f83e0 0x607c01ff0007e0f8

def z648 : W := mkw 0x960b8583826054b8 0x2582e160e098152e 0x3e0f870380e07cfd 0x0f83e1c0e0381f3f

def z649 : W := mkw 0x964b87ff8364d7f8 0x6592e1ffe0d935fe 0xfe0f87ff87e07fff 0xbf83e1ffe1f81fff

def z650 : W := mkw 0x40c46230600dad74 0x1031188c18036b5d 0x51c06030601ffffc 0x5470180c1807ffff

def z651 : W := mkw 0x2faf558300000000 0x0bebd560c0000000 0xafffffc380000003 0xebfffff0e0000000

def z652 : W := mkw 0x0930005405960300 0x024c0015016580c0 0xdff000fc07ff8303 0xf7fc003f01ffe0c0

def z653 : W := mkw 0x40422332600ca574 0x101088cc9803295d 0xe0006732601c63fe 0x780019cc980718ff

def z654 : W := mkw 0x40c46230600da944 0x1031188c18036a51 0xd1c06730601f83e3 0x747019cc1807e0f8

def z655 : W := mkw 0x69e47238700da945 0x1a791c8e1c036a51 0x01f0783c781f8000 0x407c1e0f1e07e000

def z656 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xe0006032671c631e 0x7800180c99c718c7

def z657 : W := mkw 0x0094e80006196800 0x00253a0001865a00 0x71fff800071ffc03 0xdc7ffe0001c7ff00

def z658 : W := mkw 0x1d39800006d25000 0x074e600001b49400 0x7fff800007fffc03 0xdfffe00001ffff00

def z659 : W := mkw 0x2f6b17ab50000001 0x0bdac5ead4000000 0x8e319ffff8000000 0xa38c67fffe000000

def z660 : W := mkw 0x40d6eb32661ded74 0x1035bacc99877b5d 0xf1ffff32671fffff 0xfc7fffcc99c7ffff

def z661 : W := mkw 0x0050027405b683c0 0x4014009d016da0f0 0xd1c0073007ff83e3 0x747001cc01ffe0f8

def z662 : W := mkw 0x0000000000000430 0x000000000000010c 0x5000000000007ffc 0x1400000000001fff

def z663 : W := mkw 0x5010a81026dffd74 0x94042a0409b7ff5d 0x5000000007fffffc 0x1400000001ffffff

def z664 : W := mkw 0x0050027405148340 0x0014009d014520d0 0xd1f007fc071f83e3 0xf47c01ff01c7e0f8

def z665 : W := mkw 0x001008040c100000 0x0004020103040000 0x0030180c18000000 0x000c060306000000

def z666 : W := mkw 0x00c46230000da940 0x0031188c00036a50 0xf1ce6730001fffe3 0x7c7399cc0007fff8

def z667 : W := mkw 0x00c6632240092800 0x003198c890024a00 0xf1ce6732601ffc03 0x7c7399cc9807ff00

def z668 : W := mkw 0x0200048000200080 0x0080012000080020 0x1e00070000e000e1 0x078001c000380038

def z669 : W := mkw 0x960b85d7ab6457bc 0x2582e175ead915ef 0xfe0f87ffffe07fff 0xbf83e1fffff81fff

def z670 : W := mkw 0x4b7026fc25bfaff4 0x52dc09bf096febfd 0xdff007fc07ffffff 0xf7fc01ff01ffffff

def z671 : W := mkw 0x0040023000048140 0x0010008c00012050 0x01c00030001f8000 0x4070000c0007e000

def z672 : W := mkw 0x3fbdfcc007fb7a80 0x8fef7f3001fedea0 0xffffffc007ffffe3 0xfffffff001fffff8

def z673 : W := mkw 0x160b858302405000 0x0582e160c0901400 0xfe0f87c387e07c03 0xbf83e1f0e1f81f00

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x700e000000007c03 0x1c03800000001f00

def z675 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0x8e0187c387e003fc 0xa38061f0e1f800ff

def z676 : W := mkw 0x2fed56a800000000 0x0bfb55aa00000000 0xaffffffc00000003 0xebffffff00000000

def z677 : W := mkw 0x4b7207fe65b687f4 0x52dc81ff996da1fd 0xdff007fe67ff83ff 0xf7fc01ff99ffe0ff

def z678 : W := mkw 0x024207ab50000001 0x009081ead4000000 0x0000070000000000 0x000001c000000000

def z679 : W := mkw 0x0920000000820000 0x0248000000208000 0x1fc0000000e38001 0x07f000000038e000

def z680 : W := mkw 0x29f47a3c049fa940 0xca7d1e8f0127ea50 0x01f0783c001f8000 0x407c1e0f0007e000

def z681 : W := mkw 0x2ffd56fc05b683c0 0x4bff55bf016da0f0 0xfffffffc07ff83e3 0xffffffff01ffe0f8

def z682 : W := mkw 0x0010805487144308 0x0004201521c510c2 0xe03180ff871c631e 0xf80c603fe1c718c7

def z683 : W := mkw 0x0b3004cc05b20280 0x42cc0133016c80a0 0x5ff000cc07ff8003 0xd7fc003301ffe000

def z684 : W := mkw 0x2fad548910000001 0x0beb552244000000 0x2ffff8cd98000003 0xcbfffe3366000000

def z685 : W := mkw 0x4000000000018c70 0x100000000000631c 0x1000000000039ce0 0x040000000000e738

def z686 : W := mkw 0x0b30acdcafbe638c 0x42cc2b372bef98e3 0xee31f8fffffc631e 0xfb8c7e3fffff18c7

def z687 : W := mkw 0xd60ba5d3a36dfffc 0x3582e974e8db7fff 0xfe0f87c387ffffff 0xbf83e1f0e1ffffff

def z688 : W := mkw 0x4bf647fe45b78ff0 0x52fd91ff916de3fc 0xdffe07fc07ff9fe3 0xf7ff81ff01ffe7f8

def z689 : W := mkw 0x1930a80006db7800 0x864c2a0001b6de00 0x5ff0000007fffc03 0xd7fc000001ffff00

def z690 : W := mkw 0x9000804083605288 0x2400201020d814a2 0x0000000007e00000 0x0000000001f80000

def z691 : W := mkw 0x3fefd7ab52405001 0x0ffbf5ead4901400 0xffffffffffe07c03 0xfffffffffff81f00

def z692 : W := mkw 0x0040022000008040 0x0010008800002010 0x11c00700000380e1 0x047001c00000e038

def z693 : W := mkw 0x0010004405b20280 0x40040011016c80a0 0x0000000007e00000 0x0000000001f80000

def z694 : W := mkw 0x40402230200dad74 0x1010088c08036b5d 0xd1c00730001fffff 0x747001cc0007ffff

def z695 : W := mkw 0x960b05c3816016b8 0x2582c170e05805ae 0x9e0e07c380e01ffd 0x278381f0e03807ff

def z696 : W := mkw 0x0b3004cc05b20280 0x42cc0133016c80a0 0xde3007cc07e003e3 0xb78c01f301f800f8

def z697 : W := mkw 0x40c6433260058d74 0x103190cc9801635d 0x91ce073260039ffd 0x247381cc9800e7ff

def z698 : W := mkw 0x26cf57ab50000001 0x09b3d5ead4000000 0xa00ffffff8000000 0x2803fffffe000000

def z699 : W := mkw 0x0970027c05968340 0x425c009f0165a0d0 0xc1f000fc071f8302 0xf07c003f01c7e0c0

def z700 : W := mkw 0x0250aefcaf3ce3cc 0x40942bbf2bcf38f3 0xe031ffffff1c63fe 0xf80c7fffffc718ff

def z701 : W := mkw 0xbfffd7ffd7f6d7f9 0x6ffff5fff5fdb5fe 0xffffffffffffffff 0xffffffffffffffff

def z702 : W := mkw 0x00102054251c2304 0x00040815094708c1 0xe03060fe671c631e 0xf80c183f99c718c7

def z703 : W := mkw 0x960b05c3016016b0 0x2582c170c05805ac 0xde0e07c007e01fe3 0xb78381f001f807f8

def z704 : W := mkw 0x960984c183605288 0x2582613060d814a2 0xee0180c387e0631e 0xbb806030e1f818c7

def z705 : W := mkw 0x96198cc58f705288 0x2586633163dc14a2 0x0e3198cd9fe00000 0x838c663367f80000

def z706 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0x403198cd9f1c631c 0x900c663367c718c7

def z707 : W := mkw 0x00102054251c2304 0x00040815094708c1 0xe031f8ffff1c631e 0xf80c7e3fffc718c7

def z708 : W := mkw 0x0010a854afbe638c 0x40042a152bef98e3 0xe031f8fffffc631e 0xf80c7e3fffff18c7

def z709 : W := mkw 0x0960022800000000 0x0258008a00000000 0xa1f1f8fff8000002 0xe87c7e3ffe000000

def z710 : W := mkw 0x0930000004920000 0x024c000001248000 0x7ffe000007fffc03 0xdfff800001ffff00

def z711 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x5ffe780007fffc01 0x57ff9e0001ffff00

def z712 : W := mkw 0x0b7006f005b683c0 0x02dc01bc016da0f0 0xdff007f007ff83e3 0xf7fc01fc01ffe0f8

def z713 : W := mkw 0x2def532b50000001 0x0b7bd4cad4000000 0xa1fff8fff8000002 0xe87ffe3ffe000000

def z714 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xfff187ff87ff83e3 0xfffc61ffe1ffe0f8

def z715 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xd1ce0732601ffffd 0x347381cc9807ffff

def z716 : W := mkw 0x9010a854afff7fbc 0xa4042a152bffdfef 0x5000000007fffffc 0x1400000001ffffff

def z717 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xdff19ffd9fff83e3 0xf7fc67ff67ffe0f8

def z718 : W := mkw 0x2faf558300000000 0x0bebd560c0000000 0xaffffffff8000003 0xebfffffffe000000

def z719 : W := mkw 0x0010a854af3ce3cc 0x40042a152bcf38f3 0x40000000071c63fc 0x1000000001c718ff

def z720 : W := mkw 0xbf399cc58ff25288 0xafce673163fc94a2 0x0e3198cd9fe00000 0x838c663367f80000

def z721 : W := mkw 0x961b2d972c7c35b4 0x2586cb65cb1f0d6d 0x1e3e7f3c78fc1ce1 0x478f9fcf1e3f0738

def z722 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0x5ff007cc07ff83e1 0x97fc01f301ffe0f8

def z723 : W := mkw 0x064b07ab50000001 0x0192c1ead4000000 0xae3ffffff8000003 0xeb8ffffffe000000

def z724 : W := mkw 0x2f2b158b10000001 0x0bcac562c4000000 0xae3ffffff8000003 0xeb8ffffffe000000

def z725 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xfffe07fc07ffffe3 0xffff81ff01fffff8

def z726 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xe0000002071c631e 0x3800000081c718c7

def z727 : W := mkw 0x00c66332000dad70 0x003198cc80036b5c 0xf1ce6732001fffff 0x7c7399cc8007ffff

def z728 : W := mkw 0x1252afab56db7801 0x8494abead5b6de00 0xd00007fffffffc00 0x340001ffffffff00

def z729 : W := mkw 0x001088448f104208 0x0004221123c41082 0xe031f8ffff00631e 0xf80c7e3fffc018c7

def z730 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0x7e0f870387e07ffd 0x1f83e1c0e1f81fff

def z731 : W := mkw 0xbfef57ab50401431 0x2ffbd5ead410050c 0xaffffffff8001c03 0xebfffffffe000700

def z732 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0x00000000071c0000 0x0000000001c70000

def z733 : W := mkw 0x024006fc012483c0 0x409001bf004920f0 0xdfc007fc07ff83e3 0xf7f001ff01ffe0f8

def z734 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0x71ce6702601ffffd 0x1c7399c09807ffff

def z735 : W := mkw 0x3dbd780004db3800 0x8f6f5e000136ce00 0x5ffe780007ff9c03 0xd7ff9e0001ffe700

def z736 : W := mkw 0x2b701efc05b683c0 0xcadc07bf016da0f0 0xdff01ffc07ff83e3 0xf7fc07ff01ffe0f8

def z737 : W := mkw 0x0b70aefcafbee3cc 0x42dc2bbf2befb8f3 0x5fc0070007ffe3fd 0x17f001c001fff8ff

def z738 : W := mkw 0x7d7b9b3266d6d574 0x9f5ee6cc99b5b55d 0x8e319f3267e003fc 0xa38c67cc99f800ff

def z739 : W := mkw 0x2daf510350000001 0x0b6bd440d4000000 0xaffff8fff8000003 0xebfffe3ffe000000

def z740 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xdfc0073007ff83e3 0x77f001cc01ffe0f8

def z741 : W := mkw 0x025006f405b683c0 0x409401bd016da0f0 0xdfc007f007ff83e3 0xf7f001fc01ffe0f8

def z742 : W := mkw 0x40c6432240018c70 0x103190c89000631c 0xb1fffffff8039ce3 0xec7ffffffe00e738

def z743 : W := mkw 0xd48fe903ea497c3c 0x3523fa40fa925f0f 0x200ff803f8007c1c 0x0803fe00fe001f07

def z744 : W := mkw 0x160984c083605288 0x0582613020d814a2 0xfe0f87c387e07fff 0xbf83e1f0e1f81fff

def z745 : W := mkw 0x4bb665ce65bb2eb4 0x52ed9973996ecbad 0x2e3e60ce67e07c1c 0x8b8f983399f81f07

def z746 : W := mkw 0x0086410240000000 0x0021904090000000 0xa03ff8fff8000002 0xe80ffe3ffe000000

def z747 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xf1ce67fff81fffff 0x7c7399fffe07ffff

def z748 : W := mkw 0x0010a854af9f6b0c 0x80042a152be7dac3 0x40000000071fe31c 0x1000000001c7f8c7

def z749 : W := mkw 0xd6cde6f1e36dfbcc 0x35b379bc78db7ef3 0x0fc1e0f1e7ff8000 0xc3f0783c79ffe000

def z750 : W := mkw 0x3dbdf80116db7801 0x8f6f7e0045b6de00 0x7ffff8019ffffc03 0xdffffe0067ffff00

def z751 : W := mkw 0x0b60aea8aaaae0cc 0x42d82baa2aaab833 0x3fc1ff03f8e3e0fd 0x0ff07fc0fe38f83f

def z752 : W := mkw 0x0010a854af1d6b0c 0x00042a152bc75ac3 0xf031f8ffff1fff1e 0xfc0c7e3fffc7ffc7

def z753 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xf03ff8ffff1c7f1f 0xfc0ffe3fffc71fc7

def z754 : W := mkw 0x8b7006fd85b683c8 0x62dc01bf616da0f2 0xdff007fd87ff83e3 0xf7fc01ff61ffe0f8

def z755 : W := mkw 0x960b0583006014b0 0x2582c160c018052c 0xbe3ffffff8e01ce3 0xef8ffffffe380738

def z756 : W := mkw 0xb60b95c3936056b9 0x2d82e570e4d815ae 0xfe0f9fc39fe07fff 0xbf83e7f0e7f81fff

def z757 : W := mkw 0x36cdfefc036dfbc0 0xcdb37fbf00db7ef0 0xa00ffffc00007fe0 0x2803ffff00001ff8

def z758 : W := mkw 0x824207f3812487f8 0x209081fce04921fe 0x800007f3800003fc 0x200001fce00000ff

def z759 : W := mkw 0x0002010200000000 0x0000804080000000 0xa03ffffff8000003 0xe80ffffffe000000

def z760 : W := mkw 0x0b7006fcadb683cc 0x42dc01bf2b6da0f3 0xdff007fc07ff83ff 0xf7fc01ff01ffe0ff

def z761 : W := mkw 0x424207fee92487fc 0x509081ffba4921ff 0x800007fff80003fc 0x200001fffe0000ff

def z762 : W := mkw 0x824207ffa92487fc 0x609081ffea4921ff 0x800007fff80003fc 0x200001fffe0000ff

def z763 : W := mkw 0x2fef57ab502080c1 0x4bfbd5ead4082030 0xaffffffff80000e3 0xebfffffffe000038

def z764 : W := mkw 0x3dbd500004d31800 0x8f6f54000134c600 0x5fce000007ff9c01 0x17f3800001ffe700

def z765 : W := mkw 0x40422332200dad74 0x101088cc88036b5d 0xf1ce0732001fffff 0x7c7381cc8007ffff

def z766 : W := mkw 0x2be456a850000001 0x0af915aa14000000 0xaff1fffff8000003 0xebfc7ffffe000000

def z767 : W := mkw 0x0010805487144308 0x0004201521c510c2 0xe031f8ffff1c631e 0xf80c7e3fffc718c7

def z768 : W := mkw 0xb48ff903aa497c3c 0xad23fe40ea925f0f 0x200ff803f8007c1c 0x0803fe00fe001f07

def z769 : W := mkw 0x0200048910000001 0x0080012244000000 0xa031f8fff8000002 0xe80c7e3ffe000000

def z770 : W := mkw 0x2fffffffff1c630d 0x0bffffffffc718c3 0x4fce0700071c631d 0x13f381c001c718c7

def z771 : W := mkw 0x49f46a3c6c9fa944 0x527d1a8f1b27ea51 0x01f0783c781f8000 0x407c1e0f1e07e000

def z772 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x7ffff8cd9ffffc03 0xdffffe3367ffff00

def z773 : W := mkw 0x0010a84087186208 0x00042a1021c61882 0xe031f8ffff1c631e 0xf80c7e3fffc718c7

def z774 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0x8ff007fc07ff83e0 0xe3fc01ff01ffe0f8

def z775 : W := mkw 0x9f3984c187f25288 0x27ce613061fc94a2 0x0e3180c187e00000 0x838c603061f80000

def z776 : W := mkw 0x0f6b07ab00000000 0x03dac1eac0000000 0xaffffffff8000003 0xebfffffffe000000

def z777 : W := mkw 0x3dbdf800aedb780c 0x8f6f7e002bb6de03 0x7ffff80007fffc1f 0xdffffe0001ffff07

def z778 : W := mkw 0x0970022004928040 0x025c00880124a010 0x5ff0070007ff80e3 0xd7fc01c001ffe038

def z779 : W := mkw 0x0002010200000430 0x000080408000010c 0xfe0e070207e07fff 0xbf8381c081f81fff

def z780 : W := mkw 0x2fef57ab50010801 0x0bfbd5ead4004200 0xbffffffff8039c03 0xeffffffffe00e700

def z781 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xfff067fe67ff83e3 0xfffc19ff99ffe0f8

def z782 : W := mkw 0x0010a800ae18600c 0x00042a002b861803 0xe031f8ffff1c601e 0xf80c7e3fffc71807

def z783 : W := mkw 0x960b8583026054b0 0x2582e160c098152c 0xfe0f870207e07fff 0xbf83e1c081f81fff

def z784 : W := mkw 0x9d7b833f86d6d578 0x675ee0cfe1b5b55e 0x21ff803f801ffc1c 0x487fe00fe007ff07

def z785 : W := mkw 0x2f6916a910000001 0x0bda45aa44000000 0xaff1fffff8000003 0xebfc7ffffe000000

def z786 : W := mkw 0x06cf47a340000000 0x01b3d1e8d0000000 0xaffffffff8000003 0xebfffffffe000000

def z787 : W := mkw 0xbfef57ab50e294f1 0x6ffbd5ead438a53c 0xbffffffff8e39ce3 0xeffffffffe38e738

def z788 : W := mkw 0xffef57ab50619cf1 0x3ffbd5ead418673c 0x1fce070000e39ce1 0x07f381c00038e738

def z789 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xfff1fffc07ff83e3 0xfffc7fff01ffe0f8

def z790 : W := mkw 0x3dad5054a9c71b0c 0x8f6b54152a71c6c3 0x9fce00fff8e39f1d 0x27f3803ffe38e7c7

def z791 : W := mkw 0x249f515755b683c1 0x4927d455d56da0f0 0x700ff803ffff83e0 0x1c03fe00ffffe0f8

def z792 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xa1ce6732601ffffc 0x687399cc9807ffff

def z793 : W := mkw 0x0000000000000000 0x0000000000000000 0xe031f8fff800631e 0xf80c7e3ffe0018c7

def z794 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xfe0e070207e07fff 0x3f8381c081f81fff

def z795 : W := mkw 0x4086610260092c34 0x1021984098024b0d 0xf1ce6702601fffff 0x7c7399c09807ffff

def z796 : W := mkw 0x6f293499300dad75 0x1bca4d264c036b5d 0x5e3198cd981ffffc 0x978c66336607ffff

def z797 : W := mkw 0xb9e4d268d36056b9 0x2e79349a34d815ae 0x51f0783c7fe07ffc 0x547c1e0f1ff81fff

def z798 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xfe0f87ffffe07fff 0xbf83e1fffff81fff

def z799 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0xeffffffff800631f 0xfbfffffffe0018c7

def z800 : W := mkw 0x40d6cb66cf11ce78 0x1035b2d9b3c4739e 0x11ff9fcd9f039ce1 0x847fe7f367c0e738

def z801 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x5ffe000007fffc03 0xd7ff800001ffff00

def z802 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xde0e07c387e07ffd 0x378381f0e1f81fff

def z803 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xffce673267ffffff 0xfff399cc99ffffff

def z804 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0xfffff80207ffff1f 0xfffffe0081ffffc7

def z805 : W := mkw 0x0010a854af9f6b0c 0x80042a152be7dac3 0xe031f8ffff1fe31e 0xf80c7e3fffc7f8c7

def z806 : W := mkw 0x00008054ab04430c 0x000020152ac110c3 0xe031f8ffff00631e 0xf80c7e3fffc018c7

def z807 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xde0e07c007e07fff 0xb78381f001f81fff

def z808 : W := mkw 0x0002010200000430 0x000080408000010c 0xf1ce0702001fffff 0x7c7381c08007ffff

def z809 : W := mkw 0x40c66333700dad75 0x103198ccdc036b5d 0xf1ce6733f81fffff 0x7c7399ccfe07ffff

def z810 : W := mkw 0x0000a840ab08620c 0x00002a102ac21883 0xe031f8ffff00631e 0xf80c7e3fffc018c7

def z811 : W := mkw 0x2fed56a800000000 0x0bfb55aa00000000 0xaffffffff8000003 0xebfffffffe000000

def z812 : W := mkw 0x00100054ad14030c 0x000400152b4500c3 0xe031f8ffff1c031e 0xf80c7e3fffc700c7

def z813 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xa031f8fff81c631c 0x680c7e3ffe0718c7

def z814 : W := mkw 0x2fed56a950000001 0x0bfb55aa54000000 0x8ff1fffdf8000003 0xe3fc7fff7e000000

def z815 : W := mkw 0xb60b9dc3836056b8 0xad82e770e0d815ae 0xfe0f9fc387e07fff 0xbf83e7f0e1f81fff

def z816 : W := mkw 0x960b05c3016016b0 0x2582c170c05805ac 0xfe0e07c207e07fff 0xbf8381f081f81fff

def z817 : W := mkw 0x149de80006db7800 0x85277a0001b6de00 0x7fcfe00007fffc03 0xdff3f80001ffff00

def z818 : W := mkw 0x60c67332700dad75 0x18319ccc9c036b5d 0xf1ce7f32781fffff 0x7c739fcc9e07ffff

def z819 : W := mkw 0x1010a854afde730c 0x84042a152bf79cc3 0xe031f8fffffc631e 0xf80c7e3fffff18c7

def z820 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xfe0fffc3ffe07fff 0xbf83fff0fff81fff

def z821 : W := mkw 0x0b7006a804b280c0 0x42dc01aa012ca030 0xdff007fc07ff80e3 0xf7fc01ff01ffe038

def z822 : W := mkw 0x00866112200d2d34 0x0021984488034b4d 0xf1ce6732601fffff 0x7c7399cc9807ffff

def z823 : W := mkw 0x3fef57ab50c21001 0x8ffbd5ead4308400 0xaffffffff8e00003 0xebfffffffe380000

def z824 : W := mkw 0x0b7006a804b280c0 0x42dc01aa012ca030 0x5fc0070007ff80e1 0x17f001c001ffe038

def z825 : W := mkw 0x2ded522850000001 0x0b7b548a14000000 0xaffff8fff8000003 0xebfffe3ffe000000

def z826 : W := mkw 0xbf3994cd97f25289 0x6fce653365fc94a2 0x0e3198cd9fe00000 0x838c663367f80000

def z827 : W := mkw 0x0042032240000000 0x001080c890000000 0xa031fffff8000002 0xe80c7ffffe000000

def z828 : W := mkw 0x920285c2836056b8 0x2480a170a0d815ae 0xfe0e07c207e07fff 0xbf8381f081f81fff

def z829 : W := mkw 0x960b85cf836056b8 0x6582e173e0d815ae 0xfe0f87cf87e07fff 0xbf83e1f3e1f81fff

def z830 : W := mkw 0x3fef57ab50401001 0x0ffbd5ead4100400 0xbffffffff8e01c03 0xeffffffffe380700

def z831 : W := mkw 0x3dbdf80026db7804 0x8f6f7e0009b6de01 0x7ffff80267fffc1f 0xdffffe0099ffff07

def z832 : W := mkw 0x0010a854af3ce3cc 0x40042a152bcf38f3 0xe031f8ffff1c63fe 0xf80c7e3fffc718ff

def z833 : W := mkw 0x3dbdf8002edb7804 0x8f6f7e000bb6de01 0x7ffff8007ffffc03 0xdffffe001fffff00

def z834 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xf1f1f8ffff1fe31f 0xfc7c7e3fffc7f8c7

def z835 : W := mkw 0x0000a050a30c630c 0x0000281428c318c3 0xe031f8ffff1c631e 0xf80c7e3fffc718c7

def z836 : W := mkw 0x3dbd500004d31800 0x8f6f54000134c600 0x7ffff80007ff9c03 0xdffffe0001ffe700

def z837 : W := mkw 0x348ff90202497c30 0x8d23fe4080925f0c 0x200ff80200007c1c 0x0803fe0080001f07

def z838 : W := mkw 0x940b8142836056b8 0x2502e050a0d815ae 0xfe0f870207e07fff 0xbf83e1c081f81fff

def z839 : W := mkw 0x960b85c3d36056b9 0x2582e170f4d815ae 0xfe0f87c3ffe07fff 0xbf83e1f0fff81fff

def z840 : W := mkw 0xbfef57ab50401431 0x2ffbd5ead410050c 0x0fce070000001c01 0x03f381c000000700

def z841 : W := mkw 0x00108854af14430c 0x000422152bc510c3 0xa031f8ffff00031e 0xe80c7e3fffc000c7

def z842 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xdfc007c007ff83e3 0xb7f001f001ffe0f8

def z843 : W := mkw 0x748ff90372497c35 0x9d23fe40dc925f0d 0x200ff803f8007c1c 0x0803fe00fe001f07

def z844 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xf1cfff33f81fffff 0x7c73ffccfe07ffff

def z845 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x7ffff83c7ffffc03 0xdffffe0f1fffff00

def z846 : W := mkw 0x0012a956af1c673c 0x0004aa55abc719cf 0xf00e0702071c7fff 0x3c0381c081c71fff

def z847 : W := mkw 0x3dadf00002497800 0x0f6b7c0000925e00 0x7ffff80007fffc03 0xdffffe0001ffff00

def z848 : W := mkw 0x3dbd700004db3800 0x8f6f5c000136ce00 0x7ffe600007fffc03 0xdfff980001ffff00

def z849 : W := mkw 0x0010a854af3c638c 0x00042a152bcf18e3 0xf031f8fffffc63fe 0xfc0c7e3fffff18ff

def z850 : W := mkw 0x0b7006fcadb683cc 0x42dc01bf2b6da0f3 0xfff1ffffffff83ff 0xfffc7fffffffe0ff

def z851 : W := mkw 0x1d39a80006da7000 0x074e6a0001b69c00 0x7ffff80007fffc03 0xdffffe0001ffff00

def z852 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xfe3f9fcf9fe07fff 0xbf8fe7f3e7f81fff

def z853 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xf1fe7f3e781fffff 0x7c7f9fcf9e07ffff

def z854 : W := mkw 0xb48ff90302497c30 0xad23fe40c0925f0c 0x200ff80000007c00 0x0803fe0000001f00

def z855 : W := mkw 0xf48ff103f2497c3d 0x3d23fc40fc925f0f 0x200ff803f8007c1c 0x0803fe00fe001f07

def z856 : W := mkw 0x6fef57ab50008471 0x1bfbd5ead400211c 0x0fce0700000000e1 0x03f381c000000038

def z857 : W := mkw 0x2084500050000001 0x0821140014000000 0xa031f8fff8000002 0xe80c7e3ffe000000

def z858 : W := mkw 0x0b3004d405b60380 0x02cc0135016d80e0 0xdff007fc07ff83e3 0xf7fc01ff01ffe0f8

def z859 : W := mkw 0x3dbdf8040edb7800 0x8f6f7e0103b6de00 0x7ffff80c1ffffc03 0xdffffe0307ffff00

def z860 : W := mkw 0x2fed56a950000001 0x0bfb55aa54000000 0xaff1f8fff8000002 0xebfc7e3ffe000000

def z861 : W := mkw 0x2f29148910000001 0x0bca452244000000 0x0e31f8fdf8000000 0xc38c7e3f7e000000

def z862 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xf1ce0702001fffff 0x3c7381c08007ffff

def z863 : W := mkw 0x2fef57ab50000431 0x0bfbd5ead400010c 0xbffffffff8001ce3 0xeffffffffe000738

def z864 : W := mkw 0x001028142c1c2104 0x00040a050b070841 0xe031f8fff81c631e 0xf80c7e3ffe0718c7

def z865 : W := mkw 0x40c46230200dad74 0x1031188c08036b5d 0xf1ce6730001fffff 0x7c7399cc0007ffff

def z866 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xf1cfe7f3e01fffff 0xfc73f9fcf807ffff

def z867 : W := mkw 0x1010a854af5d7b0c 0x84042a152bd75ec3 0x40000000071c7f1c 0x1000000001c71fc7

def z868 : W := mkw 0x0be647aa40000000 0x02f991ea90000000 0xaffffffff8000003 0xebfffffffe000000

def z869 : W := mkw 0x3dbdd80006d35800 0x8f6f760001b4d600 0x5fff980007ff9c03 0xd7ffe60001ffe700

def z870 : W := mkw 0x6fef57ab50008471 0x1bfbd5ead400211c 0xaffffffff80000e3 0xebfffffffe000038

def z871 : W := mkw 0x960b85cb936056b9 0x2582e172e4d815ae 0xfe0f87cf9fe07fff 0xbf83e1f3e7f81fff

def z872 : W := mkw 0x0b7006fc8db683c8 0x42dc01bf236da0f2 0xdff007fd9fff83e3 0xf7fc01ff67ffe0f8

def z873 : W := mkw 0x9010a854af7c738c 0x24042a152bdf1ce3 0xe031f8fffffc631e 0xf80c7e3fffff18c7

def z874 : W := mkw 0x0b7006ec05b282c0 0x42dc01bb016ca0b0 0x5ff007cc07ff80e3 0xd7fc01f301ffe038

def z875 : W := mkw 0x29e4522850000001 0x0a79148a14000000 0x01f1f8fdf8000000 0xc07c7e3f7e000000

def z876 : W := mkw 0x0040022850000001 0x0010008a14000000 0xa031f8fff8000002 0xe80c7e3ffe000000

def z877 : W := mkw 0x424207fe412487f0 0x509081ff904921fc 0x800007fc000003e0 0x200001ff000000f8

def z878 : W := mkw 0x824207ff012487f0 0x609081ffc04921fc 0x800007fc000003e0 0x200001ff000000f8

def z879 : W := mkw 0x3dbdf800aedb780c 0x8f6f7e002bb6de03 0xfffff8fffffffc1f 0xfffffe3fffffff07

def z880 : W := mkw 0x0b3004d405b683c0 0x42cc0135016da0f0 0xdff007c007ff83e3 0xf7fc01f001ffe0f8

def z881 : W := mkw 0x0b6006f801a683c0 0x42d801be0069a0f0 0xdfc007f007ff83e3 0xf7f001fc01ffe0f8

def z882 : W := mkw 0x2409100110000001 0x0902440044000000 0xa031f8fff8000002 0xe80c7e3ffe000000

def z883 : W := mkw 0x1dbde00006db7800 0x076f780001b6de00 0x7fffe00007fffc03 0xdffff80001ffff00

def z884 : W := mkw 0x26cf57ab50000001 0x09b3d5ead4000000 0xa03ffffff8000002 0xe80ffffffe000000

def z885 : W := mkw 0xbf399ccd87f25288 0xefce673361fc94a2 0x0e3198cd87e00000 0x838c663361f80000

def z886 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0xae3ffffff8000000 0xab8ffffffe000000

def z887 : W := mkw 0x2fad548910000001 0x0beb552244000000 0xaffff8fff8000003 0xebfffe3ffe000000

def z888 : W := mkw 0xc24207f7e92487fc 0x309081fdfa4921ff 0x800007fff80003fc 0x200001fffe0000ff

def z889 : W := mkw 0x0b7006fc2db683c4 0x42dc01bf0b6da0f1 0xdff007fc7fff83e3 0xf7fc01ff1fffe0f8

def z890 : W := mkw 0x040b010300000000 0x0102c040c0000000 0xa03ff8fff8000002 0xe80ffe3ffe000000

def z891 : W := mkw 0x0010a810261c6104 0x00042a0409871841 0xe031f8ffff1c631e 0xf80c7e3fffc718c7

def z892 : W := mkw 0x268f558350000001 0x09a3d560d4000000 0xae3ffffff8000003 0xeb8ffffffe000000

def z893 : W := mkw 0x19b4e80006db7800 0x866d3a0001b6de00 0x7ffe600007fffc03 0xdfff980001ffff00

def z894 : W := mkw 0x024207fe012487f0 0x409081ff804921fc 0x800007fe000003fc 0x200001ff800000ff

def z895 : W := mkw 0x0970027405968340 0x025c009d0165a0d0 0xdff007fc07ff83e3 0xf7fc01ff01ffe0f8

def z896 : W := mkw 0x0b7006bc04b681c0 0x42dc01af012da070 0x5ff0073c07ff80e3 0xd7fc01cf01ffe038

def z897 : W := mkw 0x2fef57ab50830801 0x8bfbd5ead420c200 0xaffffffff8038003 0xebfffffffe00e000

def z898 : W := mkw 0x020004c001200280 0x00800130004800a0 0xdfc007c007ff83e3 0xf7f001f001ffe0f8

def z899 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xdff07ffc7fff83e3 0xf7fc1fff1fffe0f8

def z900 : W := mkw 0x69f47a346c9fa944 0x9a7d1e8d1b27ea51 0x01f0783c781f8000 0x407c1e0f1e07e000

def z901 : W := mkw 0x248d500000000000 0x0923540000000000 0xa03ff8fff8000002 0xe80ffe3ffe000000

def z902 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xfe0fe7f3e7e07fff 0xff83f9fcf9f81fff

def z903 : W := mkw 0x1010a854af5d7b0c 0x84042a152bd75ec3 0xe031f8ffff1c7f1e 0xf80c7e3fffc71fc7

def z904 : W := mkw 0x0010a854af1d6b0c 0x00042a152bc75ac3 0x50000000071fff1c 0x1400000001c7ffc7

def z905 : W := mkw 0xf48ff903e2497c3c 0xbd23fe40f8925f0f 0x200ff803e0007c1c 0x0803fe00f8001f07

def z906 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0xfffff8fc07fffc03 0xfffffe3f01ffff00

def z907 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0xfffff8c387fffc03 0xfffffe30e1ffff00

def z908 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0x0ffffffdf8000001 0xc3ffffff7e000000

def z909 : W := mkw 0x0609048100000000 0x0182412040000000 0xae31f8fff8000002 0xeb8c7e3ffe000000

def z910 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0x5ff0070007ff83e3 0xd7fc01c001ffe0f8

def z911 : W := mkw 0x4010a854afbfeffc 0x50042a152beffbff 0x5000000007fffffc 0x1400000001ffffff

def z912 : W := mkw 0xbf399cc997f25289 0xafce673265fc94a2 0x0e3198cd9fe00000 0x838c663367f80000

def z913 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xdff007ffffff83e3 0xf7fc01ffffffe0f8

def z914 : W := mkw 0x3dbdf80c06db7800 0xcf6f7e0301b6de00 0x7ffff80c07fffc03 0xdffffe0301ffff00

def z915 : W := mkw 0x00002054a90c230c 0x000008152a4308c3 0xe031f8fff81c631e 0xf80c7e3ffe0718c7

def z916 : W := mkw 0x00c4422040000000 0x0031108810000000 0xa1f1f8fff8000002 0xe87c7e3ffe000000

def z917 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xf031ffffff1c63ff 0xfc0c7fffffc718ff

def z918 : W := mkw 0x3f399ccc8ff25288 0xcfce673323fc94a2 0x0e3198cd9fe00000 0x838c663367f80000

def z919 : W := mkw 0x0000200020082004 0x0000080008020801 0xa031f8fff800601e 0xe80c7e3ffe001807

def z920 : W := mkw 0x00c46230200da944 0x0031188c08036a51 0xf1ce6732601fffff 0x7c7399cc9807ffff

def z921 : W := mkw 0x0010a814ae1c610c 0x00042a052b871843 0xa031f8fff81c601e 0xe80c7e3ffe071807

def z922 : W := mkw 0x24cf532350000001 0x0933d4c8d4000000 0xa1fffffff8000003 0xe87ffffffe000000

def z923 : W := mkw 0x5010a854afdfff7c 0x94042a152bf7ffdf 0x5000000007fffffc 0x1400000001ffffff

def z924 : W := mkw 0xbfef57ab50601081 0x2ffbd5ead4180420 0xaffffffff8e00003 0xebfffffffe380000

def z925 : W := mkw 0x748ff902ea497c3c 0x9d23fe40ba925f0f 0x200ff803f8007c1c 0x0803fe00fe001f07

def z926 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x7fcf800007fffc03 0x9ff3e00001ffff00

def z927 : W := mkw 0x0010a854af9e630c 0x00042a152be798c3 0x5000000007ffe31c 0x1400000001fff8c7

def z928 : W := mkw 0xb48ff903d2497c39 0xad23fe40f4925f0e 0x200ff803f8007c1c 0x0803fe00fe001f07

def z929 : W := mkw 0x0b7006fd15b683c1 0x42dc01bf456da0f0 0xdff007fd9fff83e3 0xf7fc01ff67ffe0f8

def z930 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xffcf87c387ffffff 0xfff3e1f0e1ffffff

def z931 : W := mkw 0x0b7006e805b20280 0x02dc01ba016c80a0 0xdff007fc07ff83e3 0xf7fc01ff01ffe0f8

def z932 : W := mkw 0x1010a854af5c730c 0x04042a152bd71cc3 0x5000000007fc7f1c 0x1400000001ff1fc7

def z933 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xfe3f87ff87e07fff 0xff8fe1ffe1f81fff

def z934 : W := mkw 0x960984c0836056b8 0x2582613020d815ae 0xfe0f87c007e07fff 0xbf83e1f001f81fff

def z935 : W := mkw 0x49f46230649fa944 0x127d188c1927ea51 0x01f06030601f8000 0x407c180c1807e000

def z936 : W := mkw 0x60c67b32600dad74 0x98319ecc98036b5d 0xf1ce7f32601fffff 0x7c739fcc9807ffff

def z937 : W := mkw 0x0b7006b804968140 0x02dc01ae0125a050 0xdff007fc07ff83e3 0xf7fc01ff01ffe0f8

def z938 : W := mkw 0x0970027405b683c0 0x425c009d016da0f0 0xdff0073007ff83e3 0xf7fc01cc01ffe0f8

def z939 : W := mkw 0x0010a854af1c673c 0x00042a152bc719cf 0x50000000071c7ffc 0x1400000001c71fff

def z940 : W := mkw 0x0002010200000430 0x000080408000010c 0xf03ffffff8007fff 0xfc0ffffffe001fff

def z941 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xdfc007fc07ff83e1 0x37f001ff01ffe0f8

def z942 : W := mkw 0x0010a854af9ee34c 0x40042a152be7b8d3 0xe031f8ffff1fe31e 0xf80c7e3fffc7f8c7

def z943 : W := mkw 0x3dbdf80086db7808 0x8f6f7e0021b6de02 0x7ffff80387fffc1f 0xdffffe00e1ffff07

def z944 : W := mkw 0x3dbdf854afdf7b0c 0x8f6f7e152bf7dec3 0x5fce000007ffff1d 0x17f3800001ffffc7

def z945 : W := mkw 0x3dbdf8008edb7808 0x8f6f7e0023b6de02 0x7ffff8019ffffc03 0xdffffe0067ffff00

def z946 : W := mkw 0x0b7006e805b282c0 0x42dc01ba016ca0b0 0xdff007c007ff83e3 0xf7fc01f001ffe0f8

def z947 : W := mkw 0x9010a854af5c773c 0x24042a152bd71dcf 0x40000000071c7f1c 0x1000000001c71fc7

def z948 : W := mkw 0x0b6006a800a280c0 0x42d801aa0028a030 0xbff1fffff8e380e3 0xeffc7ffffe38e038

def z949 : W := mkw 0x0000a854ab0c630c 0x00002a152ac318c3 0xa031f8fff800631e 0xe80c7e3ffe0018c7

def z950 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0xfffffffff81f8003 0xfffffffffe07e000

def z951 : W := mkw 0x2fef57ab50008041 0x0bfbd5ead4002010 0xbffffffff80380e3 0xeffffffffe00e038

def z952 : W := mkw 0x4042033260048574 0x101080cc9801215d 0xf1ce0732601fffff 0x7c7381cc9807ffff

def z953 : W := mkw 0x548fe10262497c34 0x1523f84098925f0d 0x200fe00260007c1c 0x0803f80098001f07

def z954 : W := mkw 0x0010a854af9e630c 0x00042a152be798c3 0xf031f8ffffffe31e 0xfc0c7e3ffffff8c7

def z955 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x7ffff803fffffc03 0xdffffe00ffffff00

def z956 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xfe3fffc387e07fff 0xff8ffff0e1f81fff

def z957 : W := mkw 0x6fef57ab50a38cf1 0x5bfbd5ead428e33c 0x1fce070000e39ce1 0x07f381c00038e738

def z958 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0x2ffff8fff8000000 0xcbfffe3ffe000000

def z959 : W := mkw 0x00102854ad1c230c 0x00040a152b4708c3 0xa031f8fff81c031e 0xe80c7e3ffe0700c7

def z960 : W := mkw 0x0000800082004008 0x0000200020801002 0xa031f8fff800601e 0xe80c7e3ffe001807

def z961 : W := mkw 0x2fef57ab50820001 0x0bfbd5ead4208000 0xbffffffff8e38003 0xeffffffffe38e000

def z962 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0x51ce6730601ffffd 0x547399cc1807ffff

def z963 : W := mkw 0x0040023000048140 0x0010008c00012050 0xdfc0073007ff83e3 0xf7f001cc01ffe0f8

def z964 : W := mkw 0x40c66b32680dad74 0x10319acc9a036b5d 0xf1ce7f32781fffff 0x7c739fcc9e07ffff

def z965 : W := mkw 0x09b4400004930800 0x026d10000124c200 0x5ffe000007ff9c03 0xd7ff800001ffe700

def z966 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xd1ce0730001fffff 0x747381cc0007ffff

def z967 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0xae0f87c387e07ffc 0xab83e1f0e1f81fff

def z968 : W := mkw 0x2fef57ab50000431 0x0bfbd5ead400010c 0x1fce070000001ce1 0x07f381c000000738

def z969 : W := mkw 0x3dbdd00006d35800 0x8f6f740001b4d600 0x7fff800007fffc03 0xdfffe00001ffff00

def z970 : W := mkw 0x3fef57ab50e398c1 0xcffbd5ead438e630 0xbffffffff8e39ce3 0xeffffffffe38e738

def z971 : W := mkw 0x6fef57ab50a38cf1 0x5bfbd5ead428e33c 0xbffffffff8e39ce3 0xeffffffffe38e738

def z972 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x7fcff80007fffc01 0x1ff3fe0001ffff00

def z973 : W := mkw 0x40866112200dad74 0x1021984488036b5d 0xf1ce6702001fffff 0x7c7399c08007ffff

def z974 : W := mkw 0x960b8dc38b6056b8 0x2582e370e2d815ae 0xfe0f9fc39fe07fff 0xbf83e7f0e7f81fff

def z975 : W := mkw 0x0b7006b804b681c0 0x42dc01ae012da070 0xdff0073007ff83e3 0xf7fc01cc01ffe0f8

def z976 : W := mkw 0x0200048000000000 0x0080012000000000 0xae31fffff8000003 0xeb8c7ffffe000000

def z977 : W := mkw 0xabb67dc385bb2eb8 0xaaed9f70e16ecbae 0x81f07fc3801f83fc 0x607c1ff0e007e0ff

def z978 : W := mkw 0x4010a854af1deb4c 0x10042a152bc77ad3 0xe031f8ffff1fe31e 0xf80c7e3fffc7f8c7

def z979 : W := mkw 0x29f47a3c2c9fa944 0xca7d1e8f0b27ea51 0x01f0783c781f8000 0x407c1e0f1e07e000

def z980 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0x71ce6700001fffff 0x5c7399c00007ffff

def z981 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0xa1fffffff8000000 0x687ffffffe000000

def z982 : W := mkw 0x0930000004920000 0x024c000001248000 0xdff0070007ff83e3 0xf7fc01c001ffe0f8

def z983 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xf1fe67fe601fffff 0xfc7f99ff9807ffff

def z984 : W := mkw 0x69f4723c749fa945 0x5a7d1c8f1d27ea51 0x01f0783c781f8000 0x407c1e0f1e07e000

def z985 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0xfffffffff80003e3 0xfffffffffe0000f8

def z986 : W := mkw 0x3dbdd00006d25000 0x0f6f740001b49400 0x7ffff80007fffc03 0xdffffe0001ffff00

def z987 : W := mkw 0x40c6433240058d70 0x103190cc9001635c 0xf1ce0732001fffff 0x7c7381cc8007ffff

def z988 : W := mkw 0x0000000000000000 0x0000000000000000 0x0031f8fdf8000000 0xc00c7e3f7e000000

def z989 : W := mkw 0x0000004081000208 0x0000001020400082 0xa031f8fff800031e 0xe80c7e3ffe0000c7

def z990 : W := mkw 0xafef57ab502004b1 0x2bfbd5ead408012c 0xaffffffff80000e3 0xebfffffffe000038

def z991 : W := mkw 0xbfef57ab50e294f1 0x6ffbd5ead438a53c 0x1fce070000e39ce1 0x07f381c00038e738

def z992 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x7fce600007fffc03 0x5ff3980001ffff00

def z993 : W := mkw 0x0040022000000000 0x0010008800000000 0xa1f1fffff8000003 0xe87c7ffffe000000

def z994 : W := mkw 0x2fef57ab50828041 0x4bfbd5ead420a010 0xaffffffff8038003 0xebfffffffe00e000

def z995 : W := mkw 0x348df80002497800 0x8d237e0000925e00 0x7fcff80007fffc03 0xdff3fe0001ffff00

def z996 : W := mkw 0xffef57ab50619cf1 0x3ffbd5ead418673c 0xbffffffff8e39ce3 0xeffffffffe38e738

def z997 : W := mkw 0x00422332200ca574 0x001088cc8803295d 0xf1ce6732601fffff 0x7c7399cc9807ffff

def z998 : W := mkw 0x00000000a800000c 0x000000002a000003 0xa031f8fff800001e 0xe80c7e3ffe000007

def z999 : W := mkw 0x7fef57ab50c39c71 0x9ffbd5ead430e71c 0xbffffffff8e39ce3 0xeffffffffe38e738

def z1000 : W := mkw 0x40d6eb76ef1def7c 0x1035baddbbc77bdf 0x51ce0700071ffffd 0x147381c001c7ffff

def z1001 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0xffffff0007ffffe3 0xffffffc001fffff8

def z1002 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0xfffffffff8007c03 0xfffffffffe001f00

def z1003 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0x5ff0073c07ff83e1 0x57fc01cf01ffe0f8

def z1004 : W := mkw 0xbfef57ab50e31cb1 0xaffbd5ead438c72c 0xbffffffff8e39ce3 0xeffffffffe38e738

def z1005 : W := mkw 0x4010a854af1deb4c 0x10042a152bc77ad3 0x40000000071fe31c 0x1000000001c7f8c7

def z1006 : W := mkw 0x2b7016fc15b683c1 0x4adc05bf056da0f0 0xdff01ffc1fff83e3 0xf7fc07ff07ffe0f8

def z1007 : W := mkw 0x0b20048800000000 0x02c8012200000000 0xae31f8fff8000002 0xeb8c7e3ffe000000

def z1008 : W := mkw 0x160b85c2036056b0 0x0582e17080d815ac 0xfe0f87c207e07fff 0xbf83e1f081f81fff

def z1009 : W := mkw 0x0010a854afbe638c 0x40042a152bef98e3 0x4000000007fc631c 0x1000000001ff18c7

def z1010 : W := mkw 0x0084600000092800 0x0021180000024a00 0x7fce600007fffc03 0xdff3980001ffff00

def z1011 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0x7e0f870007e07fff 0x9f83e1c001f81fff

def z1012 : W := mkw 0x424207f2612487f4 0x109081fc984921fd 0x800007f2600003fc 0x200001fc980000ff

def z1013 : W := mkw 0x3dad500000c31800 0x8f6b54000030c600 0xbffff8fff8e39c03 0xeffffe3ffe38e700

def z1014 : W := mkw 0x40c66336680dad74 0x103198cd9a036b5d 0xf1ce673e781fffff 0x7c7399cf9e07ffff

def z1015 : W := mkw 0xc24207ffe12487fc 0x709081fff84921ff 0x800007ffe00003fc 0x200001fff80000ff

def z1016 : W := mkw 0x8010a854af3c67bc 0x20042a152bcf19ef 0x40000000071c63fc 0x1000000001c718ff

def z1017 : W := mkw 0x025006f4053483c0 0x009401bd014d20f0 0xdff007fc07ff83e3 0xf7fc01ff01ffe0f8

def z1018 : W := mkw 0x3dadf00002cb7800 0x8f6b7c0000b2de00 0x7fcfe00007fffc03 0xdff3f80001ffff00

def z1019 : W := mkw 0x960b85c3836056b8 0x2582e170e0d815ae 0x5e0f87c187e07ffd 0x9783e1f061f81fff

def z1020 : W := mkw 0xbfef57ab506014b1 0x2ffbd5ead418052c 0xfffffffff8e07fff 0xfffffffffe381fff

def z1021 : W := mkw 0x024006a800000000 0x009001aa00000000 0xa031fffff8000002 0xe80c7ffffe000000

def z1022 : W := mkw 0x140b814283405638 0x0502e050a0d0158e 0xfe0f87c387e07fff 0xbf83e1f0e1f81fff

def z1023 : W := mkw 0x2f6b17ab50000001 0x0bdac5ead4000000 0xae31fffff8000002 0xeb8c7ffffe000000

def z1024 : W := mkw 0x748ff90242497c30 0x9d23fe4090925f0c 0x200ff80000007c00 0x0803fe0000001f00

def z1025 : W := mkw 0x1010a854affffbcc 0xc4042a152bfffef3 0xf031f8fffffffffe 0xfc0c7e3fffffffff

def z1026 : W := mkw 0x0b6006f8012483c0 0x02d801be004920f0 0xdff007fc07ff83e3 0xf7fc01ff01ffe0f8

def z1027 : W := mkw 0x69f47a3c649fa944 0xda7d1e8f1927ea51 0x01f0783c601f8000 0x407c1e0f1807e000

def z1028 : W := mkw 0x0010a854af3c638c 0x00042a152bcf18e3 0x5000000007fc63fc 0x1400000001ff18ff

def z1029 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xa031f8ffff00631c 0xa80c7e3fffc018c7

def z1030 : W := mkw 0x0084400000000000 0x0021100000000000 0xa1fff8fff8000003 0xe87ffe3ffe000000

def z1031 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x5fff980007fffc01 0x97ffe60001ffff00

def z1032 : W := mkw 0xbdbdf80186db7808 0xaf6f7e0061b6de02 0x7ffff80187fffc03 0xdffffe0061ffff00

def z1033 : W := mkw 0x09b4e800069b6800 0x026d3a0001a6da00 0x7ffff80007fffc03 0xdffffe0001ffff00

def z1034 : W := mkw 0x2dbd7000049b2800 0x0b6f5c000126ca00 0x7ffff80007fffc03 0xdffffe0001ffff00

def z1035 : W := mkw 0x1010a854afde730c 0x84042a152bf79cc3 0x4000000007fc631c 0x1000000001ff18c7

def z1036 : W := mkw 0x2fed56a950000001 0x0bfb55aa54000000 0x2ffff8fdf8000003 0xcbfffe3f7e000000

def z1037 : W := mkw 0x0b30048004b20080 0x02cc0120012c8020 0x5ff0070007ff80e3 0xd7fc01c001ffe038

def z1038 : W := mkw 0x3fef57ab50411801 0x8ffbd5ead4104600 0xaffffffff8001c03 0xebfffffffe000700

def z1039 : W := mkw 0x6fef57ab50018841 0x1bfbd5ead4006210 0xaffffffff8038003 0xebfffffffe00e000

def z1040 : W := mkw 0x0010a854af9ee34c 0x40042a152be7b8d3 0x40000000071fe31c 0x1000000001c7f8c7

def z1041 : W := mkw 0x2d29100000000000 0x0b4a440000000000 0xae31f8fff8000002 0xeb8c7e3ffe000000

def z1042 : W := mkw 0x6fef57ab50018c71 0x1bfbd5ead400631c 0xfffffffff803ffff 0xfffffffffe00ffff

def z1043 : W := mkw 0x1010a854affffbcc 0xc4042a152bfffef3 0x5000000007fffffc 0x1400000001ffffff

def z1044 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x1ffff80007ff9c01 0xc7fffe0001ffe700

def z1045 : W := mkw 0x3dbdf80816db7801 0x8f6f7e0205b6de00 0x7ffff80c1ffffc03 0xdffffe0307ffff00

def z1046 : W := mkw 0x0010a854af1ce34c 0x00042a152bc738d3 0xf031f8ffff1fe3fe 0xfc0c7e3fffc7f8ff

def z1047 : W := mkw 0xc24207fbf12487fd 0x309081fefc4921ff 0x800007fff80003fc 0x200001fffe0000ff

def z1048 : W := mkw 0x0b7006fc55b683c1 0x42dc01bf156da0f0 0xdff007fc7fff83e3 0xf7fc01ff1fffe0f8

def z1049 : W := mkw 0xd010a854af7dfffc 0x34042a152bdf7fff 0x5000000007fffffc 0x1400000001ffffff

def z1050 : W := mkw 0x29e6532a50000001 0x0a7994ca94000000 0xa1fffffff8000003 0xe87ffffffe000000

def z1051 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0x2ffff80007fffc00 0xcbfffe0001ffff00

def z1052 : W := mkw 0x29b47800049b2800 0x8a6d1e000126ca00 0x7ffe780007fffc03 0xdfff9e0001ffff00

def z1053 : W := mkw 0x020285c2832046b8 0x0080a170a0c811ae 0xfe0f87c387e07fff 0xbf83e1f0e1f81fff

def z1054 : W := mkw 0x02c647ab50000001 0x00b191ead4000000 0xa1fffffff8000003 0xe87ffffffe000000

def z1055 : W := mkw 0x0002010350000001 0x00008040d4000000 0xa031f8fff8000002 0xe80c7e3ffe000000

def z1056 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0xfff007fe07ffe3ff 0xfffc01ff81fff8ff

def z1057 : W := mkw 0x820205c3812006b8 0x20808170e04801ae 0xfe0e07c387e07fff 0xbf8381f0e1f81fff

def z1058 : W := mkw 0x7dbdf80066db7804 0x9f6f7e0019b6de01 0x7ffff80067fffc03 0xdffffe0019ffff00

def z1059 : W := mkw 0x0010a854af1ce34c 0x00042a152bc738d3 0x50000000071fe3fc 0x1400000001c7f8ff

def z1060 : W := mkw 0x0b3004cc05b20280 0x42cc0133016c80a0 0xdff007cc07ff83e3 0xf7fc01f301ffe0f8

def z1061 : W := mkw 0x40c66332600dad74 0x103198cc98036b5d 0xf1ffff32601fffff 0xfc7fffcc9807ffff

def z1062 : W := mkw 0x0010a844af18620c 0x00042a112bc61883 0xa031f8ffff00601e 0xe80c7e3fffc01807

def z1063 : W := mkw 0x69f47a38749fa945 0x9a7d1e8e1d27ea51 0x01f0783c781f8000 0x407c1e0f1e07e000

def z1064 : W := mkw 0x2fef57ab50000431 0x0bfbd5ead400010c 0xaffffffff80003ff 0xebfffffffe0000ff

def z1065 : W := mkw 0x0000a810aa0c610c 0x00002a042a831843 0xe031f8fff81c631e 0xf80c7e3ffe0718c7

def z1066 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0xffffffffffe00003 0xfffffffffff80000

def z1067 : W := mkw 0x1010a854af5c730c 0x04042a152bd71cc3 0xf031f8fffffc7f1e 0xfc0c7e3fffff1fc7

def z1068 : W := mkw 0x824207ffd12487f9 0x609081fff44921fe 0x800007fff80003fc 0x200001fffe0000ff

def z1069 : W := mkw 0x2fef57ab50a20081 0x4bfbd5ead4288020 0xaffffffff8e00003 0xebfffffffe380000

def z1070 : W := mkw 0x3dbdf80006db7800 0x8f6f7e0001b6de00 0xfffff83267fffc03 0xfffffe0c99ffff00

def z1071 : W := mkw 0x3dbdf80056db7801 0x8f6f7e0015b6de00 0x7ffff8007ffffc03 0xdffffe001fffff00

def z1072 : W := mkw 0x160b858302405430 0x0582e160c090150c 0xfe0f87c387e07fff 0xbf83e1f0e1f81fff

def z1073 : W := mkw 0x00c6632240092c30 0x003198c890024b0c 0xf1ce6732601fffff 0x7c7399cc9807ffff

def z1074 : W := mkw 0xafef57ab502004b1 0x2bfbd5ead408012c 0x0fce0700000000e1 0x03f381c000000038

def z1075 : W := mkw 0x2fef57ab50000431 0x0bfbd5ead400010c 0xaffffffff8007c1f 0xebfffffffe001f07

def z1076 : W := mkw 0x2be657ab50000001 0x0af995ead4000000 0xa1f1fffff8000002 0xe87c7ffffe000000

def z1077 : W := mkw 0x149de80006597800 0x05277a0001965e00 0x7ffff80007fffc03 0xdffffe0001ffff00

def z1078 : W := mkw 0x0920000000000000 0x0248000000000000 0xaff1f8fff8000003 0xebfc7e3ffe000000

def z1079 : W := mkw 0x9010a854affef7fc 0x64042a152bffbdff 0x5000000007fffffc 0x1400000001ffffff

def z1080 : W := mkw 0x7fef57ab50c39c71 0x9ffbd5ead430e71c 0x1fce070000e39ce1 0x07f381c00038e738

def z1081 : W := mkw 0x9010a854af7c738c 0x24042a152bdf1ce3 0x4000000007fc631c 0x1000000001ff18c7

def z1082 : W := mkw 0x2def532240000000 0x0b7bd4c890000000 0xaffffffff8000003 0xebfffffffe000000

def z1083 : W := mkw 0x424207ff712487f5 0x509081ffdc4921fd 0x800007fff80003fc 0x200001fffe0000ff

def z1084 : W := mkw 0x1d39a80006db7800 0x874e6a0001b6de00 0x7fff800007fffc03 0xdfffe00001ffff00

def z1085 : W := mkw 0x4010a854af1ce77c 0x10042a152bc739df 0x40000000071c63fc 0x1000000001c718ff

def z1086 : W := mkw 0xbfef57ab50e31cb1 0xaffbd5ead438c72c 0x1fce070000e39ce1 0x07f381c00038e738

def z1087 : W := mkw 0x1409800002405000 0x0502600000901400 0x7fcf800007fffc03 0xdff3e00001ffff00

def z1088 : W := mkw 0x4010a854af1d6f3c 0x10042a152bc75bcf 0x40000000071c7f1c 0x1000000001c71fc7

def z1089 : W := mkw 0x0000001020040104 0x0000000408010041 0xa031f8fff800031e 0xe80c7e3ffe0000c7

def z1090 : W := mkw 0x960b85c78b6056b8 0x2582e171e2d815ae 0xfe0f87cf9fe07fff 0xbf83e1f3e7f81fff

def z1091 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0x2031f8ffff1c601c 0xc80c7e3fffc71807

def z1092 : W := mkw 0x0b700efc0db683c0 0x42dc03bf036da0f0 0xdff01ffc1fff83e3 0xf7fc07ff07ffe0f8

def z1093 : W := mkw 0x6fef57ab50010c31 0x1bfbd5ead400430c 0x0fce070000001c01 0x03f381c000000700

def z1094 : W := mkw 0x00c6433240048570 0x003190cc9001215c 0xf1ce6732601fffff 0x7c7399cc9807ffff

def z1095 : W := mkw 0x3d39980006d25000 0x8f4e660001b49400 0x7fff980007fffc03 0xdfffe60001ffff00

def z1096 : W := mkw 0x0b7006fc05b683c0 0x42dc01bf016da0f0 0x1ff007fc07ff80e1 0xc7fc01ff01ffe038

def z1097 : W := mkw 0x29a4500000000000 0x0a69140000000000 0xa1f1f8fff8000002 0xe87c7e3ffe000000

def z1098 : W := mkw 0x948fe10382497c38 0x2523f840e0925f0e 0x200fe00380007c1c 0x0803f800e0001f07

def z1099 : W := mkw 0x2faf558b50000001 0x0bebd562d4000000 0xae3ff8fff8000002 0xeb8ffe3ffe000000

def z1100 : W := mkw 0x961badd7af7c77bc 0x2586eb75ebdf1def 0x5e0e070007fc7ffd 0x178381c001ff1fff

def z1101 : W := mkw 0x940b810382405438 0x2502e040e090150e 0xfe0f870387e07fff 0xbf83e1c0e1f81fff

def z1102 : W := mkw 0x2920100810000001 0x0a48040204000000 0xa031f8fff8000002 0xe80c7e3ffe000000

def z1103 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0xfe31f8fffffc631f 0xff8c7e3fffff18c7

def z1104 : W := mkw 0x4b7006fc65b683c4 0x52dc01bf196da0f1 0xdff007fc67ff83e3 0xf7fc01ff19ffe0f8

def z1105 : W := mkw 0x0b6207ab50000001 0x02d881ead4000000 0xaff1fffff8000003 0xebfc7ffffe000000

def z1106 : W := mkw 0x6fef57ab50010c31 0x1bfbd5ead400430c 0xaffffffff8001c03 0xebfffffffe000700

def z1107 : W := mkw 0x40c663224009ac70 0x103198c890026b1c 0xf1ce6702001fffff 0x7c7399c08007ffff

def z1108 : W := mkw 0x060b05c3012006b0 0x0182c170c04801ac 0xfe0f87c387e07fff 0xbf83e1f0e1f81fff

def z1109 : W := mkw 0x40c6633e600dad74 0x503198cf98036b5d 0xf1ce673e601fffff 0x7c7399cf9807ffff

def z1110 : W := mkw 0x0b7006fc85b683c8 0x42dc01bf216da0f2 0xdff007ff87ff83ff 0xf7fc01ffe1ffe0ff

def z1111 : W := mkw 0x0409000000000000 0x0102400000000000 0xae3ff8fff8000003 0xeb8ffe3ffe000000

def z1112 : W := mkw 0x0010a854af1c630c 0x00042a152bc718c3 0x8031f8ffff1c031c 0xe00c7e3fffc700c7

def z1113 : W := mkw 0x0970023c04968140 0x425c008f0125a050 0xdff0073c07ff83e3 0xf7fc01cf01ffe0f8

def z1114 : W := mkw 0x40c6633a700dad75 0x103198ce9c036b5d 0xf1ce673e781fffff 0x7c7399cf9e07ffff

def z1115 : W := mkw 0x2fef57ab50000001 0x0bfbd5ead4000000 0x8ff1fffff8000000 0xe3fc7ffffe000000

def z1116 : W := mkw 0x9f398ccd8ff25288 0x67ce633363fc94a2 0x0e3198cd9fe00000 0x838c663367f80000

def z1117 : W := mkw 0x1d39000004d21000 0x074e400001348400 0x5ffe000007ff9c03 0xd7ff800001ffe700

def z1118 : W := mkw 0x0202058300000000 0x00808160c0000000 0xa031fffff8000002 0xe80c7ffffe000000

def z1119 : W := mkw 0x2fef57ab50200081 0x0bfbd5ead4080020 0xbffffffff8e000e3 0xeffffffffe380038

def z1120 : W := mkw 0x0b7006fc25b683c4 0x42dc01bf096da0f1 0xdff007fe67ff83ff 0xf7fc01ff99ffe0ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z8,z4,z6]),(0,[z0,z7,z2,z9,z3,z4,z6]),(0,[z0,z2,z3,z4,z10,z11,z6]),(0,[z0,z7,z2,z12,z4,z11,z6])],[(0,[z13,z14,z7,z2,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z6,z15]),(0,[z0,z7,z2,z3,z4,z16,z6]),(0,[z0,z17,z7,z2,z3,z4,z6]),(0,[z0,z2,z18,z3,z4,z5,z6]),(0,[z0,z19,z2,z3,z20,z4,z6]),(0,[z0,z7,z2,z3,z4,z21,z6]),(0,[z0,z7,z2,z3,z22,z4,z6])],[(0,[z0,z7,z2,z3,z23,z4,z6]),(0,[z0,z24,z7,z2,z18,z4,z6])],[(1,[z0,z25,z7,z3,z4,z6]),(0,[z0,z7,z26,z2,z3,z4,z6]),(0,[z13,z0,z27,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z28,z6]),(0,[z0,z1,z27,z2,z3,z4,z6]),(0,[z0,z7,z29,z2,z3,z4,z6]),(0,[z0,z7,z30,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z31,z6]),(0,[z32,z13,z0,z7,z3,z4,z6]),(0,[z0,z33,z7,z2,z34,z4,z6]),(0,[z0,z35,z7,z2,z3,z4,z6])],[(0,[z36,z13,z0,z7,z3,z4,z6]),(0,[z37,z38,z0,z7,z3,z4,z6]),(0,[z0,z7,z2,z39,z3,z4,z6]),(0,[z0,z33,z7,z40,z2,z4,z6]),(0,[z0,z7,z2,z3,z6,z41,z42]),(0,[z0,z7,z43,z2,z3,z4,z6]),(0,[z0,z7,z44,z2,z3,z4,z6]),(0,[z0,z45,z7,z2,z3,z4,z6]),(0,[z46,z7,z2,z3,z4,z6,z47])],[(0,[z48,z38,z0,z7,z3,z4,z6]),(0,[z49,z0,z7,z2,z3,z4,z6]),(0,[z38,z0,z7,z50,z3,z4,z6]),(0,[z0,z7,z3,z4,z51,z6,z52]),(0,[z0,z7,z2,z3,z53,z4,z6]),(0,[z0,z7,z54,z2,z3,z4,z6])],[(0,[z0,z7,z55,z2,z3,z4,z6]),(0,[z0,z56,z7,z2,z3,z4,z6]),(1,[z0,z57,z58,z3,z4,z6]),(0,[z59,z0,z7,z2,z3,z4,z6]),(0,[z0,z60,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z61,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z62])]],
   [[(1,[z0,z19,z2,z3,z4,z42]),(0,[z0,z63,z7,z2,z4,z64,z6]),(0,[z0,z7,z2,z3,z4,z65,z6])],[(0,[z0,z7,z2,z66,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z67,z6]),(0,[z13,z0,z7,z3,z68,z4,z6]),(0,[z69,z38,z0,z7,z3,z4,z6]),(0,[z0,z7,z70,z2,z3,z4,z6]),(0,[z71,z0,z7,z2,z3,z4,z6]),(0,[z0,z33,z2,z3,z4,z5,z6])],[(0,[z0,z7,z2,z3,z72,z4,z6]),(0,[z0,z73,z7,z2,z3,z4,z6]),(0,[z38,z0,z57,z7,z3,z4,z6]),(0,[z74,z0,z75,z2,z3,z4,z6])],[(0,[z0,z76,z7,z2,z3,z4,z6]),(0,[z0,z7,z77,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z78,z6]),(0,[z38,z0,z7,z3,z4,z6,z79]),(0,[z0,z7,z80,z2,z3,z4,z6]),(0,[z81,z0,z7,z2,z82,z4,z6]),(0,[z83,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z84]),(0,[z0,z7,z2,z85,z3,z4,z6]),(1,[z0,z7,z2,z86,z12,z6]),(0,[z0,z7,z87,z2,z3,z4,z64]),(0,[z0,z7,z88,z2,z3,z4,z6])],[(0,[z13,z0,z7,z18,z3,z4,z6]),(0,[z0,z89,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z90,z6]),(0,[z0,z19,z7,z2,z3,z4,z5]),(0,[z0,z91,z7,z2,z3,z4,z6]),(0,[z0,z7,z92,z2,z3,z4,z6]),(0,[z0,z63,z7,z2,z86,z4,z6]),(0,[z93,z0,z7,z2,z3,z4,z6])],[(0,[z7,z94,z2,z3,z4,z28,z6]),(0,[z0,z7,z95,z3,z34,z4,z6]),(0,[z0,z7,z2,z3,z96,z4,z6]),(0,[z0,z7,z97,z2,z3,z4,z6])],[(1,[z0,z98,z7,z3,z4,z6]),(0,[z14,z0,z7,z2,z99,z4,z6]),(0,[z0,z7,z2,z3,z100,z4,z6]),(0,[z0,z7,z2,z3,z4,z101,z6]),(0,[z102,z0,z7,z2,z3,z4,z6])]],
   [[(0,[z0,z103,z2,z58,z3,z4,z6]),(0,[z38,z0,z104,z7,z3,z4,z6]),(0,[z105,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z106]),(0,[z0,z1,z7,z2,z3,z20,z6]),(0,[z0,z19,z104,z2,z3,z4,z6])],[(0,[z107,z7,z103,z2,z3,z4,z6]),(0,[z0,z7,z2,z108,z3,z4,z6]),(0,[z14,z107,z7,z2,z3,z4,z6]),(0,[z13,z0,z7,z2,z3,z4,z109]),(0,[z38,z0,z7,z3,z4,z110,z6]),(0,[z0,z111,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z112,z6]),(0,[z0,z113,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z114,z4,z6])],[(0,[z115,z13,z0,z7,z3,z4,z6]),(0,[z38,z0,z7,z3,z4,z116,z6]),(0,[z0,z57,z7,z117,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z118]),(0,[z0,z7,z2,z86,z12,z4,z6]),(1,[z0,z119,z2,z3,z4,z6]),(0,[z0,z120,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z121])],[(0,[z0,z7,z122,z3,z123,z4,z6])],[(1,[z124,z7,z2,z3,z4,z6])],[(0,[z81,z38,z0,z7,z3,z4,z6]),(0,[z0,z125,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z126,z4,z6]),(0,[z0,z7,z2,z3,z4,z127,z6]),(0,[z0,z63,z7,z2,z3,z128,z6]),(0,[z0,z129,z7,z2,z3,z4,z6]),(0,[z0,z7,z130,z2,z3,z4,z6])],[(0,[z0,z33,z103,z2,z3,z4,z6]),(0,[z38,z0,z7,z3,z4,z6,z52]),(0,[z38,z0,z131,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z132]),(0,[z133,z0,z7,z58,z3,z4,z6]),(0,[z0,z33,z2,z3,z20,z4,z6])],[(1,[z0,z7,z2,z134,z4,z6]),(0,[z38,z0,z7,z3,z4,z135,z6]),(0,[z38,z0,z7,z3,z136,z4,z6]),(0,[z0,z7,z87,z2,z3,z4,z15])]],
   [[(0,[z0,z137,z7,z2,z3,z4,z6]),(0,[z38,z0,z7,z3,z123,z4,z6]),(0,[z0,z7,z2,z3,z4,z138,z6]),(0,[z139,z0,z7,z2,z3,z4,z6])],[(0,[z140,z0,z7,z2,z3,z4,z6]),(0,[z0,z24,z33,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z141,z4,z6]),(0,[z0,z7,z142,z2,z3,z4,z6]),(0,[z143,z0,z7,z2,z3,z4,z6])],[(0,[z0,z144,z7,z2,z3,z4,z6]),(0,[z13,z69,z0,z7,z3,z4,z6]),(0,[z145,z38,z0,z7,z3,z4,z6]),(0,[z146,z0,z7,z2,z3,z4,z6])],[(0,[z147,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z148,z2,z3,z4,z6]),(0,[z149,z0,z7,z2,z3,z4,z6])],[(0,[z38,z0,z7,z3,z4,z6,z42]),(0,[z0,z7,z150,z2,z3,z4,z6]),(0,[z0,z104,z7,z2,z3,z4,z5]),(0,[z0,z151,z7,z2,z3,z4,z6]),(0,[z0,z152,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z153,z4,z6]),(0,[z0,z7,z2,z3,z154,z4,z6])],[(0,[z0,z7,z2,z155,z3,z4,z6]),(1,[z13,z7,z103,z3,z4,z6]),(0,[z32,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z156,z2,z3,z4,z6]),(0,[z0,z151,z7,z2,z3,z157,z6]),(0,[z0,z7,z2,z3,z4,z6,z158]),(0,[z0,z7,z2,z3,z4,z6,z159])],[(0,[z0,z7,z94,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z160,z4,z6])],[(1,[z13,z0,z7,z3,z68,z6]),(0,[z38,z0,z7,z3,z4,z6,z161]),(0,[z0,z162,z7,z2,z3,z4,z6]),(0,[z0,z2,z18,z3,z23,z4,z6]),(0,[z0,z7,z2,z3,z4,z163,z6]),(0,[z0,z164,z7,z2,z3,z4,z6])]],
   [[(0,[z165,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z34,z4,z6]),(0,[z69,z0,z7,z2,z3,z4,z28]),(0,[z0,z7,z2,z3,z61,z128,z6])],[(0,[z0,z7,z2,z166,z3,z4,z6]),(0,[z0,z107,z7,z167,z3,z4,z6]),(0,[z13,z0,z19,z7,z3,z4,z6]),(1,[z0,z7,z168,z3,z4,z6]),(0,[z69,z0,z7,z2,z3,z4,z52]),(1,[z133,z0,z117,z3,z4,z6]),(0,[z0,z1,z19,z2,z3,z4,z6])],[(0,[z48,z0,z107,z2,z3,z4,z6]),(1,[z13,z38,z7,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z6,z52]),(0,[z74,z38,z0,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z169,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z170]),(0,[z0,z171,z7,z2,z3,z4,z110])],[(0,[z0,z7,z2,z3,z172,z4,z6]),(0,[z0,z7,z173,z2,z3,z4,z6]),(0,[z0,z131,z7,z122,z2,z4,z6])],[(0,[z38,z0,z7,z3,z4,z11,z6]),(0,[z81,z7,z2,z3,z34,z4,z6]),(0,[z0,z174,z7,z2,z3,z4,z6]),(0,[z0,z24,z7,z2,z3,z4,z6]),(0,[z0,z175,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z176,z6]),(0,[z0,z7,z2,z3,z177,z4,z6]),(0,[z0,z7,z2,z3,z4,z178,z6]),(0,[z0,z179,z7,z2,z3,z4,z6]),(0,[z0,z180,z7,z2,z3,z4,z6]),(1,[z7,z181,z2,z3,z4,z6]),(0,[z0,z7,z2,z86,z3,z12,z6]),(0,[z0,z182,z7,z2,z3,z4,z6])],[(1,[z0,z7,z2,z4,z183,z6]),(0,[z0,z7,z2,z3,z4,z184,z6]),(0,[z0,z7,z185,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z186,z6])],[(0,[z0,z33,z2,z3,z23,z4,z6]),(0,[z0,z7,z2,z3,z4,z187,z6])]],
   [[(0,[z0,z25,z7,z103,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z157,z6]),(0,[z0,z7,z188,z2,z3,z4,z6]),(0,[z0,z189,z7,z2,z3,z4,z6]),(0,[z0,z7,z50,z3,z123,z4,z6]),(0,[z190,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z191]),(0,[z192,z0,z7,z2,z3,z4,z6])],[(0,[z13,z0,z0,z7,z3,z4,z6]),(0,[z13,z37,z0,z7,z3,z4,z6]),(0,[z38,z0,z7,z193,z3,z4,z6]),(0,[z194,z0,z7,z2,z3,z4,z6]),(0,[z195,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z196,z2,z3,z4,z6]),(0,[z0,z7,z197,z198,z3,z4,z6]),(0,[z0,z7,z40,z87,z2,z4,z6])],[(0,[z13,z0,z199,z2,z3,z4,z6]),(1,[z0,z75,z2,z3,z4,z6]),(0,[z0,z200,z7,z2,z3,z4,z6]),(1,[z195,z7,z2,z3,z4,z6]),(0,[z201,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z202,z4,z6]),(0,[z0,z7,z2,z3,z4,z203,z6]),(0,[z0,z7,z2,z3,z4,z6,z204])],[(0,[z38,z0,z7,z3,z205,z4,z6]),(0,[z7,z94,z2,z3,z34,z4,z6]),(1,[z0,z200,z7,z3,z4,z6]),(0,[z0,z7,z206,z2,z3,z4,z6]),(1,[z7,z2,z3,z4,z207,z6]),(0,[z0,z7,z2,z3,z208,z4,z6]),(0,[z209,z0,z7,z2,z3,z4,z6]),(0,[z0,z119,z7,z2,z3,z4,z6])],[(0,[z133,z0,z103,z2,z3,z4,z6]),(0,[z13,z0,z7,z2,z210,z4,z6]),(0,[z0,z211,z7,z3,z4,z116,z6]),(0,[z0,z57,z2,z58,z3,z4,z6])],[(0,[z0,z212,z7,z2,z3,z4,z6]),(0,[z0,z213,z7,z2,z3,z4,z6]),(0,[z0,z7,z3,z205,z4,z157,z6])],[(0,[z0,z25,z7,z2,z3,z4,z6]),(0,[z13,z0,z7,z58,z3,z4,z6]),(0,[z0,z214,z7,z2,z3,z4,z6]),(0,[z215,z38,z0,z7,z3,z4,z6]),(0,[z38,z0,z1,z7,z3,z4,z6]),(0,[z0,z24,z7,z2,z82,z4,z6]),(0,[z0,z7,z2,z3,z216,z4,z6]),(0,[z0,z7,z217,z2,z3,z4,z6])],[(0,[z0,z7,z2,z218,z3,z4,z6]),(0,[z0,z7,z2,z219,z3,z4,z6]),(0,[z0,z220,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z221,z4,z6]),(0,[z0,z7,z2,z3,z4,z222,z6]),(0,[z0,z7,z2,z3,z4,z223,z6]),(0,[z0,z120,z2,z3,z4,z6,z79])]],
   [[(0,[z38,z0,z7,z3,z4,z224,z6]),(0,[z0,z7,z225,z2,z3,z4,z6]),(0,[z0,z24,z7,z2,z4,z64,z6])],[(0,[z14,z38,z0,z7,z3,z4,z6]),(0,[z13,z0,z7,z199,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z6,z226]),(0,[z0,z7,z2,z227,z3,z4,z6]),(0,[z0,z7,z228,z2,z3,z4,z6]),(0,[z229,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z198,z3,z4,z6,z47])],[(0,[z0,z103,z2,z18,z3,z4,z6]),(0,[z230,z38,z0,z7,z3,z4,z6]),(0,[z7,z2,z3,z4,z28,z6,z52])],[(0,[z14,z0,z7,z2,z231,z4,z6]),(0,[z38,z0,z7,z3,z4,z5,z6]),(0,[z232,z38,z0,z7,z3,z4,z6]),(0,[z0,z233,z7,z2,z3,z4,z6]),(0,[z0,z7,z234,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z235,z6]),(0,[z0,z7,z2,z3,z4,z6,z236]),(0,[z0,z63,z7,z2,z4,z11,z6])],[(0,[z13,z0,z7,z237,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z238]),(0,[z0,z7,z2,z3,z4,z51,z6]),(0,[z0,z7,z239,z2,z3,z4,z6])],[(0,[z0,z98,z7,z103,z3,z4,z6]),(0,[z37,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z240,z6]),(0,[z241,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z242,z3,z4,z6]),(1,[z232,z0,z7,z2,z3,z79])],[(0,[z48,z0,z7,z2,z3,z4,z6]),(0,[z13,z0,z7,z82,z3,z4,z6]),(0,[z38,z0,z7,z3,z243,z4,z6]),(0,[z0,z24,z2,z18,z3,z4,z6]),(0,[z244,z0,z7,z2,z3,z4,z6]),(1,[z0,z7,z40,z2,z4,z15]),(0,[z0,z7,z2,z245,z3,z4,z6])],[(0,[z13,z14,z0,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z246,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z247]),(0,[z0,z7,z2,z3,z4,z248,z6])]],
   [[(1,[z0,z7,z2,z3,z68,z6]),(1,[z38,z7,z94,z3,z4,z6]),(0,[z0,z63,z33,z7,z2,z4,z6]),(0,[z0,z249,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z250,z6]),(0,[z0,z251,z7,z2,z3,z4,z6])],[(0,[z0,z252,z7,z2,z3,z4,z6]),(0,[z253,z0,z7,z2,z3,z4,z6]),(0,[z69,z0,z7,z2,z3,z4,z6])],[(0,[z13,z0,z7,z86,z3,z4,z6]),(0,[z0,z254,z7,z2,z3,z4,z6]),(0,[z255,z0,z7,z2,z3,z4,z6]),(1,[z0,z256,z2,z3,z4,z6]),(0,[z0,z7,z40,z2,z3,z61,z4]),(0,[z0,z257,z7,z2,z3,z4,z6])],[(1,[z13,z0,z7,z3,z67,z6]),(0,[z0,z7,z258,z2,z3,z4,z6]),(0,[z0,z33,z7,z2,z12,z4,z6])],[(0,[z0,z19,z2,z18,z3,z4,z6]),(1,[z0,z7,z2,z3,z4,z90]),(0,[z0,z7,z122,z50,z2,z4,z6]),(0,[z259,z0,z7,z2,z3,z4,z6]),(0,[z0,z63,z7,z40,z2,z4,z6])],[(0,[z0,z7,z2,z3,z4,z260,z6])],[(0,[z261,z38,z0,z7,z3,z4,z6]),(0,[z133,z0,z117,z2,z3,z4,z6]),(0,[z0,z262,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z263,z6]),(0,[z0,z7,z2,z3,z4,z264,z6]),(0,[z0,z63,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z265])]],
   [[(0,[z13,z0,z7,z3,z4,z128,z6]),(0,[z38,z0,z7,z3,z20,z4,z6]),(0,[z0,z7,z266,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z267,z6]),(0,[z0,z7,z2,z3,z268,z4,z6]),(0,[z269,z0,z7,z2,z3,z4,z6])],[(0,[z0,z270,z7,z2,z3,z4,z6]),(0,[z0,z271,z7,z2,z3,z4,z6]),(1,[z13,z37,z7,z3,z4,z6]),(0,[z38,z0,z7,z197,z3,z4,z6]),(0,[z0,z7,z3,z136,z4,z272,z6]),(0,[z0,z273,z7,z2,z3,z4,z6])],[(0,[z0,z274,z7,z2,z3,z4,z6]),(1,[z38,z0,z7,z3,z4,z6]),(0,[z0,z131,z7,z2,z123,z4,z6]),(0,[z0,z7,z40,z2,z4,z6,z15])],[(1,[z48,z103,z2,z3,z4,z6]),(0,[z0,z7,z95,z2,z3,z4,z6]),(0,[z275,z0,z7,z2,z3,z4,z6]),(1,[z0,z131,z7,z122,z4,z6]),(0,[z0,z7,z198,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z47])],[(1,[z0,z7,z2,z231,z4,z6]),(0,[z37,z0,z7,z2,z3,z136,z6]),(0,[z0,z276,z7,z2,z3,z4,z6]),(0,[z0,z7,z198,z2,z3,z157,z6])],[(1,[z13,z14,z7,z3,z4,z6]),(0,[z81,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z168,z3,z34,z4,z6]),(0,[z215,z0,z7,z2,z3,z4,z28]),(0,[z0,z24,z7,z2,z23,z4,z6]),(0,[z0,z7,z277,z2,z3,z4,z6])],[(0,[z215,z0,z7,z2,z3,z4,z52]),(0,[z278,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z279,z3,z4,z6]),(0,[z0,z7,z280,z2,z3,z4,z6]),(0,[z232,z0,z7,z87,z2,z3,z4])],[(0,[z0,z7,z281,z2,z3,z4,z6]),(0,[z0,z7,z2,z282,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z283,z6])]],
   [[(0,[z0,z284,z7,z2,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z64,z6]),(0,[z38,z0,z7,z3,z4,z285,z6]),(0,[z0,z7,z286,z2,z3,z4,z6]),(0,[z0,z63,z7,z2,z3,z11,z6]),(0,[z0,z7,z2,z287,z3,z4,z6])],[(0,[z0,z7,z2,z3,z288,z4,z6]),(0,[z0,z7,z3,z4,z28,z6,z84]),(0,[z0,z7,z198,z2,z3,z205,z6])],[(0,[z289,z0,z7,z2,z3,z4,z6]),(0,[z38,z0,z63,z7,z3,z4,z6]),(0,[z145,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z290,z6]),(0,[z0,z7,z2,z3,z4,z291,z6]),(0,[z232,z0,z63,z7,z2,z3,z6]),(1,[z0,z120,z2,z3,z4,z6]),(0,[z0,z292,z7,z2,z3,z4,z6])],[(1,[z0,z7,z3,z216,z4,z6]),(1,[z293,z7,z2,z3,z4,z6]),(1,[z0,z7,z294,z2,z4,z6])],[(0,[z0,z7,z295,z2,z3,z4,z6]),(0,[z296,z38,z0,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z297]),(0,[z0,z7,z197,z2,z3,z4,z6]),(0,[z0,z7,z298,z2,z3,z4,z6])],[(0,[z14,z0,z107,z2,z3,z4,z6]),(0,[z0,z7,z2,z58,z3,z4,z6]),(0,[z299,z0,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z300,z4,z6]),(0,[z0,z301,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z302,z4,z6])],[(0,[z7,z122,z181,z2,z3,z4,z6])]],
   [[(1,[z13,z0,z7,z3,z4,z226]),(0,[z0,z7,z2,z3,z4,z303,z6]),(0,[z0,z7,z304,z2,z3,z4,z6])],[(0,[z38,z0,z7,z3,z23,z4,z6]),(1,[z0,z7,z3,z4,z51,z6]),(0,[z0,z117,z2,z58,z3,z4,z6]),(0,[z0,z2,z18,z3,z20,z4,z6]),(0,[z0,z151,z7,z3,z4,z157,z6]),(0,[z0,z305,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z306,z4,z6]),(0,[z38,z0,z7,z3,z4,z28,z6]),(0,[z74,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z307,z3,z4,z6]),(0,[z0,z7,z308,z3,z4,z28,z6]),(0,[z0,z7,z2,z3,z4,z183,z6])],[(0,[z309,z13,z0,z7,z3,z4,z6]),(0,[z0,z7,z3,z310,z4,z116,z6]),(0,[z7,z2,z3,z4,z6,z236,z47])],[(0,[z311,z0,z7,z2,z3,z4,z6]),(0,[z13,z232,z0,z7,z3,z4,z6]),(0,[z0,z7,z2,z312,z3,z4,z6]),(1,[z0,z7,z87,z2,z4,z64]),(0,[z0,z7,z2,z3,z4,z6,z313])],[(0,[z0,z7,z314,z2,z3,z4,z6]),(0,[z0,z7,z2,z2,z3,z4,z6]),(0,[z13,z0,z7,z50,z3,z4,z6]),(0,[z37,z7,z94,z2,z3,z4,z6]),(0,[z0,z7,z2,z82,z3,z4,z6]),(0,[z0,z7,z2,z3,z315,z4,z6]),(0,[z0,z7,z2,z3,z4,z316,z6]),(0,[z317,z0,z7,z2,z3,z4,z6]),(0,[z0,z113,z7,z2,z3,z6,z42]),(1,[z0,z7,z198,z3,z205,z6]),(0,[z0,z7,z2,z3,z4,z318,z6])],[(0,[z319,z13,z0,z7,z3,z4,z6]),(0,[z13,z0,z7,z134,z3,z4,z6]),(0,[z38,z0,z7,z3,z61,z4,z6]),(0,[z320,z0,z7,z2,z3,z4,z6]),(0,[z0,z63,z24,z7,z2,z4,z6]),(0,[z321,z0,z7,z2,z3,z4,z6]),(1,[z0,z151,z7,z3,z157,z6]),(0,[z0,z7,z2,z3,z4,z322,z6])],[(0,[z323,z0,z7,z2,z3,z4,z6]),(0,[z0,z324,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z12,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z325])]],
   [[(0,[z0,z326,z7,z2,z3,z4,z6]),(0,[z74,z81,z7,z2,z3,z4,z6]),(0,[z0,z7,z327,z2,z3,z4,z6]),(0,[z0,z7,z328,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z329,z4,z6])],[(0,[z38,z0,z107,z7,z3,z4,z6]),(1,[z13,z0,z7,z3,z4,z6]),(0,[z13,z0,z57,z7,z3,z4,z6]),(0,[z38,z0,z125,z7,z3,z4,z6]),(0,[z69,z7,z94,z2,z3,z4,z6]),(0,[z0,z200,z7,z3,z4,z6,z52])],[(0,[z0,z7,z2,z330,z3,z4,z6]),(1,[z0,z7,z308,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z331,z6]),(1,[z0,z332,z7,z2,z4,z6]),(0,[z0,z131,z7,z2,z3,z4,z6])],[(0,[z0,z107,z2,z58,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z6,z79]),(0,[z0,z7,z333,z2,z3,z4,z6]),(0,[z0,z19,z7,z2,z3,z4,z42])],[(0,[z74,z0,z7,z2,z82,z4,z6]),(0,[z0,z7,z2,z3,z4,z334,z6]),(0,[z0,z7,z2,z3,z335,z4,z6]),(1,[z0,z336,z7,z2,z3,z6]),(0,[z0,z7,z87,z2,z4,z64,z6])],[(0,[z0,z7,z2,z3,z4,z6,z337])],[(1,[z13,z69,z7,z3,z4,z6]),(0,[z215,z0,z7,z2,z3,z4,z6]),(0,[z338,z0,z7,z2,z3,z4,z6])],[(0,[z13,z0,z104,z7,z3,z4,z6]),(0,[z0,z7,z339,z2,z3,z4,z6]),(0,[z340,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z341])]],
   [[(0,[z13,z0,z7,z3,z4,z110,z6]),(0,[z0,z7,z2,z3,z4,z342,z6]),(0,[z0,z33,z7,z2,z18,z4,z6]),(0,[z232,z0,z7,z40,z2,z3,z4])],[(0,[z36,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z343,z2,z3,z4,z6]),(0,[z344,z0,z7,z2,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z116,z6])],[(0,[z345,z0,z7,z2,z3,z4,z6]),(0,[z38,z0,z33,z7,z3,z4,z6]),(0,[z230,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z346,z4,z6]),(0,[z0,z7,z2,z3,z347,z4,z6]),(0,[z0,z19,z33,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z348])],[(0,[z0,z24,z7,z2,z34,z4,z6]),(0,[z215,z7,z2,z3,z4,z28,z6]),(1,[z0,z24,z2,z18,z4,z6]),(0,[z0,z349,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z15]),(0,[z232,z0,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z350,z6]),(0,[z0,z24,z7,z40,z2,z4,z6]),(0,[z0,z7,z351,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z352,z6])],[(0,[z13,z0,z131,z7,z3,z4,z6]),(0,[z0,z353,z7,z2,z3,z4,z6]),(0,[z0,z45,z7,z2,z3,z4,z285])],[(0,[z13,z48,z0,z7,z3,z4,z6]),(0,[z13,z0,z7,z3,z136,z4,z6]),(0,[z354,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z122,z2,z82,z4,z6]),(0,[z0,z7,z2,z3,z4,z355,z6]),(0,[z0,z27,z7,z2,z3,z110,z6]),(0,[z7,z2,z3,z4,z207,z157,z6])],[(0,[z13,z0,z7,z3,z123,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z356]),(0,[z0,z7,z2,z3,z4,z357,z6])]],
   [[(0,[z0,z7,z2,z3,z4,z6,z358])],[(1,[z0,z7,z2,z3,z4,z226]),(0,[z359,z38,z0,z7,z3,z4,z6]),(0,[z0,z7,z360,z2,z3,z4,z6]),(0,[z232,z0,z7,z2,z3,z61,z6])],[(0,[z0,z361,z7,z2,z3,z4,z6]),(0,[z0,z362,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z363,z4,z6])],[(0,[z13,z0,z7,z3,z4,z6,z42]),(0,[z0,z7,z2,z3,z4,z67,z6]),(0,[z0,z7,z2,z3,z68,z4,z6]),(0,[z0,z7,z2,z3,z364,z4,z6]),(0,[z365,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z366,z2,z3,z4,z6]),(0,[z0,z367,z7,z2,z3,z4,z6])],[(1,[z14,z107,z2,z3,z4,z6]),(1,[z0,z7,z3,z4,z6,z84]),(0,[z368,z0,z7,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z110,z6]),(0,[z0,z7,z2,z369,z3,z4,z6]),(0,[z0,z370,z7,z2,z3,z4,z6])],[(0,[z371,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z372,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z373,z4,z6]),(0,[z0,z7,z2,z3,z374,z4,z6]),(0,[z0,z7,z2,z3,z4,z90,z110]),(0,[z0,z19,z7,z2,z3,z4,z6]),(0,[z0,z7,z375,z2,z3,z4,z6])],[(0,[z261,z0,z7,z2,z3,z4,z6]),(0,[z115,z0,z7,z2,z3,z4,z6]),(0,[z13,z74,z0,z7,z3,z4,z6]),(0,[z0,z7,z376,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z377,z4,z6]),(0,[z0,z7,z378,z2,z3,z4,z6]),(0,[z379,z0,z7,z2,z3,z4,z6])],[(0,[z319,z0,z7,z2,z3,z4,z6]),(0,[z38,z0,z7,z3,z34,z4,z6]),(0,[z380,z0,z7,z2,z3,z4,z6]),(0,[z0,z381,z7,z2,z3,z4,z6]),(0,[z37,z0,z7,z2,z3,z116,z6]),(0,[z0,z7,z2,z18,z3,z4,z6]),(0,[z0,z382,z7,z2,z3,z4,z6]),(1,[z0,z7,z197,z3,z4,z285]),(0,[z0,z7,z2,z3,z61,z4,z128])]],
   [[(0,[z0,z7,z2,z3,z383,z4,z6]),(0,[z0,z7,z2,z3,z231,z4,z6]),(0,[z384,z0,z7,z2,z3,z4,z6]),(0,[z0,z27,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z385])],[(0,[z0,z7,z2,z3,z4,z6,z386]),(0,[z0,z387,z7,z2,z3,z4,z6]),(0,[z230,z0,z7,z2,z3,z136,z6]),(0,[z133,z293,z7,z2,z3,z4,z6]),(0,[z232,z0,z1,z7,z2,z3,z6]),(0,[z0,z7,z388,z2,z3,z4,z6]),(0,[z0,z256,z7,z2,z3,z4,z6])],[(1,[z0,z252,z2,z3,z4,z6]),(0,[z74,z7,z94,z2,z3,z4,z6]),(1,[z0,z211,z7,z3,z4,z6]),(0,[z0,z2,z3,z20,z4,z110,z6])],[(0,[z13,z0,z7,z3,z4,z11,z6]),(0,[z0,z7,z2,z3,z4,z389,z6]),(0,[z0,z7,z390,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z10,z6])],[(0,[z13,z230,z0,z7,z3,z4,z6]),(0,[z38,z38,z0,z7,z3,z4,z6]),(0,[z74,z0,z391,z2,z3,z4,z6]),(0,[z0,z392,z7,z2,z3,z4,z6]),(0,[z393,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z394])],[(0,[z13,z0,z7,z3,z210,z4,z6]),(0,[z13,z0,z7,z3,z4,z109,z6]),(0,[z38,z0,z7,z122,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z395])],[(0,[z0,z7,z2,z3,z4,z6,z396]),(0,[z0,z7,z2,z397,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z398,z6]),(0,[z0,z7,z399,z2,z3,z4,z6]),(0,[z400,z0,z7,z2,z3,z4,z6])],[(1,[z13,z0,z7,z3,z4,z109]),(0,[z0,z57,z7,z58,z3,z4,z6]),(0,[z0,z401,z7,z2,z3,z4,z6]),(0,[z143,z7,z122,z2,z3,z4,z6])]],
   [[(0,[z0,z7,z2,z402,z3,z4,z6]),(0,[z133,z0,z57,z2,z3,z4,z6]),(0,[z0,z403,z7,z2,z3,z4,z6]),(0,[z404,z0,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z405,z6]),(0,[z0,z7,z2,z406,z3,z4,z6]),(0,[z407,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z408,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z409]),(0,[z0,z7,z2,z410,z3,z4,z6]),(0,[z0,z131,z7,z50,z3,z4,z6]),(0,[z0,z411,z7,z2,z3,z4,z6]),(0,[z0,z7,z412,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z413]),(0,[z0,z7,z40,z2,z12,z4,z6])],[(0,[z13,z7,z2,z3,z136,z4,z6]),(0,[z13,z0,z7,z3,z205,z4,z6]),(0,[z38,z0,z7,z117,z3,z4,z6]),(0,[z0,z7,z168,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z414]),(0,[z415,z0,z7,z2,z3,z4,z6]),(0,[z232,z0,z7,z2,z86,z3,z6])],[(0,[z416,z0,z7,z2,z3,z4,z6]),(0,[z13,z74,z7,z2,z3,z4,z6]),(0,[z0,z7,z417,z2,z3,z4,z6]),(0,[z418,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z419,z2,z3,z4,z6]),(0,[z0,z7,z420,z2,z3,z4,z6])],[(0,[z296,z0,z7,z2,z3,z4,z6]),(0,[z421,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z422,z2,z3,z4,z6]),(0,[z0,z104,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z423]),(0,[z0,z7,z2,z3,z4,z6,z424]),(0,[z0,z7,z40,z2,z3,z4,z64])],[(0,[z0,z107,z2,z18,z3,z4,z6]),(0,[z13,z0,z1,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z425,z4,z6]),(0,[z0,z426,z7,z2,z3,z4,z6])],[(0,[z0,z98,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z427,z3,z4,z6]),(0,[z38,z0,z45,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z428,z4,z6])],[(0,[z0,z57,z7,z2,z3,z4,z6]),(0,[z0,z7,z429,z2,z3,z4,z6])]],
   [[(0,[z359,z13,z0,z7,z3,z4,z6]),(0,[z38,z0,z24,z7,z3,z4,z6]),(0,[z0,z7,z2,z82,z123,z4,z6]),(0,[z37,z230,z7,z2,z3,z4,z6])],[(0,[z14,z7,z94,z2,z3,z4,z6]),(0,[z13,z0,z7,z122,z3,z4,z6]),(0,[z0,z7,z430,z2,z3,z4,z6]),(0,[z38,z0,z7,z198,z3,z4,z6]),(0,[z0,z75,z7,z2,z3,z4,z6]),(0,[z431,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z197,z3,z4,z157,z6]),(0,[z0,z7,z2,z3,z4,z6,z432]),(1,[z0,z7,z433,z2,z3,z4])],[(0,[z13,z0,z7,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z434,z4,z6]),(0,[z0,z7,z2,z3,z435,z4,z6]),(0,[z0,z7,z2,z436,z3,z4,z6])],[(0,[z13,z215,z0,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z437,z6]),(0,[z0,z7,z2,z438,z3,z4,z6]),(0,[z0,z439,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z440])],[(0,[z81,z0,z7,z2,z34,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z52]),(0,[z0,z7,z2,z3,z441,z4,z6]),(0,[z442,z0,z7,z2,z3,z4,z6]),(0,[z232,z0,z7,z2,z3,z4,z79])],[(0,[z443,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z444,z3,z4,z6]),(0,[z0,z63,z7,z2,z3,z12,z6]),(0,[z0,z7,z2,z3,z4,z445,z6]),(0,[z0,z7,z2,z3,z446,z4,z6]),(0,[z0,z7,z294,z2,z4,z6,z79])],[(0,[z0,z7,z2,z3,z136,z157,z6]),(0,[z447,z0,z7,z2,z3,z4,z6]),(0,[z0,z448,z7,z2,z3,z4,z6])],[(0,[z48,z0,z103,z2,z3,z4,z6]),(0,[z38,z0,z151,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z449,z6]),(0,[z0,z7,z2,z3,z450,z4,z6]),(0,[z0,z7,z2,z451,z3,z4,z6]),(0,[z0,z7,z40,z2,z3,z4,z15]),(0,[z452,z0,z7,z2,z3,z4,z6])]],
   [[(0,[z453,z0,z7,z2,z3,z4,z6]),(1,[z0,z33,z2,z23,z4,z6]),(1,[z0,z2,z3,z4,z10,z6]),(0,[z0,z7,z2,z3,z4,z454,z6])],[(0,[z0,z7,z82,z3,z216,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z455]),(0,[z0,z7,z2,z3,z4,z4,z6]),(0,[z0,z27,z7,z2,z3,z128,z6]),(0,[z0,z7,z2,z3,z4,z456,z6]),(0,[z232,z0,z19,z7,z2,z3,z4]),(0,[z0,z7,z2,z3,z4,z457,z6])],[(0,[z0,z7,z2,z3,z4,z6,z458]),(0,[z0,z7,z2,z3,z4,z157,z6]),(0,[z0,z2,z3,z4,z6,z459,z79])],[(0,[z13,z7,z2,z237,z3,z4,z6]),(0,[z0,z1,z2,z18,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z460,z6]),(0,[z461,z0,z7,z2,z3,z4,z6])],[(0,[z0,z33,z7,z2,z82,z4,z6]),(1,[z0,z324,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z462,z4,z6]),(1,[z0,z7,z2,z4,z463,z6])],[(0,[z13,z38,z7,z2,z3,z4,z6]),(0,[z38,z0,z7,z94,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z464]),(0,[z0,z7,z2,z3,z4,z6,z465]),(0,[z0,z7,z466,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z6,z467]),(0,[z0,z7,z2,z3,z4,z468,z6]),(1,[z69,z7,z2,z3,z4,z52])],[(0,[z13,z0,z7,z3,z20,z4,z6]),(0,[z38,z0,z7,z87,z3,z4,z6]),(0,[z0,z7,z2,z3,z469,z4,z6]),(0,[z0,z470,z7,z2,z3,z4,z6])]],
   [[(1,[z0,z7,z2,z3,z4,z109]),(0,[z13,z0,z7,z197,z3,z4,z6]),(0,[z124,z0,z7,z2,z3,z4,z6]),(1,[z0,z7,z2,z3,z6,z471])],[(0,[z0,z7,z2,z3,z472,z4,z6]),(0,[z473,z38,z0,z7,z3,z4,z6]),(0,[z74,z0,z7,z2,z34,z4,z6])],[(0,[z0,z474,z7,z2,z3,z4,z6]),(1,[z13,z0,z7,z210,z4,z6]),(0,[z38,z0,z7,z3,z4,z6,z47]),(0,[z0,z7,z475,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z476]),(0,[z0,z7,z2,z3,z4,z477,z6])],[(0,[z0,z7,z2,z99,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z226]),(0,[z69,z215,z7,z2,z3,z4,z6]),(0,[z0,z7,z87,z2,z3,z4,z6])],[(0,[z478,z0,z7,z2,z3,z4,z6]),(0,[z0,z293,z7,z2,z3,z4,z6]),(0,[z0,z2,z3,z20,z4,z5,z6]),(0,[z0,z7,z2,z3,z479,z4,z6])],[(0,[z13,z133,z0,z7,z3,z4,z6]),(0,[z195,z133,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z480,z6]),(0,[z481,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z4,z183,z110,z6]),(0,[z0,z7,z482,z2,z3,z4,z6])],[(1,[z13,z7,z3,z136,z4,z6]),(0,[z0,z7,z2,z237,z3,z4,z6]),(1,[z0,z7,z483,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z484,z6]),(0,[z0,z7,z2,z3,z4,z485,z6])],[(1,[z0,z7,z2,z3,z67,z6]),(0,[z13,z0,z7,z3,z4,z285,z6]),(0,[z0,z7,z2,z3,z310,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z486]),(0,[z0,z7,z2,z3,z4,z6,z487]),(0,[z232,z0,z7,z2,z3,z6,z79])]],
   [[(0,[z488,z13,z0,z7,z3,z4,z6]),(0,[z13,z0,z7,z2,z134,z4,z6]),(0,[z0,z7,z2,z489,z3,z4,z6])],[(0,[z359,z0,z7,z2,z3,z4,z6]),(0,[z13,z0,z63,z7,z3,z4,z6]),(0,[z0,z7,z490,z2,z3,z4,z6]),(0,[z0,z7,z2,z491,z3,z4,z6]),(0,[z0,z7,z3,z4,z285,z6,z47]),(0,[z0,z7,z2,z3,z4,z6,z492])],[(0,[z0,z324,z7,z82,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z493]),(0,[z0,z19,z2,z3,z4,z6,z42]),(0,[z0,z7,z2,z3,z494,z4,z6]),(0,[z0,z7,z2,z3,z4,z495,z6])],[(0,[z0,z496,z7,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z110,z6])],[(0,[z230,z0,z7,z2,z3,z116,z6]),(0,[z0,z7,z50,z2,z123,z4,z6]),(0,[z0,z7,z2,z86,z3,z4,z6]),(0,[z0,z336,z7,z2,z3,z6,z15])],[],[(0,[z38,z0,z7,z103,z3,z4,z6]),(0,[z7,z103,z94,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z497,z4,z6]),(0,[z0,z7,z2,z498,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z499]),(0,[z0,z7,z2,z3,z4,z6,z500]),(0,[z0,z7,z2,z3,z501,z4,z6]),(0,[z0,z7,z2,z502,z3,z4,z6])],[(0,[z503,z38,z0,z7,z3,z4,z6]),(0,[z0,z7,z2,z504,z3,z4,z6]),(0,[z0,z7,z122,z2,z3,z4,z6]),(1,[z0,z63,z7,z2,z11,z6])]],
   [[(0,[z0,z7,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z505]),(0,[z13,z0,z7,z3,z23,z4,z6]),(0,[z0,z7,z483,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z506,z6]),(0,[z0,z7,z2,z3,z4,z507,z6])],[(1,[z13,z74,z7,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z28,z6]),(0,[z7,z94,z2,z237,z3,z4,z6]),(0,[z0,z508,z7,z2,z3,z4,z6])],[(0,[z7,z2,z3,z136,z4,z116,z6]),(0,[z0,z7,z509,z2,z3,z4,z6]),(0,[z0,z45,z7,z197,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z128,z6])],[(0,[z0,z7,z2,z510,z3,z4,z6]),(0,[z511,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z512,z4,z6]),(0,[z513,z0,z7,z2,z3,z4,z6]),(1,[z0,z113,z7,z2,z3,z6]),(0,[z0,z7,z2,z3,z4,z514,z6])],[(0,[z14,z0,z7,z2,z3,z4,z6]),(0,[z38,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z515,z6]),(0,[z0,z7,z308,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z516,z4,z6]),(0,[z517,z0,z7,z2,z3,z4,z6])],[(0,[z13,z0,z7,z3,z61,z4,z6]),(0,[z518,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z4,z6,z121,z79])],[(0,[z0,z7,z2,z3,z4,z6,z519]),(0,[z38,z0,z7,z3,z12,z4,z6]),(0,[z520,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z521,z6]),(0,[z0,z7,z2,z3,z522,z4,z6]),(0,[z0,z7,z2,z523,z3,z4,z6]),(0,[z0,z524,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z525]),(0,[z0,z256,z2,z3,z4,z11,z6])],[(1,[z13,z7,z237,z3,z4,z6]),(0,[z146,z38,z0,z7,z3,z4,z6]),(0,[z0,z526,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z527,z4,z6]),(1,[z7,z2,z3,z4,z6,z236]),(0,[z0,z7,z2,z4,z64,z6,z15]),(0,[z0,z7,z2,z3,z4,z6,z471])]],
   [[(0,[z13,z0,z107,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z528,z6]),(0,[z0,z7,z2,z3,z205,z136,z6]),(0,[z0,z529,z7,z2,z3,z4,z6])],[(0,[z530,z0,z7,z2,z3,z4,z6]),(1,[z0,z199,z2,z3,z4,z6]),(0,[z38,z0,z7,z40,z3,z4,z6]),(0,[z74,z7,z2,z82,z3,z4,z6]),(0,[z0,z7,z2,z531,z3,z4,z6]),(0,[z0,z7,z2,z3,z532,z4,z6]),(0,[z0,z7,z2,z3,z4,z533,z6]),(0,[z0,z7,z2,z3,z534,z4,z6]),(0,[z0,z7,z294,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z28,z47]),(0,[z0,z7,z2,z3,z4,z535,z6]),(0,[z0,z7,z2,z536,z3,z4,z6]),(0,[z0,z7,z537,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z64,z6])],[(1,[z0,z7,z2,z210,z4,z6]),(0,[z0,z7,z538,z2,z3,z4,z6]),(0,[z133,z38,z0,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z539,z6]),(0,[z0,z540,z7,z2,z3,z4,z6]),(0,[z0,z119,z2,z3,z4,z6,z15])],[(1,[z37,z7,z2,z3,z116,z6]),(0,[z0,z7,z2,z3,z541,z4,z6]),(0,[z0,z45,z7,z2,z3,z4,z47]),(0,[z0,z7,z197,z2,z3,z4,z285]),(0,[z232,z0,z7,z502,z3,z4,z6]),(0,[z542,z0,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z543,z3,z4,z6]),(0,[z0,z7,z544,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z545,z4,z6]),(0,[z0,z104,z7,z2,z3,z4,z42]),(0,[z0,z7,z2,z3,z546,z4,z6])],[(0,[z0,z107,z7,z2,z3,z4,z6]),(0,[z0,z547,z7,z2,z3,z4,z6]),(0,[z0,z548,z7,z2,z3,z4,z6])],[(0,[z309,z0,z7,z2,z3,z4,z6]),(0,[z0,z549,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z550,z6]),(0,[z0,z7,z2,z3,z4,z6,z41]),(0,[z0,z7,z2,z3,z4,z6,z551])]],
   [[(0,[z0,z7,z2,z3,z4,z552,z6]),(0,[z553,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z554])],[(0,[z0,z33,z107,z2,z3,z4,z6]),(0,[z13,z0,z33,z7,z3,z4,z6]),(0,[z488,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z555,z3,z4,z6]),(0,[z133,z0,z7,z117,z3,z4,z6]),(0,[z0,z1,z33,z2,z3,z4,z6]),(0,[z0,z7,z181,z2,z3,z4,z6])],[(0,[z14,z0,z103,z2,z3,z4,z6]),(0,[z38,z0,z7,z3,z4,z6,z15]),(0,[z0,z7,z2,z3,z4,z556,z6]),(0,[z0,z1,z7,z2,z3,z110,z6]),(0,[z0,z7,z2,z3,z557,z4,z6])],[(1,[z215,z7,z2,z3,z4,z28]),(0,[z0,z558,z7,z2,z3,z4,z6])],[(0,[z38,z0,z27,z7,z3,z4,z6]),(0,[z0,z7,z559,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z560,z6]),(0,[z0,z7,z50,z2,z3,z4,z6]),(0,[z0,z7,z2,z561,z3,z4,z6])],[(1,[z0,z7,z2,z3,z4,z6]),(1,[z0,z104,z2,z3,z4,z5]),(0,[z0,z7,z2,z86,z3,z128,z6])],[],[(0,[z0,z7,z2,z3,z562,z4,z6]),(1,[z81,z7,z2,z34,z4,z6]),(0,[z0,z7,z2,z3,z4,z563,z6]),(0,[z0,z7,z2,z564,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z207,z6])]],
   [[(0,[z0,z7,z2,z134,z3,z4,z6]),(0,[z0,z7,z2,z565,z3,z4,z6]),(0,[z0,z7,z2,z566,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z463,z6])],[(0,[z13,z0,z7,z2,z3,z68,z6]),(0,[z0,z7,z2,z3,z567,z4,z6])],[(0,[z0,z7,z193,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z42]),(0,[z568,z0,z7,z2,z3,z4,z6])],[(0,[z0,z569,z7,z2,z3,z4,z6])],[(0,[z13,z0,z252,z7,z3,z4,z6]),(0,[z0,z1,z7,z2,z3,z4,z6]),(1,[z0,z7,z50,z123,z4,z6]),(0,[z0,z570,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z571,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z79])],[(0,[z13,z0,z7,z3,z34,z4,z6]),(0,[z38,z0,z7,z18,z3,z4,z6]),(0,[z0,z211,z7,z2,z3,z4,z6])],[(0,[z69,z7,z2,z3,z4,z6,z52])]],
   [[(0,[z0,z7,z117,z2,z3,z4,z6]),(0,[z0,z572,z7,z2,z3,z4,z6]),(0,[z0,z104,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z6,z573]),(0,[z46,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z574]),(0,[z0,z7,z40,z2,z3,z4,z6])],[(0,[z473,z0,z7,z2,z3,z4,z6]),(1,[z74,z7,z2,z82,z4,z6]),(0,[z0,z27,z2,z3,z20,z4,z6]),(0,[z0,z575,z7,z2,z3,z4,z6])],[(0,[z576,z13,z0,z7,z3,z4,z6]),(1,[z0,z7,z95,z3,z4,z6]),(0,[z0,z7,z391,z2,z3,z4,z6]),(0,[z577,z0,z7,z2,z3,z4,z6]),(0,[z578,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z110,z6]),(0,[z0,z171,z7,z2,z3,z4,z6]),(0,[z0,z7,z579,z2,z3,z4,z6]),(0,[z0,z336,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z6,z580]),(0,[z13,z38,z0,z7,z3,z4,z6]),(0,[z581,z38,z0,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z116,z6]),(0,[z0,z7,z582,z2,z3,z4,z6]),(0,[z0,z7,z433,z2,z3,z4,z6]),(0,[z0,z7,z583,z2,z3,z4,z6])],[(0,[z165,z13,z0,z7,z3,z4,z6]),(0,[z38,z7,z94,z2,z3,z4,z6]),(0,[z0,z584,z7,z2,z3,z4,z6]),(0,[z0,z27,z7,z2,z3,z20,z6]),(0,[z0,z7,z2,z3,z585,z4,z6])],[(0,[z0,z7,z2,z3,z4,z586,z6]),(0,[z0,z33,z7,z2,z3,z4,z6])],[(0,[z0,z7,z587,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z588]),(0,[z0,z7,z2,z3,z589,z4,z6])],[(0,[z133,z0,z107,z2,z3,z4,z6]),(0,[z0,z590,z7,z2,z3,z4,z6]),(0,[z232,z0,z104,z7,z2,z3,z4]),(0,[z0,z7,z591,z2,z3,z4,z6])]],
   [[(0,[z0,z7,z2,z167,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z135,z6]),(0,[z0,z7,z2,z3,z136,z4,z6]),(0,[z592,z0,z7,z2,z3,z4,z6])],[(0,[z13,z0,z7,z117,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z593]),(0,[z0,z7,z2,z3,z4,z594,z6]),(0,[z0,z7,z2,z3,z123,z4,z6]),(0,[z0,z7,z2,z595,z3,z4,z6])],[(0,[z0,z7,z2,z3,z596,z4,z6]),(0,[z0,z7,z597,z2,z3,z4,z6]),(0,[z0,z7,z198,z3,z205,z4,z6]),(0,[z0,z7,z2,z3,z4,z485,z11]),(0,[z0,z7,z87,z2,z3,z61,z4])],[(1,[z46,z7,z2,z3,z4,z6]),(0,[z232,z0,z7,z2,z3,z4,z128])],[(0,[z0,z7,z598,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z599]),(1,[z230,z7,z2,z3,z136,z6]),(0,[z0,z7,z2,z600,z3,z4,z6])],[(0,[z13,z0,z45,z7,z3,z4,z6]),(0,[z38,z0,z7,z427,z3,z4,z6]),(0,[z0,z601,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z42])],[(1,[z13,z0,z199,z3,z4,z6]),(0,[z0,z7,z602,z2,z3,z4,z6]),(0,[z0,z7,z603,z2,z3,z4,z6]),(0,[z0,z604,z7,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z605,z15])],[(0,[z503,z0,z7,z2,z3,z4,z6]),(0,[z13,z0,z24,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z606,z4,z6]),(0,[z0,z7,z607,z2,z3,z4,z6]),(0,[z0,z7,z608,z2,z3,z4,z6])]],
   [[(0,[z13,z0,z7,z198,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z161]),(0,[z0,z7,z483,z3,z136,z4,z6])],[(1,[z13,z7,z3,z4,z28,z6]),(0,[z0,z33,z7,z2,z4,z64,z6])],[(0,[z0,z7,z2,z3,z4,z609,z6]),(0,[z13,z7,z2,z3,z34,z4,z6]),(0,[z38,z0,z19,z7,z3,z4,z6]),(0,[z0,z610,z7,z2,z3,z4,z6]),(0,[z0,z7,z611,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z612,z6]),(0,[z7,z94,z2,z3,z136,z4,z6]),(0,[z0,z7,z2,z3,z613,z4,z6]),(0,[z0,z7,z2,z3,z205,z116,z6]),(0,[z0,z7,z2,z3,z4,z272,z6]),(0,[z0,z7,z2,z3,z4,z614,z6])],[(0,[z0,z7,z2,z615,z3,z4,z6]),(0,[z0,z7,z2,z3,z616,z4,z6]),(0,[z0,z7,z617,z2,z3,z4,z6]),(0,[z0,z7,z618,z2,z3,z4,z6])],[(0,[z13,z0,z7,z2,z3,z67,z6]),(0,[z0,z7,z2,z3,z4,z52,z47]),(0,[z0,z1,z7,z2,z3,z128,z6]),(0,[z0,z332,z7,z2,z4,z110,z6]),(0,[z0,z7,z2,z3,z4,z11,z6]),(0,[z0,z7,z2,z12,z4,z64,z6]),(0,[z619,z0,z7,z2,z3,z4,z6])],[(0,[z13,z0,z151,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z605])],[(0,[z0,z7,z199,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z210,z4,z6]),(0,[z0,z7,z2,z3,z4,z109,z6]),(1,[z0,z391,z2,z3,z4,z6]),(0,[z0,z620,z7,z2,z3,z4,z6]),(0,[z0,z621,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z459])]],
   [[(0,[z0,z7,z2,z622,z3,z4,z6]),(0,[z0,z7,z2,z34,z123,z4,z6])],[(0,[z38,z0,z7,z3,z4,z157,z6]),(0,[z0,z7,z623,z2,z3,z4,z6]),(0,[z124,z7,z2,z3,z4,z157,z6])],[(0,[z13,z13,z0,z7,z3,z4,z6]),(0,[z38,z0,z0,z7,z3,z4,z6]),(0,[z624,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z625,z6]),(0,[z0,z7,z626,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z627,z6])],[(0,[z576,z0,z7,z2,z3,z4,z6]),(0,[z133,z0,z7,z2,z3,z4,z6]),(1,[z0,z7,z2,z3,z6,z41]),(0,[z0,z7,z2,z3,z4,z628,z6])],[(0,[z629,z0,z7,z2,z3,z4,z6]),(0,[z13,z0,z7,z94,z3,z4,z6]),(0,[z0,z7,z630,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z205,z4,z6]),(0,[z0,z7,z2,z3,z631,z4,z6])],[(1,[z0,z7,z2,z99,z4,z6]),(0,[z0,z632,z7,z2,z3,z4,z6]),(0,[z0,z7,z633,z2,z3,z4,z6]),(0,[z0,z24,z7,z2,z12,z4,z6]),(0,[z0,z7,z2,z3,z4,z634,z6])],[(0,[z13,z0,z7,z87,z3,z4,z6]),(0,[z0,z7,z122,z2,z34,z4,z6]),(0,[z0,z635,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z636,z6])],[(0,[z38,z0,z7,z58,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z6]),(0,[z0,z637,z7,z2,z3,z4,z6]),(0,[z0,z151,z7,z2,z3,z205,z6])]],
   [[(0,[z0,z7,z2,z3,z4,z638,z6]),(0,[z0,z7,z2,z3,z4,z285,z28]),(0,[z0,z7,z2,z3,z4,z639,z6]),(0,[z0,z7,z2,z3,z4,z640,z6]),(0,[z0,z641,z7,z2,z3,z4,z6]),(1,[z0,z7,z2,z3,z61,z128])],[(0,[z14,z48,z7,z2,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z6,z47]),(0,[z0,z7,z2,z3,z4,z224,z6]),(0,[z0,z7,z2,z3,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z285,z52]),(0,[z0,z642,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z643,z6]),(0,[z0,z7,z2,z3,z6,z471,z15])],[(0,[z0,z7,z2,z3,z4,z644,z6]),(0,[z0,z645,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z4,z463,z6,z42]),(0,[z0,z646,z7,z2,z3,z4,z6]),(0,[z0,z647,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z648,z6]),(0,[z0,z107,z7,z26,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z649]),(0,[z0,z7,z2,z3,z650,z4,z6]),(0,[z0,z7,z651,z2,z3,z4,z6])],[(0,[z13,z69,z7,z2,z3,z4,z6]),(0,[z0,z652,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z653,z4,z6]),(0,[z0,z7,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z654,z4,z6])],[(1,[z0,z7,z167,z3,z4,z6]),(0,[z38,z0,z7,z237,z3,z4,z6]),(0,[z0,z7,z3,z4,z157,z6,z47]),(0,[z0,z7,z2,z3,z61,z4,z79])],[(0,[z48,z7,z103,z2,z3,z4,z6]),(0,[z13,z7,z103,z2,z3,z4,z6]),(0,[z0,z33,z7,z2,z23,z4,z6]),(0,[z0,z7,z2,z3,z4,z655,z6]),(0,[z656,z0,z7,z2,z3,z4,z6]),(1,[z0,z7,z2,z4,z6,z121])],[(0,[z38,z0,z7,z82,z3,z4,z6]),(0,[z0,z7,z2,z3,z243,z4,z6]),(0,[z0,z657,z7,z2,z3,z4,z6]),(0,[z0,z19,z7,z2,z3,z61,z4]),(0,[z0,z7,z658,z2,z4,z6,z42]),(0,[z0,z7,z659,z2,z3,z4,z6])]],
   [[(0,[z0,z7,z2,z3,z4,z660,z6]),(0,[z0,z131,z7,z122,z3,z4,z6]),(0,[z0,z661,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z86,z3,z11,z6])],[(0,[z230,z7,z2,z3,z136,z4,z6]),(1,[z0,z7,z658,z2,z4,z6]),(0,[z662,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z663,z6])],[(1,[z0,z7,z26,z3,z4,z6]),(0,[z13,z0,z7,z2,z3,z4,z226])],[(0,[z38,z0,z7,z86,z3,z4,z6]),(0,[z0,z664,z7,z2,z3,z4,z6]),(0,[z665,z0,z7,z2,z3,z4,z6]),(0,[z0,z666,z7,z2,z3,z4,z6]),(0,[z0,z667,z7,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z6,z605])],[(0,[z0,z668,z7,z2,z3,z4,z6]),(0,[z13,z81,z0,z7,z3,z4,z6]),(0,[z7,z2,z82,z3,z34,z4,z6]),(1,[z0,z2,z3,z4,z6,z459])],[(0,[z13,z0,z7,z103,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z669]),(0,[z0,z7,z2,z3,z4,z670,z6])],[(1,[z13,z7,z3,z34,z4,z6]),(0,[z0,z671,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z672,z4,z6]),(0,[z232,z0,z7,z608,z3,z4,z6])],[(0,[z0,z7,z673,z2,z3,z4,z6]),(0,[z674,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z675,z6]),(0,[z0,z7,z2,z3,z128,z6,z79])]],
   [[(1,[z0,z7,z3,z4,z272,z6]),(0,[z0,z7,z676,z2,z3,z4,z6]),(0,[z0,z7,z197,z3,z4,z285,z6]),(0,[z0,z7,z2,z3,z4,z677,z6])],[(0,[z0,z7,z103,z2,z3,z4,z6]),(0,[z38,z0,z7,z3,z4,z128,z6]),(0,[z0,z678,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z20,z4,z6]),(1,[z0,z7,z2,z3,z4,z485])],[(0,[z0,z679,z7,z2,z3,z4,z6]),(0,[z38,z0,z7,z3,z512,z4,z6])],[(0,[z13,z0,z7,z2,z3,z4,z6]),(0,[z13,z0,z252,z2,z3,z4,z6]),(0,[z13,z37,z7,z2,z3,z4,z6]),(0,[z354,z38,z0,z7,z3,z4,z6]),(0,[z581,z0,z7,z2,z3,z4,z6]),(0,[z0,z7,z680,z2,z3,z4,z6]),(0,[z0,z7,z2,z681,z3,z4,z6]),(1,[z0,z45,z7,z3,z4,z47]),(0,[z0,z45,z7,z3,z4,z6,z47]),(0,[z0,z7,z197,z2,z3,z4,z47])],[(0,[z0,z332,z7,z2,z3,z4,z6]),(0,[z682,z0,z7,z2,z3,z4,z6]),(0,[z0,z683,z7,z2,z3,z4,z6]),(0,[z0,z7,z684,z2,z3,z4,z6])],[(0,[z13,z0,z7,z3,z12,z4,z6])],[(0,[z0,z7,z2,z3,z685,z4,z6]),(0,[z0,z686,z7,z2,z3,z4,z6]),(0,[z0,z104,z7,z2,z3,z61,z4])],[(1,[z0,z7,z3,z310,z4,z6]),(0,[z232,z0,z27,z7,z2,z3,z6]),(1,[z143,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z6,z687]),(0,[z0,z7,z433,z2,z3,z4,z11])]],
   [[(0,[z13,z0,z7,z40,z3,z4,z6]),(0,[z13,z7,z2,z3,z4,z28,z6]),(0,[z0,z7,z2,z3,z4,z688,z6]),(0,[z0,z7,z689,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z690,z6]),(0,[z0,z7,z2,z3,z691,z4,z6])],[(0,[z0,z692,z7,z2,z3,z4,z6]),(0,[z38,z0,z7,z3,z4,z64,z6]),(0,[z693,z0,z7,z2,z3,z4,z6]),(0,[z0,z151,z7,z198,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z285,z6])],[(1,[z13,z0,z252,z3,z4,z6]),(0,[z37,z7,z2,z3,z4,z116,z6]),(0,[z0,z7,z2,z3,z694,z4,z6])],[(0,[z0,z7,z2,z3,z4,z695,z6]),(0,[z0,z7,z658,z2,z3,z4,z6]),(0,[z0,z696,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z697,z4,z6]),(0,[z0,z7,z698,z2,z3,z4,z6])],[(0,[z0,z699,z7,z2,z3,z4,z6]),(0,[z0,z700,z7,z2,z3,z4,z6]),(1,[z0,z7,z608,z3,z4,z6])],[(0,[z0,z0,z7,z2,z3,z4,z6]),(1,[z13,z0,z7,z134,z4,z6]),(0,[z0,z7,z2,z3,z116,z157,z6]),(0,[z0,z7,z2,z3,z4,z6,z701]),(0,[z702,z0,z7,z2,z3,z4,z6]),(1,[z0,z171,z7,z2,z3,z4]),(1,[z0,z7,z502,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z703,z6]),(0,[z0,z7,z2,z3,z4,z704,z6]),(0,[z0,z7,z2,z3,z4,z6,z705]),(0,[z706,z0,z7,z2,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z13,z0,z7,z134,z4,z109]),(0,[z13,z700,z7,z3,z4,z6]),(0,[z13,z548,z7,z3,z4,z6]),(0,[z13,z0,z7,z658,z4,z6]),(0,[z707,z7,z2,z3,z4,z6]),(0,[z708,z7,z2,z3,z4,z6]),(0,[z0,z709,z7,z3,z4,z6]),(0,[z0,z336,z7,z40,z2,z4]),(0,[z0,z710,z7,z2,z4,z6])],[(0,[z13,z252,z103,z3,z4,z6]),(0,[z0,z7,z2,z711,z4,z6]),(0,[z13,z7,z3,z4,z6,z84]),(0,[z0,z712,z2,z3,z4,z6])],[(0,[z13,z14,z107,z3,z4,z6]),(0,[z0,z7,z713,z3,z4,z6]),(0,[z7,z2,z3,z136,z67,z6]),(0,[z0,z7,z3,z205,z67,z6]),(0,[z0,z714,z2,z3,z4,z6]),(0,[z74,z324,z7,z82,z4,z6]),(0,[z0,z119,z2,z4,z64,z6])],[(0,[z13,z0,z7,z3,z68,z6]),(0,[z13,z7,z210,z34,z4,z6]),(0,[z0,z7,z2,z3,z715,z6]),(0,[z0,z7,z3,z4,z716,z6])],[(0,[z0,z7,z2,z99,z4,z6]),(0,[z147,z7,z2,z34,z4,z6]),(0,[z232,z0,z2,z3,z459,z79])],[(0,[z0,z717,z2,z3,z4,z6]),(0,[z0,z7,z718,z3,z4,z6]),(0,[z133,z0,z117,z3,z4,z6]),(0,[z0,z719,z7,z3,z4,z6])],[(0,[z48,z38,z103,z3,z4,z6]),(0,[z13,z7,z108,z3,z4,z6]),(0,[z0,z7,z2,z3,z6,z720]),(0,[z7,z2,z3,z4,z6,z721]),(0,[z195,z7,z58,z3,z4,z6]),(0,[z0,z19,z2,z4,z463,z42])],[(0,[z13,z0,z7,z134,z67,z6]),(0,[z13,z7,z3,z315,z4,z6]),(0,[z13,z0,z7,z3,z4,z90]),(0,[z0,z722,z2,z3,z4,z6]),(0,[z0,z723,z7,z3,z4,z6]),(0,[z0,z7,z724,z3,z4,z6]),(0,[z0,z725,z2,z3,z4,z6]),(0,[z726,z0,z7,z3,z4,z6]),(0,[z0,z120,z294,z2,z4,z6])]],
   [[(0,[z13,z69,z7,z3,z68,z6]),(0,[z13,z354,z7,z3,z4,z109]),(0,[z0,z727,z7,z2,z3,z6]),(0,[z0,z332,z7,z2,z4,z90]),(0,[z0,z7,z728,z3,z4,z6]),(0,[z729,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z730]),(0,[z0,z7,z3,z4,z6,z731]),(0,[z13,z199,z3,z34,z4,z6]),(0,[z38,z0,z391,z3,z4,z6]),(0,[z732,z0,z7,z3,z4,z6]),(0,[z38,z7,z3,z208,z4,z6]),(0,[z0,z33,z2,z141,z4,z6]),(0,[z0,z733,z2,z3,z4,z6])],[(0,[z13,z7,z3,z126,z4,z6]),(0,[z74,z391,z2,z82,z4,z6]),(0,[z0,z7,z2,z4,z183,z6])],[(0,[z0,z7,z2,z3,z734,z6]),(0,[z0,z7,z2,z735,z4,z6]),(0,[z13,z581,z7,z3,z4,z6]),(0,[z13,z7,z3,z4,z6,z132]),(0,[z13,z572,z7,z3,z4,z6]),(0,[z7,z2,z3,z4,z28,z297]),(0,[z0,z33,z366,z2,z4,z6]),(0,[z0,z736,z2,z3,z4,z6])],[(0,[z0,z7,z167,z3,z4,z6]),(0,[z7,z737,z103,z3,z4,z6]),(0,[z0,z63,z7,z2,z738,z6])],[(0,[z0,z7,z739,z3,z4,z6]),(0,[z32,z0,z7,z210,z4,z6]),(0,[z13,z0,z740,z3,z4,z6]),(0,[z195,z38,z7,z3,z4,z6]),(0,[z0,z741,z2,z3,z4,z6]),(0,[z0,z7,z2,z4,z6,z121])],[(0,[z195,z7,z2,z3,z4,z6]),(0,[z13,z0,z722,z3,z4,z6]),(0,[z13,z0,z714,z3,z4,z6]),(0,[z13,z7,z3,z742,z4,z6]),(0,[z195,z252,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z743]),(0,[z69,z7,z3,z4,z51,z52]),(1,[z232,z0,z120,z2,z3])],[(0,[z0,z7,z744,z2,z3,z4]),(0,[z13,z0,z7,z231,z4,z6]),(0,[z13,z38,z7,z3,z68,z6]),(0,[z309,z0,z7,z3,z4,z226]),(0,[z7,z2,z3,z4,z207,z6]),(0,[z0,z2,z3,z4,z745,z6]),(0,[z0,z746,z7,z3,z4,z6]),(0,[z0,z131,z7,z728,z4,z6])]],
   [[(0,[z13,z0,z7,z3,z747,z6]),(0,[z13,z7,z181,z3,z4,z6]),(0,[z296,z0,z7,z427,z4,z6]),(0,[z0,z1,z2,z3,z264,z6]),(0,[z0,z7,z658,z2,z4,z6]),(0,[z0,z1,z583,z2,z3,z6]),(0,[z0,z63,z7,z433,z2,z3]),(0,[z0,z336,z7,z40,z2,z15]),(0,[z0,z748,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z749,z79])],[(0,[z0,z7,z197,z3,z4,z109]),(0,[z38,z7,z3,z4,z6,z236]),(0,[z215,z7,z3,z4,z28,z84]),(0,[z0,z2,z3,z745,z110,z6])],[(0,[z0,z7,z3,z4,z109,z226]),(0,[z13,z81,z7,z34,z4,z6]),(0,[z13,z7,z3,z4,z6,z159]),(0,[z0,z7,z2,z750,z4,z6]),(0,[z0,z7,z2,z3,z128,z265])],[(0,[z48,z751,z2,z3,z4,z6]),(0,[z752,z7,z2,z3,z4,z6]),(0,[z753,z7,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z754,z6])],[(0,[z13,z7,z3,z4,z755,z6]),(0,[z0,z119,z2,z3,z6,z471])],[(0,[z13,z7,z3,z34,z4,z6]),(0,[z0,z324,z7,z134,z4,z6]),(0,[z37,z7,z3,z310,z116,z6]),(0,[z0,z7,z2,z3,z4,z756]),(1,[z0,z2,z757,z4,z6]),(0,[z0,z7,z2,z4,z758,z6]),(0,[z759,z0,z7,z3,z4,z6])],[(0,[z503,z0,z125,z3,z4,z6]),(0,[z38,z0,z760,z3,z4,z6]),(0,[z38,z0,z256,z3,z4,z6]),(0,[z0,z7,z2,z4,z738,z6])],[(0,[z0,z7,z2,z4,z761,z6]),(0,[z0,z7,z2,z4,z762,z6]),(0,[z0,z7,z763,z3,z4,z6]),(0,[z13,z7,z3,z169,z4,z6]),(0,[z13,z7,z122,z34,z4,z6]),(0,[z0,z7,z3,z4,z272,z6]),(0,[z0,z7,z2,z764,z4,z6]),(0,[z0,z7,z2,z3,z765,z6]),(0,[z0,z666,z33,z2,z4,z6])]],
   [[(0,[z0,z7,z766,z3,z4,z6]),(0,[z13,z46,z7,z3,z4,z226]),(0,[z13,z7,z3,z172,z4,z6]),(0,[z0,z7,z197,z3,z67,z6]),(0,[z0,z75,z2,z82,z4,z6]),(0,[z767,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z485])],[(0,[z0,z7,z2,z134,z4,z109]),(0,[z0,z2,z3,z4,z6,z768]),(0,[z0,z769,z7,z3,z4,z6])],[(0,[z751,z103,z2,z3,z4,z6]),(0,[z165,z0,z7,z3,z4,z109]),(0,[z13,z7,z3,z4,z176,z6]),(0,[z7,z2,z770,z3,z4,z6]),(0,[z0,z33,z2,z373,z4,z6])],[(0,[z0,z7,z2,z3,z4,z771]),(0,[z13,z0,z7,z772,z4,z6]),(0,[z13,z7,z3,z4,z186,z6]),(0,[z393,z7,z2,z3,z4,z28]),(0,[z773,z7,z2,z3,z4,z6]),(0,[z0,z774,z2,z3,z4,z6])],[(0,[z13,z37,z7,z3,z4,z226]),(0,[z38,z7,z94,z3,z4,z6]),(0,[z0,z252,z2,z3,z68,z6]),(0,[z0,z7,z2,z3,z6,z775])],[(0,[z0,z7,z776,z3,z4,z6]),(0,[z38,z0,z7,z3,z4,z226]),(0,[z13,z102,z7,z3,z4,z6]),(0,[z124,z7,z2,z3,z67,z6]),(0,[z13,z89,z7,z3,z4,z6]),(0,[z143,z38,z7,z3,z4,z6])],[(0,[z0,z7,z2,z777,z4,z6]),(0,[z143,z7,z2,z3,z4,z6]),(0,[z261,z0,z193,z3,z4,z6]),(0,[z0,z778,z2,z3,z4,z6])],[(0,[z13,z7,z103,z3,z4,z109]),(0,[z779,z0,z7,z2,z3,z4])]],
   [[(0,[z13,z14,z7,z3,z4,z226]),(0,[z13,z0,z717,z3,z4,z6]),(0,[z13,z0,z391,z3,z4,z6]),(0,[z0,z7,z2,z134,z67,z6]),(0,[z581,z0,z7,z3,z224,z6]),(0,[z0,z7,z780,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z90])],[(0,[z165,z0,z7,z3,z67,z6]),(0,[z13,z0,z7,z3,z68,z109]),(0,[z0,z781,z2,z3,z4,z6]),(0,[z38,z0,z3,z4,z6,z605]),(0,[z0,z24,z2,z4,z322,z6]),(0,[z0,z171,z7,z2,z4,z183])],[(0,[z0,z98,z58,z3,z4,z6]),(0,[z14,z107,z2,z231,z4,z6]),(0,[z7,z3,z136,z742,z4,z6]),(0,[z38,z0,z3,z4,z6,z459]),(0,[z782,z7,z2,z3,z4,z6])],[(0,[z13,z706,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z783]),(1,[z0,z1,z171,z2,z3]),(0,[z0,z2,z3,z4,z6,z784]),(0,[z0,z104,z2,z3,z4,z65])],[(0,[z0,z7,z785,z3,z4,z6]),(0,[z13,z38,z7,z3,z4,z109]),(0,[z13,z124,z7,z3,z67,z6]),(0,[z0,z786,z7,z3,z4,z6]),(0,[z0,z2,z18,z757,z4,z6]),(0,[z0,z7,z3,z4,z6,z787]),(0,[z0,z7,z608,z3,z4,z6]),(0,[z7,z2,z3,z4,z6,z788])],[(0,[z13,z37,z7,z3,z4,z6])],[(0,[z13,z7,z103,z3,z67,z6]),(0,[z592,z103,z2,z3,z4,z6]),(0,[z13,z74,z252,z3,z4,z6]),(0,[z0,z7,z2,z3,z745,z6])],[(0,[z48,z103,z2,z3,z4,z6]),(0,[z13,z255,z7,z3,z4,z6]),(0,[z0,z789,z2,z3,z4,z6]),(0,[z0,z45,z7,z3,z4,z226]),(0,[z74,z7,z2,z790,z4,z6]),(1,[z0,z791,z3,z4,z6]),(0,[z0,z7,z2,z3,z792,z6]),(0,[z0,z7,z2,z3,z4,z784]),(0,[z0,z131,z7,z122,z4,z6]),(0,[z0,z63,z256,z2,z4,z6]),(0,[z793,z232,z7,z3,z4,z6]),(0,[z232,z0,z120,z2,z3,z79])]],
   [[(0,[z0,z7,z2,z231,z4,z6]),(0,[z13,z0,z7,z3,z4,z794]),(0,[z13,z209,z7,z3,z4,z6]),(0,[z7,z770,z237,z3,z4,z6]),(0,[z13,z7,z3,z4,z6,z236]),(0,[z0,z7,z308,z3,z4,z47])],[(1,[z751,z2,z3,z4,z6]),(0,[z13,z69,z7,z3,z4,z28]),(0,[z13,z338,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z747,z6]),(0,[z0,z7,z2,z3,z795,z6]),(1,[z0,z7,z3,z796,z6]),(0,[z124,z7,z3,z4,z6,z47]),(1,[z0,z7,z3,z4,z797]),(0,[z232,z0,z7,z294,z2,z4])],[(0,[z13,z0,z7,z3,z4,z798]),(0,[z13,z74,z7,z134,z4,z6]),(0,[z13,z69,z7,z3,z4,z52]),(0,[z0,z7,z799,z3,z4,z6]),(0,[z7,z2,z3,z4,z800,z6]),(0,[z7,z2,z3,z4,z28,z721])],[(0,[z0,z7,z2,z801,z4,z6]),(0,[z13,z38,z7,z3,z67,z6]),(0,[z0,z740,z2,z3,z4,z6]),(0,[z69,z200,z7,z3,z4,z52])],[(0,[z13,z0,z7,z3,z4,z802]),(0,[z0,z252,z117,z3,z4,z6]),(0,[z0,z7,z2,z3,z803,z6]),(0,[z0,z171,z2,z3,z20,z4])],[(0,[z13,z7,z737,z3,z4,z6]),(0,[z13,z354,z7,z3,z4,z6]),(0,[z13,z143,z7,z3,z4,z6]),(0,[z13,z0,z256,z3,z4,z6]),(0,[z0,z7,z2,z804,z4,z6]),(0,[z230,z7,z2,z3,z800,z6]),(0,[z805,z7,z2,z3,z4,z6]),(0,[z806,z7,z2,z3,z4,z6]),(0,[z0,z256,z433,z2,z3,z4])],[(0,[z13,z0,z7,z3,z4,z807]),(0,[z0,z7,z3,z4,z285,z161]),(0,[z38,z7,z3,z4,z303,z6]),(0,[z0,z57,z58,z3,z4,z6]),(0,[z808,z0,z7,z2,z3,z6]),(0,[z0,z120,z2,z3,z4,z6])],[(0,[z293,z7,z2,z3,z4,z6]),(0,[z13,z344,z7,z3,z4,z6]),(0,[z0,z7,z3,z216,z4,z6]),(0,[z0,z7,z2,z3,z809,z6]),(0,[z0,z7,z294,z2,z4,z6])]],
   [[(0,[z13,z7,z237,z134,z4,z6]),(0,[z200,z7,z3,z4,z28,z6]),(0,[z810,z7,z2,z3,z4,z6]),(0,[z0,z63,z7,z2,z264,z6])],[(0,[z13,z411,z7,z3,z4,z6])],[(0,[z0,z7,z811,z3,z4,z6]),(0,[z0,z199,z2,z134,z4,z6]),(0,[z812,z7,z2,z3,z4,z6]),(0,[z813,z7,z2,z3,z4,z6]),(1,[z0,z7,z2,z738,z6])],[(0,[z393,z38,z7,z3,z4,z6]),(0,[z0,z7,z814,z3,z4,z6]),(0,[z232,z0,z7,z2,z3,z21])],[(0,[z13,z37,z7,z3,z136,z6]),(0,[z13,z7,z3,z4,z263,z6]),(0,[z0,z7,z2,z772,z4,z6]),(0,[z0,z7,z3,z4,z285,z226]),(0,[z38,z0,z120,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z815])],[(0,[z13,z503,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z816]),(0,[z13,z91,z7,z3,z4,z6]),(0,[z0,z7,z3,z4,z51,z6]),(0,[z0,z7,z3,z205,z224,z6]),(1,[z7,z2,z790,z4,z6]),(1,[z7,z2,z3,z800,z6]),(0,[z0,z7,z817,z2,z4,z6]),(0,[z0,z7,z2,z3,z6,z749])],[(0,[z0,z7,z2,z3,z818,z6]),(0,[z0,z7,z658,z2,z6,z41]),(0,[z7,z819,z2,z3,z4,z6]),(0,[z0,z119,z40,z2,z4,z6])],[(0,[z13,z0,z7,z3,z4,z820]),(0,[z0,z821,z2,z3,z4,z6]),(0,[z7,z94,z3,z4,z272,z6]),(0,[z0,z822,z7,z2,z3,z6]),(0,[z0,z7,z3,z823,z4,z6]),(0,[z0,z824,z2,z3,z4,z6]),(0,[z0,z45,z7,z3,z4,z797])]],
   [[(0,[z13,z199,z103,z3,z4,z6]),(0,[z13,z0,z3,z4,z6,z605]),(0,[z0,z211,z7,z3,z67,z6]),(0,[z232,z0,z7,z502,z3,z79])],[(0,[z13,z33,z103,z3,z4,z6]),(0,[z13,z69,z7,z3,z4,z226]),(0,[z13,z7,z559,z3,z4,z6]),(0,[z13,z340,z7,z3,z4,z6]),(0,[z13,z7,z451,z3,z4,z6]),(0,[z13,z0,z3,z4,z6,z459]),(0,[z0,z119,z2,z3,z4,z6]),(0,[z131,z7,z122,z181,z4,z6]),(0,[z0,z7,z198,z3,z205,z6])],[(0,[z13,z7,z103,z210,z4,z6]),(0,[z0,z7,z2,z3,z68,z109]),(0,[z124,z38,z7,z3,z4,z6]),(0,[z0,z7,z825,z3,z4,z6]),(0,[z0,z151,z7,z3,z157,z6]),(0,[z0,z7,z198,z3,z796,z6])],[(0,[z124,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z6,z826]),(0,[z0,z827,z7,z3,z4,z6])],[(0,[z14,z38,z107,z3,z4,z6]),(0,[z13,z0,z7,z210,z68,z6]),(0,[z0,z7,z198,z3,z68,z6]),(0,[z38,z0,z7,z40,z4,z15]),(0,[z0,z7,z2,z3,z4,z828]),(0,[z0,z7,z2,z3,z4,z829]),(0,[z0,z7,z3,z4,z797,z47]),(0,[z0,z7,z2,z86,z738,z6])],[(0,[z13,z530,z7,z3,z4,z6]),(0,[z13,z407,z7,z3,z4,z6]),(0,[z38,z0,z75,z3,z4,z6]),(0,[z0,z7,z3,z830,z4,z6])],[(0,[z0,z33,z2,z472,z4,z6]),(0,[z13,z323,z7,z3,z4,z6]),(0,[z0,z7,z2,z134,z4,z6]),(0,[z0,z332,z7,z2,z4,z6]),(0,[z0,z1,z2,z3,z90,z110])],[(0,[z0,z7,z2,z831,z4,z6]),(0,[z13,z38,z7,z210,z4,z6]),(0,[z488,z0,z7,z3,z68,z6]),(0,[z13,z7,z466,z3,z4,z6]),(0,[z7,z2,z3,z136,z528,z6]),(0,[z832,z7,z2,z3,z4,z6]),(0,[z0,z171,z332,z7,z2,z4])]],
   [[(0,[z0,z7,z2,z833,z4,z6]),(0,[z13,z38,z7,z3,z4,z226]),(0,[z13,z7,z3,z136,z68,z6]),(0,[z0,z7,z483,z3,z68,z6]),(0,[z38,z0,z7,z4,z463,z6]),(0,[z133,z0,z791,z3,z4,z6]),(0,[z834,z7,z2,z3,z4,z6]),(0,[z0,z151,z7,z3,z796,z6]),(0,[z835,z7,z2,z3,z4,z6]),(0,[z0,z336,z7,z2,z3,z6])],[(0,[z0,z7,z2,z3,z4,z794]),(0,[z0,z19,z2,z3,z4,z170])],[(0,[z13,z69,z7,z3,z4,z6]),(0,[z13,z124,z7,z3,z4,z6]),(0,[z13,z230,z7,z3,z136,z6]),(0,[z38,z0,z7,z836,z4,z6]),(0,[z0,z2,z837,z3,z4,z6])],[(0,[z107,z751,z2,z3,z4,z6]),(0,[z13,z37,z7,z3,z4,z109]),(0,[z13,z702,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z798]),(0,[z69,z200,z7,z3,z4,z6]),(0,[z0,z7,z728,z2,z4,z6]),(0,[z0,z7,z2,z3,z4,z838])],[(0,[z13,z7,z103,z3,z4,z6]),(0,[z38,z0,z7,z3,z4,z109]),(0,[z38,z0,z7,z3,z6,z471]),(0,[z0,z7,z2,z3,z4,z839]),(0,[z7,z2,z3,z4,z6,z840]),(0,[z841,z7,z2,z3,z4,z6]),(0,[z0,z7,z3,z4,z285,z797]),(0,[z232,z0,z120,z7,z2,z3])],[(0,[z278,z103,z2,z3,z4,z6]),(0,[z0,z842,z2,z3,z4,z6]),(0,[z38,z0,z7,z87,z4,z64]),(0,[z0,z2,z3,z4,z843,z6])],[(0,[z13,z0,z7,z3,z844,z6]),(0,[z13,z0,z7,z845,z4,z6]),(0,[z7,z3,z4,z6,z236,z84])],[(0,[z0,z7,z2,z3,z4,z807]),(0,[z13,z14,z7,z3,z4,z109]),(0,[z13,z33,z7,z34,z4,z6]),(0,[z13,z7,z307,z3,z4,z6]),(0,[z13,z201,z7,z3,z4,z6]),(0,[z0,z846,z7,z3,z4,z6]),(0,[z0,z24,z2,z18,z4,z6]),(0,[z0,z113,z7,z658,z2,z6]),(0,[z0,z7,z2,z847,z4,z6]),(0,[z0,z120,z2,z3,z128,z6])]],
   [[(0,[z13,z274,z7,z3,z4,z6]),(0,[z7,z94,z2,z231,z4,z6]),(0,[z0,z7,z168,z3,z4,z6]),(0,[z0,z7,z294,z2,z128,z6])],[(0,[z0,z7,z2,z848,z4,z6]),(0,[z13,z38,z7,z3,z4,z6]),(0,[z13,z368,z7,z3,z4,z6]),(0,[z0,z200,z7,z3,z4,z226]),(0,[z849,z7,z2,z3,z4,z6]),(0,[z232,z0,z621,z7,z2,z3]),(0,[z0,z850,z2,z3,z4,z6]),(0,[z232,z0,z63,z7,z40,z2]),(0,[z232,z0,z120,z2,z3,z6])],[(0,[z13,z37,z7,z3,z67,z6]),(0,[z81,z7,z168,z34,z4,z6]),(0,[z124,z7,z2,z3,z136,z6]),(0,[z0,z33,z2,z757,z4,z6]),(0,[z0,z63,z7,z433,z2,z6])],[(0,[z0,z7,z851,z2,z4,z6]),(0,[z38,z0,z7,z3,z67,z6]),(0,[z13,z74,z7,z3,z68,z6]),(0,[z13,z0,z120,z3,z4,z6])],[(0,[z13,z0,z7,z3,z4,z852]),(0,[z13,z0,z7,z3,z853,z6]),(0,[z7,z181,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z854]),(0,[z0,z2,z3,z4,z6,z855]),(0,[z7,z2,z3,z4,z856,z6])],[(0,[z0,z7,z3,z67,z6,z226]),(0,[z0,z252,z2,z3,z4,z226]),(0,[z0,z75,z2,z34,z4,z6]),(0,[z0,z7,z857,z3,z4,z6]),(0,[z0,z113,z104,z7,z2,z3])],[(0,[z25,z293,z7,z3,z4,z6]),(0,[z13,z14,z7,z3,z67,z6]),(0,[z38,z0,z104,z3,z4,z5]),(0,[z0,z858,z2,z3,z4,z6]),(0,[z151,z7,z3,z207,z157,z6]),(0,[z0,z63,z7,z2,z507,z6]),(0,[z0,z2,z3,z6,z605,z471])],[(0,[z7,z2,z134,z34,z4,z6]),(0,[z0,z7,z2,z859,z4,z6]),(0,[z0,z7,z860,z3,z4,z6]),(0,[z0,z7,z861,z3,z4,z6]),(0,[z195,z133,z117,z3,z4,z6]),(0,[z0,z7,z2,z463,z6,z41])]],
   [[(0,[z0,z7,z2,z3,z4,z820]),(0,[z0,z7,z3,z4,z6,z84]),(0,[z0,z1,z2,z3,z110,z6])],[(0,[z0,z75,z2,z3,z4,z6]),(0,[z13,z278,z7,z3,z4,z6]),(0,[z13,z7,z237,z3,z68,z6]),(0,[z0,z7,z2,z3,z862,z6]),(0,[z0,z7,z863,z3,z4,z6]),(0,[z0,z113,z19,z2,z3,z4]),(0,[z864,z7,z2,z3,z4,z6])],[(0,[z13,z682,z7,z3,z4,z6]),(0,[z7,z2,z3,z4,z28,z226]),(0,[z0,z200,z7,z3,z4,z6]),(0,[z38,z7,z3,z4,z207,z6]),(0,[z0,z7,z2,z3,z865,z6]),(0,[z232,z0,z7,z2,z3,z460])],[(0,[z13,z0,z7,z3,z866,z6]),(0,[z13,z0,z7,z40,z4,z15]),(0,[z0,z199,z2,z3,z68,z6]),(0,[z0,z7,z867,z3,z4,z6]),(0,[z46,z7,z3,z4,z285,z6])],[(0,[z0,z7,z868,z3,z4,z6]),(0,[z0,z7,z2,z869,z4,z6]),(0,[z13,z0,z75,z3,z4,z6]),(0,[z38,z0,z33,z23,z4,z6]),(0,[z0,z7,z3,z4,z870,z6]),(0,[z0,z7,z2,z3,z4,z871])],[(0,[z48,z25,z103,z3,z4,z6]),(0,[z0,z103,z2,z99,z4,z6]),(0,[z13,z0,z781,z3,z4,z6]),(0,[z0,z7,z2,z210,z68,z6]),(0,[z0,z760,z2,z3,z4,z6]),(0,[z0,z872,z2,z3,z4,z6]),(0,[z0,z7,z2,z757,z4,z6]),(0,[z7,z2,z3,z4,z873,z6])],[(0,[z13,z174,z7,z3,z4,z6]),(0,[z0,z211,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z68,z226]),(0,[z38,z0,z336,z7,z3,z6]),(0,[z0,z874,z2,z3,z4,z6]),(0,[z37,z211,z7,z3,z4,z6]),(0,[z0,z7,z875,z3,z4,z6]),(0,[z0,z876,z7,z3,z4,z6])],[(0,[z13,z0,z199,z134,z4,z6]),(0,[z13,z0,z7,z4,z463,z6]),(0,[z0,z211,z7,z3,z157,z6]),(0,[z0,z7,z2,z4,z877,z6]),(0,[z0,z7,z2,z4,z878,z6]),(0,[z0,z791,z58,z3,z4,z6]),(0,[z0,z7,z2,z879,z4,z6]),(0,[z0,z880,z2,z3,z4,z6])]],
   [[(0,[z13,z0,z7,z210,z67,z6])],[(0,[z13,z0,z7,z3,z67,z226]),(0,[z13,z74,z75,z3,z4,z6]),(1,[z7,z770,z3,z4,z6]),(0,[z0,z881,z2,z3,z4,z6]),(0,[z69,z7,z2,z3,z4,z721]),(0,[z0,z7,z882,z3,z4,z6]),(0,[z0,z7,z883,z2,z4,z6])],[(0,[z13,z14,z103,z3,z4,z6]),(0,[z0,z7,z884,z3,z4,z6]),(0,[z0,z7,z2,z3,z6,z885])],[(0,[z13,z0,z7,z3,z4,z109]),(0,[z13,z0,z7,z3,z6,z471]),(0,[z13,z7,z531,z3,z4,z6]),(0,[z0,z7,z886,z3,z4,z6]),(0,[z0,z2,z757,z3,z4,z6]),(0,[z0,z7,z728,z50,z4,z6]),(0,[z0,z336,z7,z2,z64,z6])],[(0,[z13,z0,z7,z87,z4,z64]),(0,[z0,z7,z308,z3,z4,z109]),(0,[z13,z7,z3,z4,z28,z47]),(0,[z0,z7,z887,z3,z4,z6]),(0,[z0,z211,z7,z3,z205,z6]),(0,[z0,z7,z2,z4,z6,z888]),(0,[z232,z0,z7,z2,z3,z79])],[(0,[z0,z7,z3,z742,z4,z6]),(0,[z38,z7,z770,z3,z4,z6]),(0,[z143,z7,z2,z34,z4,z6]),(0,[z0,z7,z2,z3,z128,z458]),(0,[z0,z7,z40,z2,z4,z15])],[(0,[z13,z37,z7,z210,z4,z6]),(0,[z13,z568,z7,z3,z4,z6]),(0,[z0,z151,z7,z3,z67,z6])],[(0,[z195,z103,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z844,z6]),(0,[z38,z0,z7,z210,z4,z6]),(0,[z13,z37,z7,z3,z116,z6]),(0,[z0,z7,z2,z3,z68,z6]),(0,[z0,z889,z2,z3,z4,z6]),(0,[z0,z791,z2,z3,z4,z6]),(0,[z0,z890,z7,z3,z4,z6]),(0,[z232,z0,z7,z2,z3,z574]),(0,[z0,z7,z2,z4,z64,z492])]],
   [[(0,[z13,z48,z103,z3,z4,z6]),(0,[z13,z69,z7,z3,z4,z109]),(0,[z0,z7,z122,z210,z4,z6]),(0,[z0,z448,z7,z3,z157,z6])],[(0,[z48,z98,z103,z3,z4,z6]),(0,[z0,z256,z2,z3,z4,z6]),(0,[z0,z33,z2,z4,z560,z6]),(0,[z0,z1,z171,z7,z2,z3]),(0,[z891,z7,z2,z3,z4,z6])],[(0,[z13,z14,z7,z210,z4,z6]),(0,[z13,z0,z7,z3,z67,z6]),(0,[z13,z7,z582,z3,z4,z6]),(0,[z13,z404,z7,z3,z4,z6])],[(0,[z13,z656,z7,z3,z4,z6]),(0,[z13,z7,z3,z377,z4,z6]),(0,[z0,z7,z3,z4,z755,z6]),(0,[z0,z19,z658,z2,z4,z42]),(0,[z354,z46,z7,z3,z4,z6])],[(0,[z14,z252,z2,z3,z4,z6]),(0,[z13,z46,z7,z3,z4,z6])],[(0,[z13,z7,z3,z231,z4,z6]),(0,[z0,z7,z892,z3,z4,z6]),(0,[z13,z24,z7,z34,z4,z6]),(0,[z13,z0,z104,z3,z4,z5]),(0,[z13,z7,z3,z4,z6,z385]),(0,[z0,z7,z2,z3,z4,z852]),(0,[z0,z7,z893,z2,z4,z6]),(0,[z0,z894,z7,z2,z4,z6])],[(0,[z0,z895,z2,z3,z4,z6]),(0,[z0,z896,z2,z3,z4,z6]),(0,[z0,z7,z897,z3,z4,z6]),(0,[z0,z1,z171,z2,z3,z6]),(0,[z0,z898,z2,z3,z4,z6])],[(0,[z13,z74,z7,z3,z67,z6]),(0,[z13,z69,z7,z3,z67,z6]),(0,[z13,z0,z899,z3,z4,z6]),(0,[z0,z899,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z900]),(0,[z0,z7,z791,z3,z4,z6]),(0,[z0,z7,z901,z3,z4,z6])]],
   [[(0,[z0,z98,z199,z3,z4,z6]),(0,[z13,z7,z210,z136,z4,z6]),(0,[z13,z0,z7,z3,z4,z902]),(0,[z13,z74,z391,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z721]),(0,[z0,z24,z2,z757,z4,z6])],[(0,[z38,z0,z7,z3,z4,z6]),(0,[z0,z274,z2,z18,z4,z6]),(0,[z13,z7,z3,z4,z6,z394]),(0,[z7,z2,z3,z136,z800,z6]),(1,[z0,z7,z728,z4,z6])],[(0,[z38,z0,z19,z3,z4,z42]),(0,[z7,z903,z2,z3,z4,z6])],[(0,[z13,z0,z33,z23,z4,z6]),(0,[z13,z7,z397,z3,z4,z6]),(0,[z0,z19,z583,z2,z3,z4]),(0,[z0,z2,z3,z4,z5,z784]),(0,[z0,z904,z7,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z905])],[(0,[z13,z14,z7,z3,z4,z6]),(0,[z13,z195,z7,z3,z4,z6]),(0,[z13,z0,z7,z906,z4,z6]),(0,[z13,z391,z2,z3,z4,z6]),(0,[z13,z7,z603,z3,z4,z6]),(0,[z0,z2,z3,z4,z10,z6])],[(0,[z13,z0,z7,z210,z4,z226]),(0,[z13,z0,z7,z907,z4,z6]),(0,[z13,z0,z336,z7,z3,z6]),(0,[z13,z7,z237,z3,z67,z6]),(0,[z0,z7,z198,z3,z4,z226]),(1,[z0,z113,z19,z2,z3])],[(0,[z13,z7,z3,z67,z28,z6]),(0,[z13,z7,z475,z3,z4,z6]),(0,[z13,z7,z408,z3,z4,z6]),(0,[z74,z7,z82,z216,z4,z6]),(0,[z0,z7,z908,z3,z4,z6]),(0,[z0,z7,z122,z728,z4,z6]),(0,[z0,z7,z2,z3,z738,z6])],[(0,[z0,z909,z7,z3,z4,z6])]],
   [[(0,[z488,z0,z7,z3,z4,z226]),(0,[z13,z275,z7,z3,z4,z6]),(0,[z0,z910,z2,z3,z4,z6]),(0,[z354,z0,z7,z3,z4,z161]),(0,[z0,z7,z122,z243,z4,z6]),(0,[z7,z94,z3,z4,z6,z84]),(0,[z0,z7,z2,z4,z463,z6]),(0,[z232,z0,z7,z2,z121,z79])],[(0,[z0,z7,z3,z911,z4,z6]),(0,[z13,z7,z3,z136,z4,z226]),(0,[z69,z38,z7,z3,z4,z52])],[(0,[z0,z7,z2,z836,z4,z6]),(0,[z0,z7,z2,z3,z67,z226]),(0,[z69,z7,z2,z3,z4,z52]),(0,[z0,z2,z3,z4,z784,z42]),(0,[z0,z7,z2,z3,z6,z912])],[(0,[z13,z0,z913,z3,z4,z6]),(0,[z13,z7,z611,z3,z4,z6]),(0,[z0,z7,z2,z914,z4,z6]),(0,[z915,z7,z2,z3,z4,z6]),(0,[z0,z63,z256,z2,z11,z6]),(0,[z0,z7,z2,z3,z61,z614]),(0,[z0,z916,z7,z3,z4,z6])],[(0,[z0,z57,z199,z3,z4,z6]),(0,[z0,z252,z2,z3,z4,z109]),(0,[z13,z7,z770,z3,z4,z6]),(0,[z917,z7,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z918,z6]),(0,[z38,z0,z113,z7,z3,z6]),(0,[z124,z7,z2,z3,z116,z6]),(0,[z919,z7,z2,z3,z4,z6]),(0,[z0,z19,z658,z2,z4,z6]),(0,[z0,z7,z198,z3,z435,z6])],[(0,[z0,z920,z7,z2,z3,z6]),(0,[z13,z0,z7,z210,z4,z6])],[(0,[z13,z0,z7,z3,z4,z226]),(0,[z115,z0,z252,z3,z4,z6]),(0,[z921,z7,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z409])]],
   [[(0,[z0,z7,z922,z3,z4,z6]),(0,[z38,z7,z3,z494,z4,z6]),(0,[z0,z7,z3,z4,z923,z6]),(0,[z0,z7,z3,z4,z6,z924]),(0,[z0,z2,z3,z4,z5,z414]),(0,[z0,z40,z2,z4,z605,z15])],[(0,[z0,z2,z3,z4,z925,z6])],[(0,[z13,z7,z3,z136,z4,z6]),(0,[z13,z252,z3,z136,z4,z6]),(0,[z13,z0,z7,z926,z4,z6]),(0,[z13,z7,z3,z4,z445,z6]),(0,[z0,z7,z483,z3,z4,z6]),(0,[z324,z7,z3,z34,z4,z6]),(0,[z0,z927,z7,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z928]),(0,[z0,z929,z2,z3,z4,z6])],[(0,[z13,z69,z7,z210,z4,z6]),(0,[z0,z7,z2,z3,z67,z6]),(0,[z0,z252,z2,z3,z67,z6]),(0,[z37,z7,z2,z3,z67,z6]),(0,[z13,z7,z3,z136,z157,z6]),(0,[z0,z7,z483,z3,z157,z6]),(0,[z0,z7,z2,z3,z4,z930]),(0,[z0,z931,z2,z3,z4,z6]),(0,[z0,z7,z932,z3,z4,z6]),(0,[z0,z7,z87,z2,z4,z64])],[(0,[z0,z7,z737,z3,z4,z6]),(0,[z13,z74,z7,z3,z4,z226]),(0,[z13,z139,z7,z3,z4,z6]),(0,[z0,z2,z757,z23,z4,z6]),(0,[z0,z63,z7,z2,z460,z6])],[(0,[z13,z0,z7,z3,z4,z933]),(0,[z0,z7,z2,z3,z4,z934]),(0,[z0,z7,z2,z3,z4,z935]),(0,[z0,z7,z2,z3,z936,z6]),(0,[z0,z937,z2,z3,z4,z6]),(0,[z0,z938,z2,z3,z4,z6]),(0,[z0,z7,z40,z2,z471,z15])],[(0,[z0,z63,z7,z433,z2,z11]),(0,[z0,z939,z7,z3,z4,z6])],[(0,[z940,z0,z7,z3,z4,z6]),(0,[z0,z941,z2,z3,z4,z6]),(0,[z942,z7,z2,z3,z4,z6]),(0,[z124,z7,z3,z205,z4,z6])]],
   [[(0,[z13,z0,z7,z3,z4,z6]),(0,[z13,z0,z7,z3,z67,z109]),(0,[z0,z7,z483,z3,z205,z6])],[(0,[z0,z7,z2,z943,z4,z6]),(0,[z13,z7,z3,z944,z4,z6]),(0,[z13,z0,z19,z3,z4,z42]),(0,[z69,z7,z2,z3,z4,z226]),(0,[z0,z7,z308,z3,z4,z6])],[(0,[z0,z7,z2,z945,z4,z6]),(0,[z13,z7,z3,z4,z6,z465]),(0,[z13,z7,z237,z3,z4,z226]),(0,[z0,z7,z87,z2,z4,z454])],[(1,[z13,z7,z231,z4,z6]),(0,[z13,z0,z252,z134,z4,z6]),(0,[z74,z7,z2,z134,z4,z6]),(0,[z0,z63,z7,z2,z11,z6]),(0,[z0,z7,z433,z2,z86,z3]),(0,[z0,z336,z2,z3,z6,z605])],[(0,[z0,z199,z2,z3,z4,z226]),(0,[z0,z946,z2,z3,z4,z6]),(0,[z0,z7,z3,z4,z947,z6])],[(0,[z0,z7,z2,z906,z4,z6]),(0,[z0,z948,z7,z3,z4,z6]),(0,[z13,z74,z7,z3,z4,z6]),(0,[z13,z0,z910,z3,z4,z6]),(0,[z949,z7,z2,z3,z4,z6]),(0,[z0,z7,z950,z3,z4,z6])],[(0,[z13,z7,z3,z472,z4,z6]),(0,[z0,z7,z2,z210,z4,z226]),(0,[z38,z0,z332,z7,z4,z6]),(0,[z0,z1,z332,z2,z4,z6])],[(0,[z0,z7,z951,z3,z4,z6]),(0,[z0,z117,z791,z3,z4,z6])]],
   [[(0,[z0,z7,z2,z3,z4,z802]),(0,[z0,z7,z2,z3,z952,z6]),(0,[z0,z2,z3,z4,z953,z6])],[(0,[z211,z7,z3,z136,z4,z6]),(0,[z954,z7,z2,z3,z4,z6]),(0,[z46,z45,z7,z3,z4,z6]),(0,[z0,z7,z40,z2,z153,z4])],[(0,[z13,z0,z7,z955,z4,z6]),(0,[z13,z0,z7,z3,z4,z956]),(0,[z13,z7,z34,z123,z4,z6]),(0,[z38,z0,z63,z7,z11,z6]),(0,[z7,z2,z3,z4,z957,z6]),(0,[z0,z7,z958,z3,z4,z6]),(0,[z959,z7,z2,z3,z4,z6]),(0,[z0,z336,z119,z2,z3,z6])],[(0,[z13,z7,z237,z3,z4,z6]),(0,[z13,z252,z237,z3,z4,z6])],[(0,[z13,z7,z193,z3,z4,z6]),(0,[z13,z0,z113,z7,z3,z6]),(0,[z195,z7,z2,z764,z4,z6]),(0,[z0,z19,z2,z3,z4,z784]),(0,[z46,z7,z198,z3,z4,z6]),(0,[z0,z336,z7,z40,z2,z6])],[(0,[z299,z7,z2,z82,z4,z6]),(0,[z0,z332,z2,z20,z4,z6]),(0,[z960,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z86,z6,z551])],[(0,[z0,z7,z961,z3,z4,z6]),(0,[z13,z0,z7,z3,z962,z6]),(0,[z0,z7,z95,z123,z4,z6]),(0,[z0,z963,z2,z3,z4,z6])],[(0,[z13,z74,z7,z82,z4,z6]),(0,[z0,z7,z2,z210,z4,z6]),(0,[z0,z252,z2,z210,z4,z6]),(0,[z37,z38,z7,z3,z116,z6]),(0,[z38,z0,z7,z3,z6,z41]),(0,[z38,z7,z555,z3,z4,z6])]],
   [[(0,[z0,z7,z2,z3,z964,z6]),(0,[z0,z7,z2,z3,z4,z226]),(0,[z37,z211,z7,z3,z116,z6]),(0,[z0,z965,z7,z2,z4,z6]),(0,[z143,z131,z7,z3,z4,z6])],[(0,[z13,z0,z7,z3,z966,z6]),(0,[z0,z252,z58,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z967]),(0,[z0,z7,z3,z4,z796,z6]),(0,[z7,z2,z968,z3,z4,z6])],[(0,[z0,z7,z2,z969,z4,z6]),(0,[z13,z524,z7,z3,z4,z6]),(0,[z38,z0,z24,z18,z4,z6]),(0,[z0,z7,z3,z970,z4,z6]),(0,[z0,z7,z2,z12,z594,z6]),(0,[z0,z7,z3,z4,z971,z6]),(0,[z0,z19,z2,z3,z469,z4]),(0,[z143,z7,z3,z123,z4,z6])],[(0,[z14,z107,z2,z3,z4,z6]),(0,[z13,z103,z58,z3,z4,z6]),(0,[z13,z7,z3,z497,z4,z6]),(0,[z13,z0,z7,z972,z4,z6]),(0,[z13,z7,z3,z4,z643,z6]),(0,[z0,z7,z2,z926,z4,z6]),(0,[z0,z7,z2,z3,z973,z6]),(0,[z232,z0,z7,z294,z2,z79])],[(0,[z0,z7,z2,z3,z4,z974]),(0,[z13,z0,z7,z210,z4,z109]),(0,[z13,z7,z134,z136,z4,z6]),(0,[z38,z0,z7,z3,z61,z128]),(0,[z0,z975,z2,z3,z4,z6]),(0,[z0,z976,z7,z3,z4,z6]),(0,[z0,z7,z2,z4,z6,z977])],[(0,[z7,z2,z3,z978,z4,z6]),(0,[z0,z336,z7,z40,z2,z3]),(1,[z232,z0,z7,z294,z2])],[(0,[z0,z7,z979,z2,z3,z4]),(0,[z13,z0,z941,z3,z4,z6]),(0,[z13,z508,z7,z3,z4,z6]),(0,[z215,z38,z7,z3,z4,z28]),(0,[z7,z3,z4,z207,z272,z6]),(0,[z46,z7,z2,z3,z4,z28]),(0,[z0,z7,z197,z3,z4,z285])],[(0,[z13,z214,z7,z3,z4,z6]),(0,[z46,z7,z2,z3,z4,z52]),(0,[z133,z293,z117,z3,z4,z6])]],
   [[(0,[z13,z25,z7,z3,z4,z6]),(0,[z13,z7,z3,z512,z4,z6]),(0,[z13,z7,z3,z34,z68,z6]),(0,[z13,z7,z3,z136,z4,z109]),(0,[z7,z168,z181,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z6]),(0,[z0,z252,z2,z3,z4,z6]),(0,[z13,z0,z7,z3,z980,z6]),(0,[z13,z7,z3,z4,z515,z6]),(0,[z0,z7,z2,z3,z67,z109]),(0,[z13,z7,z156,z3,z4,z6]),(0,[z0,z7,z981,z3,z4,z6]),(0,[z232,z0,z1,z19,z2,z3]),(0,[z0,z104,z2,z3,z4,z5]),(0,[z0,z982,z2,z3,z4,z6])],[(0,[z81,z38,z7,z34,z4,z6]),(0,[z38,z0,z7,z4,z6,z121])],[(0,[z13,z474,z7,z3,z4,z6]),(0,[z13,z0,z842,z3,z4,z6]),(0,[z473,z0,z7,z243,z4,z6]),(0,[z81,z7,z2,z34,z4,z6]),(0,[z0,z324,z7,z123,z4,z6]),(0,[z0,z33,z2,z672,z4,z6]),(0,[z296,z143,z7,z3,z4,z6])],[(0,[z13,z0,z7,z3,z983,z6]),(0,[z0,z7,z2,z3,z4,z984]),(0,[z0,z7,z985,z3,z4,z6])],[(0,[z13,z0,z332,z7,z4,z6]),(0,[z13,z7,z3,z205,z136,z6]),(0,[z0,z7,z2,z986,z4,z6]),(0,[z0,z256,z2,z3,z4,z485]),(1,[z0,z7,z2,z4,z977]),(0,[z793,z0,z7,z3,z4,z6])],[(0,[z0,z1,z2,z183,z110,z6])],[(0,[z0,z7,z2,z3,z987,z6]),(0,[z13,z7,z3,z136,z67,z6]),(0,[z988,z0,z7,z3,z4,z6]),(0,[z0,z7,z2,z790,z4,z6]),(0,[z37,z7,z2,z3,z800,z6]),(0,[z0,z171,z27,z7,z2,z3])]],
   [[(0,[z74,z75,z2,z82,z4,z6]),(0,[z0,z7,z50,z123,z4,z6]),(0,[z0,z7,z2,z3,z796,z6]),(0,[z0,z7,z2,z3,z4,z797]),(0,[z0,z7,z40,z2,z154,z4]),(0,[z989,z7,z2,z3,z4,z6])],[(0,[z13,z526,z7,z3,z4,z6]),(0,[z13,z686,z7,z3,z4,z6]),(0,[z13,z0,z63,z7,z11,z6]),(0,[z230,z7,z3,z136,z272,z6]),(0,[z195,z7,z117,z3,z4,z6])],[(0,[z0,z7,z2,z845,z4,z6]),(0,[z0,z7,z3,z4,z6,z990]),(0,[z7,z2,z3,z4,z6,z991]),(0,[z0,z7,z2,z4,z64,z977]),(0,[z0,z120,z2,z4,z6,z121]),(0,[z0,z7,z2,z3,z61,z749])],[(0,[z0,z7,z2,z955,z4,z6]),(0,[z13,z74,z7,z3,z4,z109]),(0,[z38,z0,z7,z294,z4,z6])],[(0,[z13,z0,z252,z3,z68,z6])],[(0,[z13,z0,z7,z992,z4,z6]),(0,[z13,z192,z7,z3,z4,z6]),(0,[z38,z0,z7,z3,z4,z485]),(0,[z81,z7,z2,z790,z4,z6]),(0,[z0,z993,z7,z3,z4,z6])],[(0,[z13,z7,z103,z134,z4,z6]),(0,[z0,z7,z994,z3,z4,z6]),(0,[z0,z7,z3,z4,z67,z226]),(0,[z13,z0,z7,z3,z6,z41]),(0,[z0,z7,z95,z3,z4,z6]),(0,[z46,z7,z2,z3,z4,z226]),(0,[z0,z7,z2,z995,z4,z6]),(0,[z0,z7,z3,z4,z6,z996])],[(0,[z0,z997,z7,z2,z3,z6]),(0,[z133,z0,z26,z3,z4,z6]),(0,[z13,z38,z252,z3,z4,z6]),(0,[z13,z7,z3,z4,z556,z6]),(0,[z0,z7,z2,z3,z962,z6]),(0,[z517,z38,z7,z3,z4,z6]),(0,[z998,z7,z2,z3,z4,z6]),(0,[z0,z7,z3,z4,z999,z6])]],
   [[(0,[z13,z0,z7,z134,z68,z6]),(0,[z0,z7,z3,z4,z1000,z6]),(0,[z0,z7,z2,z3,z853,z6]),(0,[z0,z7,z2,z1001,z4,z6]),(0,[z0,z7,z1002,z3,z4,z6]),(0,[z0,z7,z433,z2,z3,z4]),(0,[z0,z120,z2,z3,z61,z4])],[(0,[z13,z0,z24,z18,z4,z6]),(0,[z13,z7,z237,z3,z4,z109]),(0,[z0,z7,z2,z4,z64,z649]),(0,[z0,z336,z7,z87,z2,z3]),(0,[z0,z7,z294,z2,z61,z4])],[(0,[z0,z7,z2,z3,z966,z6]),(0,[z13,z503,z199,z3,z4,z6]),(0,[z13,z421,z7,z3,z4,z6]),(0,[z0,z1003,z2,z3,z4,z6]),(0,[z0,z7,z427,z123,z4,z6]),(0,[z0,z7,z3,z4,z6,z1004]),(0,[z793,z7,z2,z3,z4,z6]),(0,[z0,z7,z3,z1005,z4,z6])],[(0,[z13,z38,z7,z134,z4,z6]),(0,[z13,z0,z7,z3,z61,z128]),(0,[z0,z199,z2,z3,z4,z109]),(0,[z0,z1006,z2,z3,z4,z6])],[(0,[z0,z7,z2,z972,z4,z6]),(0,[z13,z7,z3,z4,z563,z6]),(0,[z13,z7,z482,z3,z4,z6]),(0,[z13,z7,z3,z4,z207,z6]),(0,[z0,z1007,z7,z3,z4,z6]),(0,[z143,z131,z7,z122,z4,z6])],[(0,[z13,z0,z7,z3,z4,z730]),(0,[z0,z7,z2,z210,z4,z109]),(0,[z0,z33,z298,z2,z4,z6]),(0,[z0,z7,z1008,z2,z3,z4])],[(0,[z13,z190,z7,z3,z4,z6]),(0,[z46,z38,z7,z3,z4,z6]),(0,[z0,z1009,z7,z3,z4,z6]),(0,[z0,z1010,z7,z2,z4,z6])],[(0,[z13,z133,z103,z3,z4,z6]),(0,[z13,z0,z7,z3,z4,z1011]),(0,[z0,z7,z2,z3,z866,z6]),(0,[z46,z7,z2,z3,z4,z6]),(0,[z0,z33,z2,z23,z4,z6]),(0,[z0,z7,z2,z4,z1012,z6])]],
   [[(0,[z0,z7,z1013,z3,z4,z6]),(0,[z133,z0,z199,z3,z4,z6]),(0,[z0,z131,z7,z134,z4,z6]),(0,[z0,z7,z3,z68,z157,z6]),(0,[z38,z0,z7,z433,z3,z4]),(0,[z0,z7,z2,z3,z1014,z6]),(0,[z0,z7,z2,z4,z6,z1015]),(0,[z0,z113,z7,z2,z463,z6]),(0,[z0,z7,z3,z4,z1016,z6])],[(0,[z13,z199,z3,z136,z4,z6]),(0,[z13,z175,z7,z3,z4,z6]),(0,[z13,z0,z7,z4,z6,z121]),(0,[z0,z1017,z2,z3,z4,z6]),(0,[z0,z7,z2,z1018,z4,z6])],[(0,[z25,z7,z94,z3,z4,z6]),(0,[z299,z107,z2,z3,z4,z6]),(0,[z0,z199,z2,z3,z67,z6]),(0,[z0,z7,z2,z3,z980,z6]),(0,[z0,z200,z7,z3,z4,z285])],[(0,[z13,z0,z7,z3,z4,z1019]),(0,[z0,z324,z7,z3,z4,z6]),(0,[z38,z0,z119,z3,z4,z6]),(0,[z0,z7,z3,z4,z135,z47]),(0,[z0,z7,z122,z95,z4,z6]),(0,[z45,z7,z3,z4,z236,z47])],[(0,[z7,z3,z4,z28,z755,z6]),(0,[z13,z299,z7,z3,z4,z6]),(0,[z0,z7,z2,z210,z67,z6]),(0,[z133,z0,z193,z3,z4,z6]),(0,[z0,z7,z3,z4,z6,z1020]),(0,[z0,z1021,z7,z3,z4,z6])],[(0,[z0,z7,z2,z3,z983,z6]),(0,[z13,z103,z18,z3,z4,z6]),(0,[z13,z252,z3,z4,z28,z6]),(0,[z232,z0,z7,z294,z2,z6])],[(0,[z0,z200,z7,z3,z4,z47]),(0,[z232,z0,z7,z608,z3,z79])],[(0,[z13,z69,z199,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z109]),(0,[z0,z7,z1022,z2,z3,z4]),(0,[z0,z7,z1023,z3,z4,z6]),(0,[z517,z7,z2,z3,z136,z6]),(0,[z0,z7,z2,z3,z6,z471]),(0,[z0,z7,z2,z4,z977,z15])]],
   [[(0,[z133,z0,z98,z3,z4,z6]),(0,[z38,z293,z7,z3,z4,z6])],[(0,[z317,z7,z2,z34,z4,z6]),(0,[z0,z2,z3,z4,z1024,z6]),(0,[z7,z1025,z2,z3,z4,z6]),(0,[z232,z0,z7,z537,z2,z3])],[(0,[z13,z0,z7,z294,z4,z6]),(0,[z0,z1026,z2,z3,z4,z6]),(0,[z0,z7,z40,z2,z4,z574]),(0,[z0,z7,z2,z738,z11,z6])],[(0,[z0,z391,z2,z3,z4,z6]),(0,[z13,z0,z199,z3,z68,z6]),(0,[z13,z578,z7,z3,z4,z6]),(0,[z13,z7,z3,z4,z6,z588]),(1,[z7,z2,z3,z4,z721]),(0,[z0,z33,z2,z96,z4,z6]),(0,[z0,z7,z2,z3,z4,z1027]),(0,[z0,z24,z2,z4,z677,z6]),(0,[z0,z1028,z7,z3,z4,z6]),(0,[z0,z63,z7,z2,z485,z11])],[(0,[z13,z0,z7,z3,z4,z485]),(0,[z1029,z7,z2,z3,z4,z6]),(0,[z143,z824,z2,z3,z4,z6]),(0,[z0,z1030,z7,z3,z4,z6])],[(0,[z513,z103,z2,z3,z4,z6]),(0,[z13,z7,z3,z4,z135,z6]),(0,[z13,z0,z7,z1031,z4,z6]),(0,[z0,z7,z2,z4,z6,z1032]),(0,[z232,z0,z120,z2,z3,z4])],[(0,[z13,z38,z199,z3,z4,z6]),(0,[z13,z74,z7,z210,z4,z6]),(0,[z0,z7,z2,z992,z4,z6]),(0,[z38,z0,z3,z4,z10,z6]),(0,[z0,z7,z2,z3,z61,z291]),(1,[z0,z63,z7,z433,z2]),(0,[z0,z63,z7,z433,z2,z4]),(0,[z232,z0,z7,z294,z2,z3])],[(0,[z0,z1033,z7,z2,z4,z6]),(0,[z13,z0,z789,z3,z4,z6]),(0,[z13,z7,z3,z596,z4,z6]),(0,[z0,z1,z332,z2,z110,z6]),(0,[z0,z7,z2,z3,z6,z41])]],
   [[(0,[z13,z0,z252,z3,z67,z6]),(0,[z576,z0,z7,z3,z67,z6]),(0,[z13,z7,z228,z3,z4,z6]),(0,[z38,z0,z7,z86,z12,z6]),(0,[z0,z125,z58,z3,z4,z6]),(0,[z0,z7,z1034,z2,z4,z6])],[(0,[z7,z103,z26,z3,z4,z6]),(0,[z0,z7,z2,z134,z68,z6]),(0,[z145,z0,z7,z3,z512,z6]),(0,[z0,z57,z791,z3,z4,z6]),(0,[z232,z0,z7,z2,z3,z170]),(0,[z0,z7,z1035,z3,z4,z6]),(0,[z0,z7,z1036,z3,z4,z6])],[(0,[z13,z199,z237,z3,z4,z6]),(0,[z0,z7,z3,z4,z109,z47]),(0,[z215,z7,z2,z3,z4,z721]),(0,[z215,z7,z308,z3,z4,z28]),(0,[z0,z2,z3,z4,z485,z10])],[(0,[z14,z107,z167,z3,z4,z6]),(0,[z13,z0,z1003,z3,z4,z6]),(0,[z143,z7,z2,z134,z4,z6]),(0,[z0,z7,z770,z3,z4,z6]),(0,[z0,z1037,z2,z3,z4,z6]),(0,[z0,z7,z40,z2,z4,z593])],[(0,[z0,z7,z3,z1038,z4,z6]),(0,[z13,z74,z7,z34,z4,z6]),(0,[z13,z194,z7,z3,z4,z6]),(0,[z13,z7,z237,z210,z4,z6]),(0,[z0,z7,z2,z3,z4,z902]),(0,[z13,z7,z3,z606,z4,z6]),(0,[z147,z38,z7,z3,z4,z6]),(0,[z38,z0,z1,z3,z110,z6]),(0,[z0,z7,z3,z4,z1039,z6]),(0,[z0,z1040,z7,z3,z4,z6]),(0,[z0,z7,z1041,z3,z4,z6]),(0,[z0,z7,z2,z3,z61,z128]),(0,[z232,z0,z7,z2,z3,z749])],[(0,[z0,z7,z3,z4,z157,z226]),(0,[z0,z7,z3,z4,z1042,z6])],[(0,[z0,z7,z1043,z3,z4,z6]),(0,[z13,z37,z252,z3,z4,z6]),(0,[z7,z3,z944,z34,z4,z6]),(0,[z0,z199,z2,z210,z4,z6]),(0,[z0,z7,z2,z1044,z4,z6]),(0,[z0,z1,z171,z2,z3,z110]),(0,[z0,z19,z2,z3,z41,z42]),(0,[z0,z7,z2,z1045,z4,z6]),(1,[z0,z336,z7,z40,z2])],[(0,[z13,z7,z103,z3,z68,z6]),(0,[z38,z0,z252,z3,z4,z6]),(0,[z13,z0,z7,z433,z3,z4])]],
   [[(0,[z14,z107,z26,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z1011]),(0,[z13,z7,z3,z4,z272,z6]),(0,[z1046,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z4,z6,z1047])],[(0,[z751,z7,z2,z3,z4,z6]),(0,[z13,z7,z3,z34,z4,z226]),(0,[z0,z7,z2,z907,z4,z6]),(0,[z13,z7,z615,z3,z4,z6]),(0,[z0,z1048,z2,z3,z4,z6])],[(0,[z13,z14,z252,z3,z4,z6]),(0,[z13,z195,z252,z3,z4,z6]),(0,[z13,z37,z7,z134,z4,z6]),(0,[z13,z0,z119,z3,z4,z6]),(0,[z0,z7,z3,z4,z6,z1049]),(0,[z503,z195,z7,z3,z4,z6]),(0,[z0,z113,z7,z2,z3,z6]),(0,[z0,z104,z2,z3,z4,z784])],[(0,[z38,z0,z7,z134,z4,z6]),(0,[z0,z7,z1050,z3,z4,z6]),(0,[z0,z7,z2,z1051,z4,z6]),(0,[z0,z113,z19,z2,z3,z42])],[(0,[z0,z7,z2,z3,z4,z1019]),(0,[z195,z7,z2,z879,z4,z6]),(0,[z0,z7,z1052,z2,z4,z6])],[(0,[z146,z0,z7,z3,z4,z135]),(0,[z581,z124,z7,z3,z4,z6]),(0,[z0,z63,z7,z2,z154,z6])],[(0,[z0,z7,z26,z3,z4,z6]),(0,[z0,z1053,z7,z2,z3,z4]),(0,[z13,z14,z7,z134,z4,z6]),(0,[z0,z252,z26,z3,z4,z6]),(0,[z7,z2,z3,z4,z6,z236]),(0,[z0,z1054,z7,z3,z4,z6]),(0,[z7,z2,z3,z800,z116,z6]),(0,[z143,z850,z2,z3,z4,z6])],[(0,[z13,z0,z7,z801,z4,z6]),(0,[z13,z7,z134,z4,z28,z6]),(0,[z13,z293,z7,z3,z4,z6]),(0,[z0,z324,z7,z122,z4,z6]),(0,[z1055,z0,z7,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z605])]],
   [[(0,[z0,z199,z2,z3,z4,z6]),(0,[z13,z0,z199,z3,z4,z109]),(0,[z0,z7,z3,z944,z4,z6]),(0,[z0,z1056,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z1057]),(0,[z0,z2,z3,z4,z6,z459]),(0,[z0,z7,z2,z4,z1058,z6])],[(0,[z13,z581,z7,z3,z68,z6]),(0,[z13,z7,z339,z3,z4,z6]),(0,[z0,z1059,z7,z3,z4,z6]),(0,[z0,z1060,z2,z3,z4,z6])],[(0,[z13,z252,z3,z34,z4,z6]),(0,[z13,z0,z7,z3,z1061,z6]),(0,[z13,z143,z7,z134,z4,z6]),(0,[z232,z38,z0,z7,z3,z79]),(0,[z0,z1,z2,z3,z21,z6])],[(0,[z13,z7,z3,z4,z28,z109]),(0,[z13,z461,z7,z3,z4,z6]),(0,[z37,z7,z2,z3,z116,z6]),(0,[z1062,z7,z2,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z1063]),(0,[z0,z7,z1064,z3,z4,z6])],[(0,[z38,z0,z7,z99,z4,z6]),(0,[z13,z0,z252,z210,z4,z6]),(0,[z0,z7,z3,z68,z67,z6]),(0,[z592,z38,z7,z3,z4,z6]),(0,[z230,z7,z483,z3,z136,z6]),(0,[z1065,z7,z2,z3,z4,z6]),(0,[z0,z7,z1066,z3,z4,z6]),(0,[z0,z7,z2,z4,z183,z90]),(0,[z7,z1067,z2,z3,z4,z6])],[(0,[z13,z0,z252,z3,z4,z226]),(0,[z13,z0,z3,z4,z10,z6]),(0,[z13,z7,z3,z4,z285,z28]),(0,[z7,z2,z3,z4,z721,z52])],[(0,[z0,z751,z2,z3,z4,z6]),(0,[z13,z232,z0,z7,z3,z79]),(0,[z0,z7,z2,z1031,z4,z6]),(0,[z0,z24,z2,z307,z4,z6]),(0,[z0,z7,z2,z4,z1068,z6]),(0,[z0,z7,z40,z2,z4,z977])],[(0,[z13,z14,z7,z99,z4,z6]),(0,[z0,z252,z199,z3,z4,z6]),(0,[z13,z0,z199,z3,z67,z6]),(1,[z13,z391,z3,z4,z6]),(0,[z13,z0,z7,z86,z12,z6]),(0,[z391,z94,z2,z3,z4,z6]),(0,[z0,z33,z2,z202,z4,z6]),(0,[z0,z45,z7,z3,z4,z47]),(0,[z0,z256,z2,z12,z4,z6])]],
   [[(0,[z13,z415,z7,z3,z4,z6]),(0,[z0,z113,z19,z7,z2,z3]),(0,[z0,z113,z2,z3,z5,z6]),(0,[z124,z7,z197,z3,z4,z6]),(0,[z0,z63,z2,z10,z11,z6])],[(0,[z0,z7,z2,z3,z4,z933]),(0,[z13,z7,z2,z231,z4,z6]),(0,[z13,z0,z7,z134,z4,z226]),(0,[z0,z7,z2,z3,z4,z977])],[(0,[z13,z7,z3,z68,z28,z6]),(0,[z38,z0,z7,z4,z183,z6]),(0,[z38,z0,z171,z7,z3,z4]),(0,[z215,z7,z2,z3,z4,z28]),(0,[z0,z1,z171,z2,z3,z4])],[(0,[z0,z7,z1069,z3,z4,z6]),(0,[z13,z0,z7,z1070,z4,z6]),(0,[z13,z0,z1,z3,z110,z6]),(0,[z13,z7,z388,z3,z4,z6]),(0,[z0,z7,z3,z310,z4,z6]),(0,[z0,z7,z2,z1071,z4,z6]),(0,[z0,z2,z18,z4,z112,z6]),(0,[z0,z7,z1072,z2,z3,z4]),(0,[z0,z1073,z7,z2,z3,z6]),(0,[z124,z151,z7,z3,z4,z6]),(0,[z0,z294,z2,z4,z6,z459])],[(0,[z14,z7,z26,z3,z4,z6]),(0,[z13,z7,z3,z243,z4,z6]),(0,[z13,z241,z7,z3,z4,z6]),(0,[z124,z151,z7,z3,z157,z6])],[(0,[z13,z37,z199,z3,z4,z6]),(0,[z0,z113,z19,z2,z3,z6]),(0,[z7,z2,z3,z4,z6,z1074])],[(0,[z13,z0,z252,z3,z4,z6]),(0,[z38,z0,z199,z3,z4,z6]),(0,[z7,z281,z2,z34,z4,z6])],[(0,[z0,z7,z95,z210,z4,z6]),(0,[z0,z7,z1075,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z749])]],
   [[(0,[z0,z7,z1076,z3,z4,z6]),(0,[z0,z7,z1077,z2,z4,z6]),(0,[z0,z1078,z7,z3,z4,z6])],[(0,[z0,z7,z3,z4,z1079,z6]),(0,[z13,z14,z199,z3,z4,z6]),(0,[z0,z7,z308,z3,z4,z285])],[(0,[z252,z103,z2,z3,z4,z6]),(0,[z13,z0,z7,z134,z4,z6]),(0,[z0,z7,z2,z3,z800,z6]),(0,[z0,z171,z7,z2,z3,z4]),(0,[z7,z2,z3,z4,z1080,z6]),(0,[z0,z7,z502,z3,z4,z6]),(0,[z0,z7,z3,z4,z1081,z6])],[(0,[z13,z69,z252,z3,z4,z6]),(0,[z7,z94,z770,z3,z4,z6]),(0,[z0,z7,z1082,z3,z4,z6]),(0,[z0,z7,z2,z4,z1083,z6]),(0,[z0,z7,z1084,z2,z4,z6]),(0,[z0,z7,z3,z1085,z4,z6]),(0,[z0,z7,z2,z12,z6,z337])],[(0,[z14,z751,z2,z3,z4,z6]),(0,[z0,z7,z134,z123,z4,z6]),(0,[z46,z7,z3,z4,z157,z6]),(0,[z0,z7,z3,z205,z796,z6]),(0,[z0,z7,z2,z12,z738,z6])],[(0,[z319,z0,z7,z134,z4,z6]),(0,[z143,z7,z2,z82,z4,z6]),(0,[z7,z2,z3,z4,z6,z1086])],[(0,[z13,z7,z210,z4,z28,z6]),(0,[z0,z7,z2,z3,z4,z956]),(0,[z0,z2,z18,z4,z6,z341]),(0,[z0,z7,z1087,z2,z4,z6]),(0,[z0,z7,z3,z1088,z4,z6]),(0,[z1089,z7,z2,z3,z4,z6])],[(0,[z0,z25,z7,z3,z4,z6]),(0,[z13,z69,z7,z134,z4,z6]),(0,[z74,z38,z7,z82,z4,z6]),(0,[z0,z1,z2,z3,z745,z6]),(1,[z0,z2,z3,z4,z784]),(0,[z0,z7,z3,z4,z6,z797])]],
   [[(0,[z13,z547,z7,z3,z4,z6]),(0,[z13,z0,z7,z711,z4,z6]),(0,[z13,z442,z7,z3,z4,z6]),(0,[z0,z7,z3,z512,z157,z6]),(0,[z74,z7,z2,z82,z4,z6]),(0,[z0,z7,z2,z3,z4,z1090]),(0,[z0,z19,z2,z3,z4,z593]),(0,[z0,z7,z433,z2,z12,z4]),(0,[z7,z968,z502,z3,z4,z6])],[(0,[z38,z0,z7,z658,z4,z6]),(0,[z1091,z7,z2,z3,z4,z6])],[(0,[z13,z0,z7,z3,z715,z6]),(0,[z0,z1092,z2,z3,z4,z6]),(0,[z7,z2,z3,z4,z1093,z6])],[(0,[z13,z0,z7,z99,z4,z6]),(0,[z13,z0,z199,z210,z4,z6]),(0,[z13,z37,z7,z3,z68,z6]),(0,[z0,z7,z2,z3,z1061,z6]),(0,[z13,z7,z3,z685,z4,z6]),(0,[z81,z7,z95,z34,z4,z6])],[(0,[z38,z0,z7,z3,z68,z6]),(0,[z13,z0,z199,z3,z4,z226]),(0,[z13,z199,z3,z4,z28,z6]),(0,[z13,z296,z7,z210,z4,z6]),(0,[z13,z7,z134,z34,z4,z6]),(0,[z0,z1094,z7,z2,z3,z6]),(0,[z0,z7,z2,z1095,z4,z6]),(0,[z0,z19,z2,z3,z4,z42]),(1,[z0,z7,z2,z3,z749])],[(0,[z13,z7,z3,z4,z688,z6]),(0,[z0,z1096,z2,z3,z4,z6]),(0,[z46,z45,z7,z3,z4,z47]),(0,[z0,z7,z1097,z3,z4,z6])],[(0,[z38,z0,z7,z777,z4,z6]),(0,[z0,z2,z3,z4,z1098,z6])],[(0,[z13,z14,z7,z3,z68,z6]),(0,[z0,z7,z1099,z3,z4,z6]),(0,[z13,z7,z3,z4,z28,z226]),(0,[z0,z7,z3,z4,z6,z1100]),(0,[z13,z542,z7,z3,z4,z6]),(0,[z0,z7,z2,z3,z4,z1101]),(0,[z0,z433,z2,z3,z4,z10]),(0,[z0,z7,z1102,z3,z4,z6])]],
   [[(0,[z0,z107,z2,z99,z4,z6]),(0,[z13,z7,z3,z34,z4,z109]),(0,[z38,z0,z7,z3,z4,z90]),(0,[z1103,z7,z2,z3,z4,z6]),(0,[z0,z7,z728,z123,z4,z6]),(0,[z0,z7,z2,z86,z12,z6]),(0,[z0,z2,z3,z4,z1104,z6])],[(0,[z13,z0,z7,z4,z183,z6]),(0,[z13,z0,z171,z7,z3,z4]),(0,[z0,z7,z50,z210,z4,z6]),(1,[z793,z7,z3,z4,z6])],[(0,[z0,z1105,z7,z3,z4,z6]),(0,[z0,z7,z3,z4,z1106,z6]),(0,[z13,z0,z7,z3,z734,z6]),(0,[z0,z7,z134,z210,z4,z6]),(0,[z0,z7,z2,z134,z4,z226]),(0,[z230,z38,z7,z3,z136,z6]),(0,[z0,z7,z2,z3,z1107,z6]),(0,[z0,z1108,z7,z2,z3,z4]),(0,[z0,z7,z197,z3,z4,z240])],[(0,[z0,z98,z7,z3,z4,z6]),(0,[z13,z362,z7,z3,z4,z6]),(0,[z230,z7,z2,z3,z136,z6]),(0,[z793,z7,z502,z3,z4,z6])],[(0,[z13,z7,z3,z4,z703,z6]),(0,[z0,z26,z58,z3,z4,z6]),(0,[z13,z7,z3,z4,z704,z6]),(0,[z0,z7,z2,z1070,z4,z6]),(0,[z0,z7,z2,z3,z1109,z6])],[(0,[z13,z0,z199,z3,z4,z6]),(0,[z13,z0,z7,z3,z862,z6]),(0,[z13,z317,z7,z3,z4,z6]),(0,[z38,z0,z821,z3,z4,z6]),(0,[z0,z1110,z2,z3,z4,z6]),(0,[z0,z1111,z7,z3,z4,z6])],[(0,[z13,z296,z7,z3,z4,z6]),(0,[z36,z0,z199,z3,z4,z6]),(0,[z13,z7,z391,z3,z4,z6]),(0,[z7,z2,z82,z790,z4,z6])],[(0,[z13,z7,z3,z34,z67,z6]),(0,[z0,z658,z2,z4,z5,z6])]],
   [[(0,[z13,z7,z103,z3,z4,z226]),(0,[z38,z0,z7,z231,z4,z6]),(0,[z13,z7,z3,z4,z28,z6]),(0,[z74,z324,z7,z3,z4,z6]),(0,[z0,z33,z54,z2,z4,z6]),(0,[z0,z7,z2,z3,z128,z749])],[(0,[z13,z7,z3,z4,z31,z6]),(0,[z13,z452,z7,z3,z4,z6]),(0,[z13,z7,z168,z3,z4,z6]),(0,[z38,z7,z181,z3,z4,z6]),(0,[z1112,z7,z2,z3,z4,z6]),(0,[z0,z1113,z2,z3,z4,z6])],[(0,[z195,z107,z2,z3,z4,z6]),(0,[z13,z74,z199,z3,z4,z6]),(0,[z13,z0,z7,z3,z68,z226]),(0,[z0,z7,z197,z3,z4,z797])],[(0,[z13,z7,z3,z288,z4,z6]),(0,[z13,z14,z7,z231,z4,z6]),(1,[z0,z7,z3,z67,z226]),(0,[z0,z252,z2,z134,z4,z6]),(0,[z7,z2,z790,z34,z4,z6]),(0,[z0,z1,z2,z3,z203,z6]),(0,[z0,z7,z2,z3,z1114,z6]),(0,[z0,z2,z4,z6,z121,z459])],[(0,[z13,z0,z252,z3,z4,z109]),(0,[z0,z7,z1115,z3,z4,z6])],[(0,[z0,z7,z2,z3,z6,z1116]),(0,[z13,z215,z7,z3,z4,z28]),(0,[z0,z7,z3,z67,z6,z47]),(0,[z0,z7,z1117,z2,z4,z6]),(0,[z0,z7,z3,z796,z157,z6]),(0,[z0,z382,z7,z3,z4,z47]),(0,[z0,z119,z40,z2,z4,z15])],[(0,[z13,z7,z66,z3,z4,z6]),(0,[z14,z107,z2,z99,z4,z6]),(0,[z7,z168,z94,z3,z4,z6]),(0,[z0,z1118,z7,z3,z4,z6])],[(0,[z0,z33,z2,z306,z4,z6]),(0,[z0,z7,z1119,z3,z4,z6]),(0,[z0,z913,z2,z3,z4,z6]),(0,[z7,z2,z790,z3,z4,z6]),(0,[z0,z1120,z2,z3,z4,z6]),(0,[z0,z7,z87,z2,z4,z977])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 509).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1018).take 209) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1227)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [509, 509, 209] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 78).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 78).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 161).take 80).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 241).take 15).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [78, 83, 80, 15] = true :=
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

end PEqualNP.Outside.L_meta_40710

theorem PEqualNP.Outside.L_meta_40710 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808362 * 2 ^ 32 + 4240490624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808362 * 2 ^ 32 + 4240490624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40710.solve