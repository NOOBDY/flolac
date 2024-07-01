#import "@preview/curryst:0.3.0": rule, proof-tree

= Intuitionistic Logic

== Natural Deduction

=== Conjunction

$
#proof-tree(
  rule(
    name: $(and upright(I))$,
    $(A and B) and C tack.r A and (B and C)$,
    rule(
      name: $(and "EL")$,
      $(A and B) and C tack.r A$,
      rule(
        name: $(and "EL")$,
        $(A and B) and C tack.r A and B$,
        rule(
          name: "(assum)",
          $(A and B) and C tack.r (A and B) and C$
        )
      )
    ),
    rule(
      name: $(and upright(I))$,
      $(A and B) and C tack.r (B and C)$,
      rule(
        name: $(and "ER")$,
        $(A and B) and C tack.r B$,
        rule(
          name: $(and "EL")$,
          $(A and B) and C tack.r A and B$,
          rule(
            name: "(assum)",
            $(A and B) and C tack.r (A and B) and C$
          )
        )
      ),
      rule(
        name: $(and "ER")$,
        $(A and B) and C tack.r C$,
        rule(
          name: "(assum)",
          $(A and B) and C tack.r (A and B) and C$
        )
      )
    )
  )
)
$

=== Falsity

$
#proof-tree(
  rule(
    name: $(-> upright(I))$,
    $tack.r ((A or B) and not B) -> A$,
    rule(
      name: $(or upright(E))$,
      $((A or B) and not B) tack.r A$,
      rule(
        name: $(and "EL")$,
        $((A or B) and not B) tack.r (A or B)$,
        rule(
          name: "(assum)",
          $((A or B) and not B) tack.r (A or B) and not B$
        )
      ),
      rule(
        name: "(assum)",
        $((A or B) and not B), A tack.r A$,
      ),
      rule(
        name: $(bot upright(E))$,
        $((A or B) and not B), B tack.r A$,
        $((A or B) and not B), B tack.r bot$,
      )
    )
  )
)
$

=== Other

$ not not (A or not A) $

$
#proof-tree(
  rule(
    name: $(-> upright(I))$,
    $tack.r ((A or (A -> bot)) -> bot) -> bot$,
    rule(
      name: $(-> upright(E))$,
      $((A or (A -> bot)) -> bot) tack.r bot$,
      rule(
        $((A or (A -> bot)) -> bot) tack.r bot -> bot$,
        "TODO"
      ),
      rule(
        $((A or (A -> bot)) -> bot) tack.r bot$,
        "TODO"
      ),
    )
  )
)
$

$ A -> not not A $

$
#proof-tree(
  rule(
    name: $(-> upright(I))$,
    $tack.r A -> (A -> bot) -> bot$,
    rule(
      name: $(-> upright(I))$,
      $A tack.r (A -> bot) -> bot$,
      rule(
        name: $(-> upright(E))$,
        $A, (A -> bot) tack.r bot$,
        rule(
          name: "(assum)",
          $A, (A -> bot) tack.r A -> bot$,
        ),
        rule(
          name: "(assum)",
          $A, (A -> bot) tack.r A$,
        ),
      ),
    ),
  ),
)
$

