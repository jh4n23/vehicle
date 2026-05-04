@network
f : Tensor Real [2] -> Tensor Real [2]


@property
expandedExpr : Bool
expandedExpr = forall x . [0, 0] < x < [1, 1] => x ! 0 >= f x ! 0

@property
parallel : Bool
-- parallel = (forall x . 0 < x < 1 => f x >= 0) and (exists y . 0 < y < 1 and f y >= 5)
parallel = True