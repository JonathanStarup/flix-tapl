mod BoolArithmetic {
    use Term.{True, False, IfThenElse}

    // Order is defined to use Sets
    pub enum Term with Eq, ToString, Order {
        case True
        case False
        case IfThenElse(Term, Term, Term)
        case Zero
        case Succ(Term)
        case Pred(Term)
        case IsZero(Term)
    }

    mod Term {
        use StepError.noRuleFor

        pub def consts(t: Term): Set[Term] = {
            use Set.{singleton, union};
            match t {
                case True => singleton(True)
                case False => singleton(False)
                case Zero => singleton(Zero)
                case Succ(t1) => consts(t1)
                case Pred(t1) => consts(t1)
                case IsZero(t1) => consts(t1)
                case IfThenElse(t1, t2, t3) => consts(t1) `union` consts(t2) `union` consts(t3)
            }
        }

        pub def size(t: Term): Int32 = {
            match t {
                case True => 1
                case False => 1
                case Zero => 1
                case Succ(t1) => size(t1) + 1
                case Pred(t1) => size(t1) + 1
                case IsZero(t1) => size(t1) + 1
                case IfThenElse(t1, t2, t3) => size(t1) + size(t2) + size(t3) + 1
            }
        }

        pub def depth(t: Term): Int32 = {
            use Int32.max;
            match t {
                case True => 1
                case False => 1
                case Zero => 1
                case Succ(t1) => depth(t1) + 1
                case Pred(t1) => depth(t1) + 1
                case IsZero(t1) => depth(t1) + 1
                case IfThenElse(t1, t2, t3) => (size(t1) `max` size(t2) `max` size(t3)) + 1
            }
        }

        pub def isValue(t: Term): Bool = match t {
            case True => true
            case False => true
            case Zero => true
            case Succ(t1) => isNumericValue(t1)

            case IfThenElse(_, _, _) => false
            case Pred(_) => false
            case IsZero(_) => false
        }

        pub def isNumericValue(t: Term): Bool = match t {
            case Zero => true
            case Succ(t1) => isNumericValue(t1)

            case True => false
            case False => false
            case IfThenElse(_, _, _) => false
            case Pred(_) => false
            case IsZero(_) => false
        }

        pub eff StepError {
            pub def noRuleFor(t: Term): Void
        }

        pub def handleError(f: a -> b \ StepError): a -> Result[String, b] = {
            x -> try Ok(f(x)) with StepError {
                def noRuleFor(errorTerm, _k) = Err("No rule for ${errorTerm}")
            }
        }

        pub def eval(t: Term): Term \ StepError = match t {
            case True => do noRuleFor(t)
            case False => do noRuleFor(t)
            case IfThenElse(True, t2, _t3) => t2
            case IfThenElse(False, _t2, t3) => t3
            case IfThenElse(t1, t2, t3) => IfThenElse(eval(t1), t2, t3)
            case Zero => do noRuleFor(t)
            case Succ(t1) => Succ(eval(t1))
            case Pred(Zero) => Zero
            case Pred(Succ(nv)) if isNumericValue(nv) => nv
            case Pred(t1) => Pred(eval(t1))
            case IsZero(Zero) => True
            case IsZero(Succ(nv)) if isNumericValue(nv) => False
            case IsZero(t1) => IsZero(eval(t1))
        }

        pub def isNormalForm(t: Term): Bool = {
            match handleError(eval)(t) {
                case Ok(_) => false
                case Err(_) => true
            }
        }

        /// Step as many times as possible
        pub def evalTransitive(t: Term): Term = {
            match handleError(eval)(t) {
                case Ok(nextTerm) => evalTransitive(nextTerm)
                case Err(_) => t
            }
        }

        pub def isStuck(t: Term): Bool = {
            isNormalForm(t) and not isValue(t)
        }

        /// Some rules are different to achieve exhaustive pattern matching
        pub def evalBigStep(t: Term): Term \ StepError = {
            match t {
                case True => True
                case False => False
                case Zero => Zero

                case IfThenElse(t1, t2, t3) =>
                    match evalBigStep(t1) {
                        case True => evalBigStep(t2)
                        case False => evalBigStep(t3)
                        case other => do noRuleFor(IfThenElse(other, t2, t3))
                    }
                case Succ(t1) =>
                    match evalBigStep(t1) {
                        case nv if isNumericValue(nv) => Succ(nv)
                        case other => do noRuleFor(Succ(other))
                    }
                case Pred(t1) =>
                    match evalBigStep(t1) {
                        case Zero => Zero
                        case Succ(nv) if isNumericValue(nv) => nv
                        case other => do noRuleFor(Pred(other))
                    }
                case IsZero(t1) =>
                    match evalBigStep(t1) {
                        case Zero => True
                        case Succ(nv) if isNumericValue(nv) => False
                        case other => do noRuleFor(IsZero(other))
                    }
            }
        }

        //
        // Examples and Tests
        //

        @Test
        pub def example353(): Bool \ IO = {
            let s = IfThenElse(True, False, False);
            let t = IfThenElse(s, True, True);
            let u = IfThenElse(False, True, True);
            let expected = IfThenElse(u, False, False);
            match handleError(eval)(IfThenElse(t, False, False)) {
                case Err(msg) => println(msg); false
                case Ok(res) =>
                    println("found    ${res}");
                    println("expected ${expected}");
                    Assert.eq(expected, res)
            }
        }

        @Test
        pub def example3513(): Bool \ IO = {
            let expected = Pred(Succ(Zero));
            match handleError(eval)(Pred(Succ(Pred(Zero)))) {
                case Err(msg) => println(msg); false
                case Ok(res) =>
                    println("found    ${res}");
                    println("expected ${expected}");
                    Assert.eq(expected, res)
            }
        }

        @Test
        pub def testBigStep(): Bool \ IO = {
            let input = Succ(IfThenElse(IsZero(Pred(Succ(Succ(Zero)))), Succ(Zero), Pred(Pred(Zero))));
            let bigOutput = handleError(evalBigStep)(input);
            let smallRes = evalTransitive(input);
            let expected = Succ(Zero);
            match bigOutput {
                case Err(msg) => println(msg); false
                case Ok(bigRes) =>
                    println("big      ${bigRes}");
                    println("small    ${smallRes}");
                    println("expected ${expected}");
                    Assert.eq(expected, bigRes) and
                    Assert.eq(expected, smallRes)
            }
        }

    }

}
