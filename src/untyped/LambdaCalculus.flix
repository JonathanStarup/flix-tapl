mod LambdaCalculus {

    pub enum Term with Eq, ToString {
        case Var(String)
        case Abs(String, Term)
        case App(Term, Term)
    }

    mod Term {

        pub def mkAbs(args: List[String], t: Term): Term = {
            (t, args) ||> List.foldRight(arg -> acc -> Abs(arg, acc))
        }

        pub def mkApp(fun: Term, args: List[Term]): Term = {
            (fun, args) ||> List.foldLeft(acc -> arg -> App(acc, arg))
        }

        // Booleans

        pub def tru(): Term = mkAbs("t" :: "f" :: Nil, Var("t"))

        pub def fls(): Term = mkAbs("t" :: "f" :: Nil, Var("f"))

        pub def land(): Term = mkAbs("b" :: "c" :: Nil, mkApp(Var("b"), Var("c") :: fls() :: Nil))

        pub def lor(): Term = mkAbs("b" :: "c" :: Nil, mkApp(Var("b"), tru() :: Var("c") :: Nil))

        pub def lnot(): Term = Abs("b", mkApp(Var("b"), fls() :: tru() :: Nil))

        // Pairs

        pub def pair(): Term = mkAbs("f" :: "s" :: "b" :: Nil, mkApp(Var("b"), Var("f") :: Var("s") :: Nil))

        pub def fst(): Term = Abs("p", App(Var("p"), tru()))

        pub def snd(): Term = Abs("p", App(Var("p"), fls()))

        // Numerals

        pub def zero(): Term = mkAbs("s" :: "z" :: Nil, Var("z"))

        pub def one(): Term = mkAbs("s" :: "z" :: Nil, App(Var("s"), Var("z")))

        pub def two(): Term = mkAbs("s" :: "z" :: Nil, App(Var("s"), App(Var("s"), Var("z"))))

        pub def three(): Term = mkAbs("s" :: "z" :: Nil, App(Var("s"), App(Var("s"), Var("z"))))

        pub def scc(): Term = mkAbs("n" :: "s" :: "z" :: Nil, App(Var("s"), mkApp(Var("n"), Var("s") :: Var("z") :: Nil)))

        pub def plus(): Term = mkAbs("m" :: "n" :: "s" :: "z" :: Nil, mkApp(Var("m"), Var("s") :: mkApp(Var("n"), Var("s") :: Var("z") :: Nil) :: Nil))

        pub def times(): Term = mkAbs("m" :: "n" :: Nil, mkApp(Var("m"), App(plus(), Var("n")) :: zero() :: Nil))

        pub def power(): Term = ??? // mkAbs("m" :: "n" :: Nil, mkApp(Var("n"), App(times(), Var("m")) :: one() :: Nil))

        pub def isZro(): Term = Abs("m", mkApp(Var("m"), Abs("x", fls()) :: tru() :: Nil))

        pub def zz(): Term = mkApp(pair(), zero() :: zero() :: Nil)

        pub def ss(): Term = Abs("p", mkApp(pair(), App(snd(), Var("p")) :: mkApp(plus(), one() :: (App(snd(), Var("p"))) :: Nil) :: Nil))

        pub def prd(): Term = Abs("m", App(fst(), mkApp(Var("m"), ss() :: zz() :: Nil)))

        pub def equal(): Term = ???

        pub def subtract(): Term = ???

        // fixpoint

        pub def omega(): Term = App(Abs("x", App(Var("x"), Var("x"))), Abs("x", App(Var("x"), Var("x"))))

        // call by value fixpoint
        pub def fixx(): Term = {
            let body = Abs("x", App(Var("f"), Abs("y", mkApp(Var("x"), Var("x") :: Var("y") :: Nil))));
            Abs("f", App(body, body))
        }


        pub def size(t: Term): Int32 = match t {
            case Var(_) => 1
            case Abs(_, t1) => size(t1) + 1
            case App(t1, t2) => size(t1) + size(t2) + 1
        }

        pub def fv(t: Term): Set[String] = {
            use Set.{singleton, difference, union};
            match t {
                case Var(x) => singleton(x)
                case Abs(x, t1) => fv(t1) `difference` singleton(x)
                case App(t1, t2) => fv(t1) `union` fv(t2)
            }
        }

        pub def eval(t: Term): Term = t // todo






        @Test
        pub def example01(): Bool = {
            let input = App(App(land(), tru()), tru());
            let expected = tru();
            Assert.eq(expected, eval(input))
        }

        @Test
        pub def example02(): Bool = {
            let input = App(App(land(), tru()), fls());
            let expected = fls();
            Assert.eq(expected, eval(input))
        }

        @Test
        pub def example03(): Bool = {
            let input = App(fst(), App(App(pair(), Var("v")), Var("w")));
            let expected = fls();
            Assert.eq(expected, eval(input))
        }

        @Test
        pub def example04(): Bool = {
            let input = App(isZro(), one());
            let expected = fls();
            Assert.eq(expected, eval(input))
        }

        @Test
        pub def example05(): Bool = {
            let input = App(isZro(), mkApp(times(), zero() :: two() :: Nil));
            let expected = tru();
            Assert.eq(expected, eval(input))
        }

        @Test
        pub def example06(): Bool = {
            let input = mkApp(equal(), three() :: three() :: Nil);
            let expected = tru();
            Assert.eq(expected, eval(input))
        }

        @Test
        pub def example07(): Bool = {
            let input = mkApp(equal(), three() :: two() :: Nil);
            let expected = fls();
            Assert.eq(expected, eval(input))
        }

    }

}
