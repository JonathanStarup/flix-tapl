mod Util {

    pub def assertRes(expected: t, actual: Result[error, t]): Bool with ToString[t], ToString[error], Eq[t], Eq[error] = {
        match actual {
            case Err(msg) => Assert.eq(Ok(()), Err(msg))
            case Ok(v) => Assert.eq(expected, v)
        }
    }

}
