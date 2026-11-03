#[cfg(creusot)]
use creusot_std::prelude::*;

use OptionExt;

impl<T> OptionExt<T> for Option<T> {
    #[cfg(creusot)]
    #[logic]
    #[ensures(result == self)]
    fn option_model(self) -> Option<T> { self }


    #[cfg(not(creusot))]
    fn contains<U>(&self, x: &U) -> bool where U: PartialEq<T> {
        match *self {
            Some(ref y) => x == y,
            None => false,
        }
    }

    #[inline]
    #[cfg(not(creusot))]
    fn map_or2<U, F: FnOnce(T) -> U>(self, f: F, default: U) -> U {
        self.map_or(default, f)
    }

    #[inline]
    #[cfg_attr(creusot, requires(match self { None => default.precondition(()), Some(t) => f.precondition((t,)) }))]
    #[cfg_attr(creusot, ensures(match self { None => resolve(f) && default.postcondition_once((), result), Some(t) => resolve(default) && f.postcondition_once((t,), result) }))]
    fn map_or_else2<U, F: FnOnce(T) -> U, D: FnOnce() -> U>(self, f: F, default: D) -> U {
        self.map_or_else(default, f)
    }
}
