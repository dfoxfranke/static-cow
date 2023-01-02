// Copyright © 2023 Daniel Fox Franke
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

use static_cow::*;
use std::borrow::Borrow;

struct FlexIter<'a, S, E> {
    inner: S,
    index: usize,
    _phantom: CowPhantom<'a, [E]>,
}

impl<'a, 'o, S, E> ToOwning<'o> for FlexIter<'a, S, E>
where
    S: ToOwning<'o>,
    E : 'o,
{
    type Owning = FlexIter<'o, S::Owning, E>;

    fn to_owning(&self) -> Self::Owning {
        FlexIter {
            inner: self.inner.to_owning(),
            index: self.index.to_owning(),
            _phantom: self._phantom.to_owning()
        }
    }
}

impl<'a, 'o, S, E> IntoOwning<'o> for FlexIter<'a, S, E>
where
    S: IntoOwning<'o>,
    E: 'o
{
    fn into_owning(self) -> Self::Owning {
        FlexIter {
            inner: self.inner.into_owning(),
            index: self.index.into_owning(),
            _phantom: self._phantom.into_owning()
        }
    }
}

impl<'b, E> FlexIter<'b, Borrowed<'b, [E]>, E> {
    fn new(slice: &'b [E]) -> FlexIter<'b, Borrowed<'b, [E]>, E> {
        FlexIter {
            inner: Borrowed(slice),
            index: slice.len(),
            _phantom: CowPhantom::default(),
        }
    }
}

impl<'a, 'o, S, E> Iterator for FlexIter<'a, S, E>
where
    E: 'o + Clone,
    S: StaticCow<'a, 'o, [E]>,
{
    type Item = E;

    fn next(&mut self) -> Option<Self::Item> {
        // This is here to show that we can also access `inner` generically
        // through its `Deref<Target=[E]>` implementation, without having to 
        // match on `mut_if_owned()`.
        assert!(self.index <= self.inner.len());

        match self.inner.mut_if_owned() {
            // We're borrowing the slice, so we have to work inefficiently
            // by cloning its elements before we return them.
            MutIfOwned::Const(slice) => {
                if self.index == 0 {
                    None
                } else {
                    self.index -= 1;
                    Some(slice[self.index].clone())
                }
            }

            // We own the slice as a `Vec`, so we can pop elements off of it
            // without cloning.
            MutIfOwned::Mut(vec) => {
                // It's necessary to make sure we first truncate the vector
                // to `index`, because we may have already started iterating
                // before `.into_owned()` was called, and this may be our
                // first time calling `.next()` since we took ownership. Of
                // course we could have had our `into_owned` implementation
                // do this instead of doing it here.
                vec.truncate(self.index);
                let ret = vec.pop()?;
                self.index -= 1;
                Some(ret)
            }
        }
    }
}
fn main() {
    let numbers = vec![1, 2, 3, 4, 5];
    let mut borrowing_iter = FlexIter::new(numbers.borrow());

    println!("Borrowing:");
    println!("{}", borrowing_iter.next().unwrap());
    println!("{}", borrowing_iter.next().unwrap());

    let owning_iter = borrowing_iter.into_owning();
    std::mem::drop(numbers);

    println!("Owning:");
    for item in owning_iter {
        println!("{}", item);
    }
}
