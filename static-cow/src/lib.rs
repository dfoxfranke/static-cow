// Copyright © 2023 Daniel Fox Franke
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

//! This crate provides a framework of traits for writing types that are generic
//! over ownership of their contents.
//!
//! <div style="max-width: 20em; margin-left: auto; margin-right: auto;">
//! <img src="https://raw.githubusercontent.com/dfoxfranke/static-cow/10cffdd130d62af2ee0c437bc06500cfe8123417/static-cow/images/mascot.webp" alt="Mascot"/>
//! </div>
//!
//! # API Overview
//! ## `ToOwning` and `IntoOwning`
//! [`ToOwning`] and [`IntoOwning`] are the most general traits provided by this
//! crate, and are the ones that you will implement on your own types.
//! `ToOwning` is a generalization of [`std::borrow::ToOwned`](ToOwned):
//!
//! ```ignore
//! pub trait ToOwning {
//!     type Owning;
//!     fn to_owning(&self) -> Self::Owning;
//! }
//! ```
//!
//! Unlike `ToOwned`, it doesn't require that `Owning: Borrow<Self>`. Hence
//! `ToOwning` represents a type that can be converted into some version of
//! itself which owns its contents,  but which does not necessarily let you get
//! a reference to the original borrowing type back out from the owning one.
//!
//! `ToOwning` has a blanket implementation for `T where T : ToOwned + ?Sized`.
//! The blanket implementation does the obvious thing of letting `Owning =
//! Owned` and `to_owning = to_owned`.
//!
//! [`IntoOwning`], then is self-explanatory from its declaration:
//!
//! ```ignore
//! pub trait IntoOwning ToOwning + Sized {
//!     fn into_owning(self) -> Self::Owning;
//! }
//! ```
//!
//! `IntoOwning` has a blanket implementation for `T where T : Clone`, which
//! makes `into_owning` the identity function. Therefore, if your type already
//! implements [`Clone`], you get an `IntoOwning` implementation automatically.
//! If you implement `IntoOwning` manually, you cannot implement `Clone`.
//!
//! User-defined types which implement `ToOwning` and `IntoOwning` generally
//! should just call `.to_owning()` and `.into_owning()` on each of their
//! fields. Eventually there will be derive macros for this, but I haven't
//! written them yet.
//!
//! ## `StaticCow`
//! [`StaticCow`], this crate's namesake, is [`std::borrow::Cow`](Cow) lifted to
//! the type level. While `Cow` is an enum, `StaticCow` is a trait. While
//! `Cow::Borrowed` and `Cow::Owned` are enum variants, this crate's
//! [`Borrowed`] and [`Owned`] are tuple structs which implement `StaticCow` (so
//! also does `Cow`). So instead of having a struct with a field `field: Cow<'a,
//! B>`, you can declare that field as `field: S` and let `S` be a generic
//! parameter `S: StaticCow<B>`. Then, wherever the ownedness of `S` is known at
//! compile-time, the compiler can generate an appropriately-specialized version
//! of the function.
//!
//! Like `Cow`, `StaticCow` requires `B : ToOwned`, which allows it to have
//! `Deref<Target=B>` for a supertrait. `IntoOwning` is another supertrait of
//! `StaticCow`.
//!
//! ## `Idempotent`
//! Using [`Idempotent`] as a bound allows you to be generic over types that
//! implement [`IntoOwning`] but not [`ToOwned`].
//!
//! [`StaticCow`]`<B>` has [`Deref`]`<Target=B>` as a supertrait, so you can do
//! anything with a `StaticCow<B>` that you can do with a `&B`. However, in
//! order to provide this supertrait, its implementations require that `B :
//! ToOwned` so that they can rely on having `B::Owned : Borrow<B>`.
//!
//! `Idempotent` has weaker requirements, so its capabilities are necessarily
//! weaker as well, and it does not inherit from `Deref`. [`ToOwning`]` places
//! no constraints on `Owning`, which means that as far as the type system is
//! concerned, `.into_owning()` is just a completely arbitrary conversion. So,
//! you can't do anything useful with a type that might be `T` or might be
//! `T::Owning` but you don't know which, because they don't promise to have any
//! traits in common.
//!
//! `Idempotent` puts back just enough information that it can be a useful
//! bound:
//!
//! 1. It can give you either a `T` or a `T::Owning`, *and tells you which*.
//!
//! 2. It constrains `T` such that `T::Owning::Owning = T::Owning`. This means
//! that you can call `into_owning()` on it as many times as you please and it
//! can *still* give you either a `T` or a `T::Owning`.
//!
//! `Idempotent<T>` is implemented by [`Change`]`<T>`, which holds a `T`;
//! [`Keep`]`<T>`, which holds a `T::Owning`; and by [`ChangeOrKeep`]`<T>` which
//! might hold either, determined at runtime. Calling `.to_owning()` or
//! `.into_owning()` on an `Idempotent<T>` always gives a `Keep<T>`.
//!
//! # Example
//! In this example, we'll implement a slice iterator which returns the slice's
//! elements in reverse. Initially, it'll borrow the slice and clone its
//! elements when returning them. But, it will implement [`IntoOwning`], so that
//! at any time during iteration you can change it into an iterator which owns a
//! [`Vec`](alloc::vec::Vec). It will then pop the elements it returns off the
//! end of the `Vec`, without cloning them.
//!
//! For starters, we'll declare our flexible iterator:
//! ```ignore
//! struct FlexIter<S, E> {
//!     inner: S,
//!     index: usize,
//!     _phantom: PhantomData<[E]>,
//! }
//! ```
//!
//! `E` is the type of the slice's elements. And although the constraint doesn't
//! appear in the struct declaration, `S` will be an implementation of
//! `StaticCow<[E]>`. Concretely, `S` will be either `Borrowed<'b, [E]>`, which
//! wraps a `&'b [E]`, or it will be `Owned<[E]>`, which wraps a `Vec<E>`.
//! `index` is one greater than the index of the next element we'll return, and
//! `_phantom` is a zero-sized object which has to be there to satisfy the
//! typechecker by having the parameter `E` appear somewhere in the struct's
//! fields.
//!
//! Now we'll create [`ToOwning`] and [`IntoOwning`] instances for `FlexIter`.
//! ```ignore
//! impl<S, E> ToOwning for FlexIter<S, E>
//! where
//!     S: ToOwning,
//! {
//!     type Owning = FlexIter<S::Owning, E>;
//!
//!     fn to_owning(&self) -> Self::Owning {
//!         FlexIter {
//!             inner: self.inner.to_owning(),
//!             index: self.index.to_owning(),
//!             _phantom: self._phantom.to_owning()
//!         }
//!     }
//! }
//!
//! impl<S, E> IntoOwning for FlexIter<S, E>
//! where
//!     S: IntoOwning,
//! {
//!     fn into_owning(self) -> Self::Owning {
//!         FlexIter {
//!             inner: self.inner.into_owning(),
//!             index: self.index.into_owning(),
//!             _phantom: self._phantom.into_owning()
//!         }
//!     }
//! }
//! ```
//!
//! You can see that these implementations are complely rote: we give an
//! `Owning` type which is the same as `Self` but with `S` replaced by
//! `S::Owning`, and `to_owning` and `into_owning` methods which simply apply
//! the same method to each of their fields.
//!
//! Now we give a constructor for a borrowing iterator, which realizes
//! `StaticCow<[E]>` with `Borrowed<'b, [E]>`.
//!
//! ```ignore
//! impl<'b, E> FlexIter<'b, Borrowed<'b, [E]>, E> {
//!     fn new(slice: &'b [E]) -> FlexIter<'b, Borrowed<'b, [E]>, E> {
//!         FlexIter {
//!             inner: Borrowed(slice),
//!             index: slice.len(),
//!             _phantom: CowPhantom::default(),
//!         }
//!     }
//! }
//! ```
//!
//! And now we can implement `Iterator`:
//!
//! ```ignore
//! impl<S, E> Iterator for FlexIter<S, E>
//! where
//!     E: Clone,
//!     S: StaticCow<[E]>,
//! {
//!     type Item = E;

//!     fn next(&mut self) -> Option<Self::Item> {
//!         // This is here to show that we can also access `inner` generically
//!         // through its `Deref<Target=[E]>` implementation, without having to
//!         // match on `mut_if_owned()`.
//!         assert!(self.index <= self.inner.len());
//!
//!         match self.inner.mut_if_owned() {
//!             // We're borrowing the slice, so we have to work inefficiently
//!             // by cloning its elements before we return them.
//!             MutIfOwned::Const(slice) => {
//!                 if self.index == 0 {
//!                     None
//!                 } else {
//!                     self.index -= 1;
//!                     Some(slice[self.index].clone())
//!                 }
//!             }
//!             // We own the slice as a `Vec`, so we can pop elements off of it
//!             // without cloning.
//!             MutIfOwned::Mut(vec) => {
//!                 // It's necessary to make sure we first truncate the vector
//!                 // to `index`, because we may have already started iterating
//!                 // before `.into_owned()` was called, and this may be our
//!                 // first time calling `.next()` since we took ownership. Of
//!                 // course we could have had our `into_owned` implementation
//!                 // do this instead of doing it here.
//!                 vec.truncate(self.index);
//!                 let ret = vec.pop()?;
//!                 self.index -= 1;
//!                 Some(ret)
//!             }
//!         }
//!     }
//! }
//! ```
//!
//! And now let's see it in action:
//!
//! ```ignore
//! fn main() {
//!     let numbers = vec![1, 2, 3, 4, 5];
//!     let mut borrowing_iter = FlexIter::new(numbers.borrow());
//!
//!     println!("Borrowing:");
//!     println!("{}", borrowing_iter.next().unwrap());
//!     println!("{}", borrowing_iter.next().unwrap());
//!
//!     let owning_iter = borrowing_iter.into_owning();
//!     std::mem::drop(numbers);
//!
//!     println!("Owning:");
//!     for item in owning_iter {
//!         println!("{}", item);
//!     }
//! }
//! ```
//!
//! Running this, we get the expected result:
//! ```text
//! Borrowing:
//! 5
//! 4
//! Owning:
//! 3
//! 2
//! 1
//! ```
//!
//! This example is also available as `examples/flex_iter.rs` in the sources of
//! this crate.

#![warn(missing_docs)]
#![no_std]
extern crate alloc;
use alloc::borrow::{Borrow, BorrowMut, Cow, ToOwned};
use core::ops::{Deref, DerefMut};

///A generalization of [`ToOwned`].
///
/// `ToOwning` is weaker than `ToOwned` because there is no constraint of
/// `Owning : Borrow<Self>` as there is on `ToOwned::Owned`. Thus, `ToOwning`
/// represents a type which can be converted from a reference into a related
/// type that owns its contents, but unlike `ToOwned` doesn't necessarily let
/// you get a reference to the original type back out.
///
/// `ToOwning` has a blanket implementation for `T where T : ToOwned`, wherein
/// `Owning = Owned` and `to_owning = to_owned`. User-defined types which
/// implement `ToOwning` but not `ToOwned` typically should do so by calling
/// `.to_owning()` on all their fields.
pub trait ToOwning {
    /// The resulting type after obtaining ownership of `self`'s contents.
    type Owning;
    /// Creates an object which owns its contents from one which borrows them.
    fn to_owning(&self) -> Self::Owning;
}

impl<B> ToOwning for B
where
    B: ToOwned + ?Sized,
{
    type Owning = B::Owned;

    #[inline]
    fn to_owning(&self) -> Self::Owning {
        self.to_owned()
    }
}

/// A trait for types that can be converted into ones which own their contents.
///
/// `IntoOwning` has a blanket implementation for `T where T : Clone`, wherein
/// `into_owning` is the identity function. User-defined types which implement
/// `IntoOwning` but not [`Clone`] typically should do so by calling
/// `into_owning()` on all their fields.
pub trait IntoOwning: ToOwning + Sized {
    /// Converts an object which owns its contents into one which borrows them.
    fn into_owning(self) -> Self::Owning;
}

impl<B> IntoOwning for B
where
    B: Clone,
{
    #[inline]
    fn into_owning(self) -> Self::Owning {
        self
    }
}

/// Trait for [`Cow`]-like types whose owned-ness might be known at
/// compile-time.
///
/// [`StaticCow`] is [`std::borrow::Cow`](Cow) lifted to the type level. While
/// `Cow` is an enum, `StaticCow` is a trait. While `Cow::Borrowed` and
/// `Cow::Owned` are enum variants, this crate's [`Borrowed`] and [`Owned`] are
/// tuple structs which implement `StaticCow` (so also does `Cow`). oS instead
/// of having a struct with a field `field: Cow<'a, B>`, you can declare that
/// field as `field: S` and let `S` be a generic parameter `S: StaticCow<B>`
pub trait StaticCow<B>: Deref<Target = B> + IntoOwning
where
    B: ToOwned + ?Sized,
{
    /// Returns either an immutable reference to an object that is borrowed, or
    /// a mutable reference to one which is owned.
    ///
    /// This method is useful if you are implementing an object that does not
    /// need to mutate its contents, but can implement optimizations if allowed
    /// to.
    ///
    /// [`Borrowed`]::`mut_if_owned()` always returns `MutIfOwned::Const(_)`,
    /// [`Owned`]::`mut_if_owned()` always returns `MutIfOwned::Mut(_)`, and
    /// both of these method implementations are compiled with
    /// `#[inline(always)]`. Therefore, if you have code that is generic over
    /// `StaticCow`, there is zero cost to calling `.mut_if_owned()` and
    /// matching on the result, because the dead branch will reliably be
    /// optimized out.
    fn mut_if_owned(&mut self) -> MutIfOwned<'_, B>;

    /// Returns true iff the data is owned, i.e. if `self.into_owning()` would
    /// be a no-op.
    fn is_owned(&self) -> bool;

    /// Returns true iff the data is borrowed, i.e. if `self.into_owning()`
    /// would clone it.
    fn is_borrowed(&self) -> bool {
        !self.is_owned()
    }

    /// Converts `self` into its dynamic equivalent as a [`Cow`].
    fn into_cow<'a>(self) -> Cow<'a, B>
    where
        Self: 'a,
        Self::Owning: 'a;

    /// Converts `self` into a `B::Owned`, cloning only if necessary.
    fn into_owned(self) -> B::Owned;
}

#[derive(Debug, PartialEq, Eq)]
/// Either an immutable reference to a borrowing object, or a mutable reference to
/// an owning one.
///
/// Returned by [`StaticCow::mut_if_owned`].
pub enum MutIfOwned<'a, B>
where
    B: ToOwned + ?Sized,
{
    /// An immutable reference to a borrowing object.
    Const(&'a B),
    /// A mutable reference to an owning object.
    Mut(&'a mut B::Owned),
}

/// A [`StaticCow`] implementation which wraps an immutable reference.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Borrowed<'b, B: ?Sized>(pub &'b B);

/// A [`StaticCow`] implementation which wraps an owned type.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Owned<B>(pub B::Owning)
where
    B: ToOwning + ?Sized;

impl<'b, B: ?Sized> AsRef<B> for Borrowed<'b, B> {
    fn as_ref(&self) -> &B {
        self.0
    }
}

impl<'b, B: ?Sized> Borrow<B> for Borrowed<'b, B> {
    fn borrow(&self) -> &B {
        self.0
    }
}

impl<'b, B: ?Sized> Deref for Borrowed<'b, B> {
    type Target = B;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'b, B> ToOwning for Borrowed<'b, B>
where
    B: ToOwning + ?Sized,
{
    type Owning = Owned<B>;

    #[inline]
    fn to_owning(&self) -> Self::Owning {
        Owned(self.0.to_owning())
    }
}

impl<'b, B> IntoOwning for Borrowed<'b, B>
where
    B: ToOwning + ?Sized,
{
    #[inline]
    fn into_owning(self) -> Self::Owning {
        Owned(self.0.to_owning())
    }
}

impl<'b, B> StaticCow<B> for Borrowed<'b, B>
where
    B: ToOwned + ?Sized,
{
    #[inline]
    fn is_owned(&self) -> bool {
        false
    }

    #[inline(always)]
    fn mut_if_owned(&mut self) -> MutIfOwned<'_, <Self as Deref>::Target> {
        MutIfOwned::Const(self.0)
    }
    #[inline]
    fn into_cow<'a>(self) -> Cow<'a, B>
    where
        Self: 'a,
        Self::Owning: 'a,
    {
        Cow::Borrowed(self.0)
    }

    fn into_owned(self) -> B::Owned {
        self.0.to_owned()
    }
}

impl<B> Deref for Owned<B>
where
    B: ToOwning + ?Sized,
    B::Owning: Borrow<B>,
{
    type Target = B;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0.borrow()
    }
}

impl<B> DerefMut for Owned<B>
where
    B: ToOwning + ?Sized,
    B::Owning: BorrowMut<B>,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.borrow_mut()
    }
}

impl<B> ToOwning for Owned<B>
where
    B: ToOwning + ?Sized,
    B::Owning: Borrow<B>,
{
    type Owning = Self;

    #[inline]
    fn to_owning(&self) -> Self::Owning {
        Owned(self.0.borrow().to_owning())
    }
}

impl<B> IntoOwning for Owned<B>
where
    B: ToOwning + ?Sized,
    B::Owning: Borrow<B>,
{
    #[inline]
    fn into_owning(self) -> Self::Owning {
        self
    }
}

impl<B> StaticCow<B> for Owned<B>
where
    B: ToOwned + ?Sized,
{
    #[inline]
    fn is_owned(&self) -> bool {
        true
    }

    #[inline(always)]
    fn mut_if_owned(&mut self) -> MutIfOwned<'_, B> {
        MutIfOwned::Mut(&mut self.0)
    }

    #[inline]
    fn into_cow<'a>(self) -> Cow<'a, B>
    where
        Self: 'a,
        Self::Owning: 'a,
    {
        Cow::Owned(self.0)
    }

    #[inline]
    fn into_owned(self) -> <B as ToOwned>::Owned {
        self.0
    }
}

impl<'a, B> StaticCow<B> for Cow<'a, B>
where
    B: 'a + ToOwned + ?Sized,
{
    #[inline]
    fn is_owned(&self) -> bool {
        match self {
            Cow::Borrowed(_) => false,
            Cow::Owned(_) => true,
        }
    }

    #[inline]
    fn mut_if_owned(&mut self) -> MutIfOwned<'_, B> {
        match self {
            Cow::Borrowed(borrowed) => MutIfOwned::Const(*borrowed),
            Cow::Owned(owned) => MutIfOwned::Mut(owned),
        }
    }
    #[inline]
    fn into_cow<'b>(self) -> Cow<'b, B>
    where
        Self: 'b,
    {
        self
    }

    #[inline]
    fn into_owned(self) -> <B as ToOwned>::Owned {
        self.into_owned()
    }
}

/// A trait which guarantees `Self::Owning::Owning = Self::Owning`.
///
/// Using `Idempotent` as a bound allows you to be generic over types that
/// implement [`IntoOwning`] but not [`ToOwned`].
///
/// [`StaticCow`]`<B>` has [`Deref`]`<Target=B>` as a supertrait, so you can do
/// anything with a `StaticCow<B>` that you can do with a `&B`. However, in
/// order to provide this supertrait, its implementations require that `B :
/// ToOwned` so that they can rely on having `B::Owned : Borrow<B>`.
///
/// `Idempotent` has weaker requirements, so its capabilities are necessarily
/// weaker as well, and it does not inherit from `Deref`. [`ToOwning`]
/// places no constraints on `Owning` which means that as far as the type system
/// is concerned, `.into_owning()` is just a completely arbitrary conversion.
/// So, you can't do anything useful with a type that might be `T` or might be
/// `T::Owning` but you don't know which, because they don't promise to have any
/// traits in common.
///
/// `Idempotent` puts back just enough information that it can be a useful
/// bound:
///
/// 1. It can give you either a `T` or a `T::Owning`, *and tells you which*.
///
/// 2. It constrains `T` such that `T::Owning::Owning = T::Owning`. This means
/// that you can call `into_owning()` on it as many times as you please and it
/// can *still* give you either a `T` or a `T::Owning`.
///
/// `Idempotent<T>` is implemented by [`Change`]`<T>`, which holds a `T`;
/// [`Keep`]`<T>`, which holds a `T::Owning`; and by [`ChangeOrKeep`]`<T>` which
/// might hold either, determined at runtime. Calling `.to_owning()` or
/// `.into_owning()` on an `Idempotent<T>` always gives a `Keep<T>`.
pub trait Idempotent<T>: IntoOwning<Owning = Keep<T>>
where
    T: ToOwning,
    T::Owning: ToOwning<Owning = T::Owning>,
{
    /// Get a reference to either a `T` or a `T::Owning`.
    fn to_ref(&self) -> IdemRef<'_, T>;

    /// Get a mutable reference to either a `T` or a `T::Owning`.
    fn to_mut(&mut self) -> IdemMut<'_, T>;

    /// Converts `self` into a `T::Owning`; equivalent to `into_owning().0`.
    #[inline]
    fn into_kept(self) -> T::Owning {
        self.into_owning().0
    }
}

/// Provides an inmutable reference to either a `T` or a `T::Owning`.
#[derive(Debug, PartialEq, Eq)]
pub enum IdemRef<'a, T>
where
    T: ToOwning,
{
    /// Provides a mutable reference to a `T`.
    Change(&'a T),
    /// Provides a mutable reference to a `T::Owning`.
    Keep(&'a T::Owning),
}

/// Provides a mutable reference to either a `T` or a `T::Owning`.
#[derive(Debug, PartialEq, Eq)]
pub enum IdemMut<'a, T>
where
    T: ToOwning,
{
    /// Provides a mutable reference to a `T`.
    Change(&'a mut T),
    /// Provides a mutable reference to a `T::Owning`.
    Keep(&'a mut T::Owning),
}

/// An [`Idempotent`] implementation which wraps a type that is already
/// `Owning`.
///
/// `Keep` has an additional function outside of its use with `Idempotent`,
/// which is that it implements [`Clone`]. Recall that all types which implement
/// `Clone` have a blanket implementation of [`IntoOwning`] which is just the
/// identity function. Contrapositively, therefore, any type with a
/// *non-trivial* `IntoOwning` implementation cannot implement `Clone`. Usually,
/// the conversion target of a struct's or enum's `IntoOwning` implementation is
/// the same struct or enum with different generic parameters. You might wish to
/// be able to clone such an object after it has already been converted into its
/// owning form, but this is not possible because it breaks Rust's rules about
/// conflicting trait implementations. If you already know you have a type that
/// `IntoOwning` (and therefore implements its supertrait [`ToOwning`]), then you
/// can work around this by calling `.to_owning()` instead of `.clone()` and
/// this will do the same thing. However, if you need to pass the object to
/// something whose generic bounds require a `Clone` implementation, wrapping it
/// with `Keep` can be a convenient solution.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Keep<T>(pub T::Owning)
where
    T: ToOwning;

/// An [`Idempotent`] implementation whose owning-ness is determined at runtime.
pub enum ChangeOrKeep<T>
where
    T: ToOwning,
{
    /// A `T` that has not yet been transformed.
    Change(T),
    /// A `T::Owning` which has already been transformed from a `T`.
    Keep(T::Owning),
}

/// An [`Idempotent`] implementation which wraps a type that may yet be converted to `Owning`.
pub struct Change<T>(pub T);
impl<T> Deref for Change<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Change<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> ToOwning for Change<T>
where
    T: ToOwning,
{
    type Owning = Keep<T>;

    fn to_owning(&self) -> Self::Owning {
        Keep(self.0.to_owning())
    }
}

impl<T> IntoOwning for Change<T>
where
    T: IntoOwning,
{
    fn into_owning(self) -> Self::Owning {
        Keep(self.0.into_owning())
    }
}

impl<T> Idempotent<T> for Change<T>
where
    T: IntoOwning,
    T::Owning: ToOwning<Owning = T::Owning>,
{
    #[inline(always)]
    fn to_ref(&self) -> IdemRef<'_, T> {
        IdemRef::Change(&self.0)
    }
    #[inline(always)]
    fn to_mut(&mut self) -> IdemMut<'_, T> {
        IdemMut::Change(&mut self.0)
    }
}

impl<T> Deref for Keep<T>
where
    T: ToOwning,
{
    type Target = T::Owning;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Keep<T>
where
    T: ToOwning,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> Clone for Keep<T>
where
    T: ToOwning,
    T::Owning: ToOwning<Owning = T::Owning>,
{
    #[inline]
    fn clone(&self) -> Self {
        Keep(self.0.to_owning())
    }
}

impl<T> Idempotent<T> for Keep<T>
where
    T: IntoOwning,
    T::Owning: ToOwning<Owning = T::Owning>,
{
    #[inline(always)]
    fn to_ref(&self) -> IdemRef<'_, T> {
        IdemRef::Keep(&self.0)
    }

    #[inline(always)]
    fn to_mut(&mut self) -> IdemMut<'_, T> {
        IdemMut::Keep(&mut self.0)
    }
}

impl<T> ToOwning for ChangeOrKeep<T>
where
    T: ToOwning,
    T::Owning: ToOwning<Owning = T::Owning>,
{
    type Owning = Keep<T>;

    fn to_owning(&self) -> Self::Owning {
        match self {
            ChangeOrKeep::Change(o) => Keep(o.to_owning()),
            ChangeOrKeep::Keep(o) => Keep(o.to_owning()),
        }
    }
}

impl<T> IntoOwning for ChangeOrKeep<T>
where
    T: IntoOwning,
    T::Owning: ToOwning<Owning = T::Owning>,
{
    fn into_owning(self) -> Self::Owning {
        match self {
            ChangeOrKeep::Change(o) => Keep(o.into_owning()),
            ChangeOrKeep::Keep(o) => Keep(o),
        }
    }
}

impl<T> Idempotent<T> for ChangeOrKeep<T>
where
    T: IntoOwning,
    T::Owning: ToOwning<Owning = T::Owning>,
{
    fn to_ref(&self) -> IdemRef<'_, T> {
        match self {
            ChangeOrKeep::Change(o) => IdemRef::Change(o),
            ChangeOrKeep::Keep(o) => IdemRef::Keep(o),
        }
    }

    fn to_mut(&mut self) -> IdemMut<'_, T> {
        match self {
            ChangeOrKeep::Change(o) => IdemMut::Change(o),
            ChangeOrKeep::Keep(o) => IdemMut::Keep(o),
        }
    }
}

/// Constructs a [`Keep`], assisting with type inference.
///
/// This function takes an object `o : T` such that `T::Owning = T`, and gives
/// you back a `Keep<T>`. It is most useful when you have a `T` that implements
/// `ToOwning<Owning=T>` but not `Clone`, and you need to wrap it in something
/// that will give you a `Clone` implementation.
///
/// You should *not* use this function in the constructor of a type that is
/// generic over `Idempotent<T>` and give it a `T::Owning`, because that will
/// result in a `Keep<T::Owning>` when what you want is a `Keep<T>`. In this
/// context you should use `Keep`'s primitive constructor instead.
pub fn keep<T>(o: T) -> Keep<T>
where
    T: ToOwning<Owning = T>,
{
    Keep(o)
}
