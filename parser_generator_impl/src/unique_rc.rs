use std::{
  borrow::Borrow,
  fmt::{Debug, Display, Pointer},
  hash::Hash,
  ops::Deref,
  pin::Pin,
  rc::{Rc, Weak},
};

pub struct UniqueWeak<T: ?Sized> {
  ptr: Weak<T>,
}

impl<T> UniqueWeak<T> {
  pub fn upgrade(&self) -> UniqueRc<T> {
    let rc = self.ptr.upgrade().unwrap();
    unsafe { Pin::new_unchecked(rc) }.into()
  }
}

impl<T: ?Sized> Clone for UniqueWeak<T> {
  fn clone(&self) -> Self {
    Self {
      ptr: self.ptr.clone(),
    }
  }
}

impl<T: Debug + ?Sized> Debug for UniqueWeak<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    Debug::fmt(&self.ptr, f)
  }
}

pub struct UniqueRc<T: ?Sized> {
  rc: Pin<Rc<T>>,
}

impl<T: ?Sized> UniqueRc<T> {
  pub fn new(val: T) -> UniqueRc<T>
  where
    T: Sized,
  {
    Self {
      rc: unsafe { Pin::new_unchecked(Rc::new(val)) },
    }
  }

  pub fn as_rc(&self) -> &Pin<Rc<T>> {
    &self.rc
  }

  pub fn as_mut_rc(&mut self) -> &mut Pin<Rc<T>> {
    &mut self.rc
  }

  pub fn raw_pointer(&self) -> *const T {
    &*self.rc as *const T
  }

  fn raw_pointer_usize(&self) -> usize {
    self.raw_pointer() as *const () as usize
  }

  pub fn downgrade(&self) -> UniqueWeak<T> {
    UniqueWeak {
      ptr: Rc::downgrade(unsafe { &Pin::into_inner_unchecked(self.rc.clone()) }),
    }
  }
}

impl<T: ?Sized> AsRef<T> for UniqueRc<T> {
  fn as_ref(&self) -> &T {
    self.rc.as_ref().get_ref()
  }
}

impl<T: ?Sized> Borrow<T> for UniqueRc<T> {
  fn borrow(&self) -> &T {
    self.rc.borrow()
  }
}

impl<T: ?Sized> Clone for UniqueRc<T> {
  fn clone(&self) -> Self {
    Self {
      rc: self.rc.clone(),
    }
  }
}

impl<T: Debug + ?Sized> Debug for UniqueRc<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    Debug::fmt(&self.rc, f)
  }
}

impl<T: ?Sized> Deref for UniqueRc<T> {
  type Target = T;
  fn deref(&self) -> &Self::Target {
    &self.rc
  }
}

impl<T: Display + ?Sized> Display for UniqueRc<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    Display::fmt(&self.rc, f)
  }
}

impl<T> From<Pin<Rc<T>>> for UniqueRc<T> {
  fn from(rc: Pin<Rc<T>>) -> Self {
    Self { rc }
  }
}

impl<T: ?Sized> Hash for UniqueRc<T> {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    state.write_usize(self.raw_pointer_usize())
  }
}

impl<T: ?Sized> PartialEq for UniqueRc<T> {
  fn eq(&self, other: &Self) -> bool {
    std::ptr::eq(self.raw_pointer(), other.raw_pointer())
  }
}

impl<T: ?Sized> Eq for UniqueRc<T> {}

impl<T: ?Sized> PartialOrd for UniqueRc<T> {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self.raw_pointer().partial_cmp(&other.raw_pointer())
  }
}

impl<T: ?Sized> Ord for UniqueRc<T> {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.raw_pointer().cmp(&other.raw_pointer())
  }
}

impl<T: ?Sized> Pointer for UniqueRc<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    Pointer::fmt(&self.rc, f)
  }
}
