//! Trait and wrapper for working with C defined FAM structures.
//!
//! In C 99 an array of unknown size may appear within a struct definition as the last member
//! (as long as there is at least one other named member).
//! This is known as a flexible array member (FAM).
//! Pre C99, the same behavior could be achieved using zero length arrays.
//!
//! Flexible Array Members are the go-to choice for working with large amounts of data
//! prefixed by header values.
//!
//! For example the KVM API has many structures of this kind.

use std::mem::{self, size_of};

/// Errors associated with the [`FamStructWrapper`](struct.FamStructWrapper.html) struct.
#[derive(Clone, Debug)]
pub enum Error {
    /// The max size has been exceeded
    SizeLimitExceeded,
}

/// Trait for accessing properties of C defined FAM structures.
///
/// This is unsafe due to the number of constraints that aren't checked:
/// * the implementer should be a POD
/// * the implementor should contain a flexible array member of elements of type `Entry`
/// * `Entry` should be a POD
///
/// Violating these may cause problems.
///
/// # Example
///
/// ```
/// use vmm_sys_util::fam::*;
///
/// #[repr(C)]
/// #[derive(Default)]
/// pub struct __IncompleteArrayField<T>(::std::marker::PhantomData<T>, [T; 0]);
/// impl<T> __IncompleteArrayField<T> {
///     #[inline]
///     pub fn new() -> Self {
///         __IncompleteArrayField(::std::marker::PhantomData, [])
///     }
///     #[inline]
///     pub unsafe fn as_ptr(&self) -> *const T {
///         ::std::mem::transmute(self)
///     }
///     #[inline]
///     pub unsafe fn as_mut_ptr(&mut self) -> *mut T {
///         ::std::mem::transmute(self)
///     }
///     #[inline]
///     pub unsafe fn as_slice(&self, len: usize) -> &[T] {
///         ::std::slice::from_raw_parts(self.as_ptr(), len)
///     }
///     #[inline]
///     pub unsafe fn as_mut_slice(&mut self, len: usize) -> &mut [T] {
///         ::std::slice::from_raw_parts_mut(self.as_mut_ptr(), len)
///     }
/// }
///
/// #[repr(C)]
/// #[derive(Default)]
/// struct MockFamStruct {
///     pub len: u32,
///     pub padding: u32,
///     pub entries: __IncompleteArrayField<u32>,
/// }
///
/// unsafe impl FamStruct for MockFamStruct {
///     type Entry = u32;
///
///     fn len(&self) -> usize {
///         self.len as usize
///     }
///
///     fn set_len(&mut self, len: usize) {
///         self.len = len as u32
///     }
///
///     fn max_len() -> usize {
///         100
///     }
///
///     fn as_slice(&self) -> &[u32] {
///         let len = self.len();
///         unsafe { self.entries.as_slice(len) }
///     }
///
///     fn as_mut_slice(&mut self) -> &mut [u32] {
///         let len = self.len();
///         unsafe { self.entries.as_mut_slice(len) }
///     }
/// }
///
/// type MockFamStructWrapper = FamStructWrapper<MockFamStruct>;
/// ```
///
#[allow(clippy::len_without_is_empty)]
pub unsafe trait FamStruct {
    /// The type of the FAM entries
    type Entry: PartialEq + Copy;

    /// Get the FAM length
    ///
    /// These type of structures contain a member that holds the FAM length.
    /// This method will return the value of that member.
    fn len(&self) -> usize;

    /// Set the FAM length
    ///
    /// These type of structures contain a member that holds the FAM length.
    /// This method will set the value of that member.
    fn set_len(&mut self, len: usize);

    /// Get max allowed FAM length
    ///
    /// This depends on each structure.
    /// For example a structure representing the cpuid can contain at most 80 entries.
    fn max_len() -> usize;

    /// Get the FAM entries as slice
    fn as_slice(&self) -> &[Self::Entry];

    /// Get the FAM entries as mut slice
    fn as_mut_slice(&mut self) -> &mut [Self::Entry];
}

/// A wrapper for [`FamStruct`](trait.FamStruct.html).
///
/// It helps in treating a [`FamStruct`](trait.FamStruct.html) similarly to an actual `Vec`.
pub struct FamStructWrapper<T: Default + FamStruct> {
    // This variable holds the FamStruct structure. We use a `Vec<T>` to make the allocation
    // large enough while still being aligned for `T`. Only the first element of `Vec<T>`
    // will actually be used as a `T`. The remaining memory in the `Vec<T>` is for `entries`,
    // which must be contiguous. Since the entries are of type `FamStruct::Entry` we must
    // be careful to convert the desired capacity of the `FamStructWrapper`
    // from `FamStruct::Entry` to `T` when reserving or releasing memory.
    mem_allocator: Vec<T>,
}

impl<T: Default + FamStruct> FamStructWrapper<T> {
    /// Convert FAM len to `mem_allocator` len.
    ///
    /// Get the capacity required by mem_allocator in order to hold
    /// the provided number of [`FamStruct::Entry`](trait.FamStruct.html#associatedtype.Entry).
    fn mem_allocator_len(fam_len: usize) -> usize {
        let wrapper_size_in_bytes = size_of::<T>() + fam_len * size_of::<T::Entry>();
        (wrapper_size_in_bytes + size_of::<T>() - 1) / size_of::<T>()
    }

    /// Convert `mem_allocator` len to FAM len.
    ///
    /// Get the number of elements of type
    /// [`FamStruct::Entry`](trait.FamStruct.html#associatedtype.Entry)
    /// that fit in a mem_allocator of provided len.
    fn fam_len(mem_allocator_len: usize) -> usize {
        if mem_allocator_len == 0 {
            return 0;
        }

        let array_size_in_bytes = (mem_allocator_len - 1) * size_of::<T>();
        array_size_in_bytes / size_of::<T::Entry>()
    }

    /// Create a new FamStructWrapper with `num_elements` elements.
    ///
    /// The elements will be zero-initialized. The type of the elements will be
    /// [`FamStruct::Entry`](trait.FamStruct.html#associatedtype.Entry).
    ///
    /// # Arguments
    ///
    /// * `num_elements` - The number of elements in the FamStructWrapper.
    pub fn new(num_elements: usize) -> FamStructWrapper<T> {
        let required_mem_allocator_capacity =
            FamStructWrapper::<T>::mem_allocator_len(num_elements);

        let mut mem_allocator = Vec::with_capacity(required_mem_allocator_capacity);
        mem_allocator.push(T::default());
        for _ in 1..required_mem_allocator_capacity {
            mem_allocator.push(unsafe { mem::zeroed() })
        }
        mem_allocator[0].set_len(num_elements);

        FamStructWrapper { mem_allocator }
    }

    /// Create a new FamStructWrapper from a slice of elements.
    ///
    /// # Arguments
    ///
    /// * `entries` - The slice of [`FamStruct::Entry`](trait.FamStruct.html#associatedtype.Entry)
    ///               entries.
    pub fn from_entries(entries: &[T::Entry]) -> FamStructWrapper<T> {
        let mut adapter = FamStructWrapper::<T>::new(entries.len());

        {
            let wrapper_entries = adapter.as_mut_fam_struct().as_mut_slice();
            wrapper_entries.copy_from_slice(entries);
        }

        adapter
    }

    /// Create a new FamStructWrapper from the raw content represented as `Vec<T>`.
    ///
    /// Sometimes we already have the raw content of an FAM struct represented as `Vec<T>`,
    /// and want to use the FamStructWrapper as accessors.
    ///
    /// This function is unsafe because the caller needs to ensure that the raw content is correctly
    /// layed out.
    ///
    /// # Arguments
    ///
    /// * `content` - The raw content represented as `Vec[T]`.
    pub unsafe fn from_raw(content: Vec<T>) -> Self {
        FamStructWrapper {
            mem_allocator: content,
        }
    }

    /// Consume the FamStructWrapper and return the raw content as `Vec<T>`.
    pub fn into_raw(self) -> Vec<T> {
        self.mem_allocator
    }

    /// Get a reference to the actual [`FamStruct`](trait.FamStruct.html) instance.
    pub fn as_fam_struct_ref(&self) -> &T {
        &self.mem_allocator[0]
    }

    /// Get a mut reference to the actual [`FamStruct`](trait.FamStruct.html) instance.
    pub fn as_mut_fam_struct(&mut self) -> &mut T {
        &mut self.mem_allocator[0]
    }

    /// Get a pointer to the [`FamStruct`](trait.FamStruct.html) instance.
    ///
    /// The caller must ensure that the fam_struct outlives the pointer this
    /// function returns, or else it will end up pointing to garbage.
    ///
    /// Modifying the container referenced by this pointer may cause its buffer
    /// to be reallocated, which would also make any pointers to it invalid.
    pub fn as_fam_struct_ptr(&self) -> *const T {
        self.as_fam_struct_ref()
    }

    /// Get a mutable pointer to the [`FamStruct`](trait.FamStruct.html) instance.
    ///
    /// The caller must ensure that the fam_struct outlives the pointer this
    /// function returns, or else it will end up pointing to garbage.
    ///
    /// Modifying the container referenced by this pointer may cause its buffer
    /// to be reallocated, which would also make any pointers to it invalid.
    pub fn as_mut_fam_struct_ptr(&mut self) -> *mut T {
        self.as_mut_fam_struct()
    }

    /// Get the elements slice.
    pub fn as_slice(&self) -> &[T::Entry] {
        self.as_fam_struct_ref().as_slice()
    }

    /// Get the mutable elements slice.
    pub fn as_mut_slice(&mut self) -> &mut [T::Entry] {
        self.as_mut_fam_struct().as_mut_slice()
    }

    /// Get the number of elements of type `FamStruct::Entry` currently in the vec.
    fn len(&self) -> usize {
        self.as_fam_struct_ref().len()
    }

    /// Get the capacity of the `FamStructWrapper`
    ///
    /// The capacity is measured in elements of type `FamStruct::Entry`.
    fn capacity(&self) -> usize {
        FamStructWrapper::<T>::fam_len(self.mem_allocator.capacity())
    }

    /// Reserve additional capacity.
    ///
    /// Reserve capacity for at least `additional` more
    /// [`FamStruct::Entry`](trait.FamStruct.html#associatedtype.Entry) elements.
    ///
    /// If the capacity is already reserved, this method doesn't do anything.
    /// If not this will trigger a reallocation of the underlying buffer.
    fn reserve(&mut self, additional: usize) {
        let desired_capacity = self.len() + additional;
        if desired_capacity <= self.capacity() {
            return;
        }

        let current_mem_allocator_len = self.mem_allocator.len();
        let required_mem_allocator_len = FamStructWrapper::<T>::mem_allocator_len(desired_capacity);
        let additional_mem_allocator_len = required_mem_allocator_len - current_mem_allocator_len;

        self.mem_allocator.reserve(additional_mem_allocator_len);
    }

    /// Update the length of the FamStructWrapper.
    ///
    /// The length of `self` will be updated to the specified value.
    /// The length of the `T` structure and of `self.mem_allocator` will be updated accordingly.
    /// If the len is increased additional capacity will be reserved.
    /// If the len is decreased the unnecessary memory will be deallocated.
    ///
    /// This method might trigger reallocations of the underlying buffer.
    ///
    /// # Errors
    ///
    /// When len is greater than the max possible len it returns Error::SizeLimitExceeded.
    fn set_len(&mut self, len: usize) -> Result<(), Error> {
        let additional_elements: isize = len as isize - self.len() as isize;
        // If len == self.len there's nothing to do.
        if additional_elements == 0 {
            return Ok(());
        }

        // If the len needs to be increased:
        if additional_elements > 0 {
            // Check if the new len is valid.
            if len > T::max_len() {
                return Err(Error::SizeLimitExceeded);
            }
            // Reserve additional capacity.
            self.reserve(additional_elements as usize);
        }

        let current_mem_allocator_len = self.mem_allocator.len();
        let required_mem_allocator_len = FamStructWrapper::<T>::mem_allocator_len(len);
        // Update the len of the `mem_allocator`.
        // This is safe since enough capacity has been reserved.
        unsafe {
            self.mem_allocator.set_len(required_mem_allocator_len);
        }
        // Zero-initialize the additional elements if any.
        for i in current_mem_allocator_len..required_mem_allocator_len {
            self.mem_allocator[i] = unsafe { mem::zeroed() }
        }
        // Update the len of the underlying `FamStruct`.
        self.as_mut_fam_struct().set_len(len);

        // If the len needs to be decreased, deallocate unnecessary memory
        if additional_elements < 0 {
            self.mem_allocator.shrink_to_fit();
        }

        Ok(())
    }

    /// Append an element.
    ///
    /// # Arguments
    ///
    /// * `entry` - The element that will be appended to the end of the collection.
    ///
    /// # Errors
    ///
    /// When len is already equal to max possible len it returns Error::SizeLimitExceeded.
    pub fn push(&mut self, entry: T::Entry) -> Result<(), Error> {
        let new_len = self.len() + 1;
        self.set_len(new_len)?;
        self.as_mut_slice()[new_len - 1] = entry;

        Ok(())
    }

    /// Retain only the elements specified by the predicate.
    ///
    /// # Arguments
    ///
    /// * `f` - The function used to evaluate whether an entry will be kept or not.
    ///         When `f` returns `true` the entry is kept.
    pub fn retain<P>(&mut self, mut f: P)
    where
        P: FnMut(&T::Entry) -> bool,
    {
        let mut num_kept_entries = 0;
        {
            let entries = self.as_mut_slice();
            for entry_idx in 0..entries.len() {
                let keep = f(&entries[entry_idx]);
                if keep {
                    entries[num_kept_entries] = entries[entry_idx];
                    num_kept_entries += 1;
                }
            }
        }

        // This is safe since this method is not increasing the len
        self.set_len(num_kept_entries).expect("invalid length");
    }
}

impl<T: Default + FamStruct> PartialEq for FamStructWrapper<T> {
    fn eq(&self, other: &FamStructWrapper<T>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: Default + FamStruct> Clone for FamStructWrapper<T> {
    fn clone(&self) -> Self {
        FamStructWrapper::from_entries(self.as_slice())
    }
}

impl<T: Default + FamStruct> From<Vec<T>> for FamStructWrapper<T> {
    fn from(vec: Vec<T>) -> Self {
        FamStructWrapper { mem_allocator: vec }
    }
}

/// Generate `FamStruct` implementation for structs with flexible array member.
#[macro_export]
macro_rules! generate_fam_struct_impl {
    ($struct_type: ty, $entry_type: ty, $entries_name: ident,
     $field_type: ty, $field_name: ident, $max: expr) => {
        unsafe impl FamStruct for $struct_type {
            type Entry = $entry_type;

            fn len(&self) -> usize {
                self.$field_name as usize
            }

            fn set_len(&mut self, len: usize) {
                self.$field_name = len as $field_type;
            }

            fn max_len() -> usize {
                $max
            }

            fn as_slice(&self) -> &[<Self as FamStruct>::Entry] {
                let len = self.len();
                unsafe { self.$entries_name.as_slice(len) }
            }

            fn as_mut_slice(&mut self) -> &mut [<Self as FamStruct>::Entry] {
                let len = self.len();
                unsafe { self.$entries_name.as_mut_slice(len) }
            }
        }
    };
}
pub(crate) use generate_fam_struct_impl;