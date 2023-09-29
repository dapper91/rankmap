pub(crate) fn sift_down<T, C>(heap: &mut Vec<T>, idx: usize, mut swap_callback: C)
where
    T: PartialOrd + Clone,
    C: FnMut(usize, &T),
{
    debug_assert!(idx < heap.len());

    let mut current_idx = idx;
    let current = heap[current_idx].clone();

    while current_idx > 0 {
        let parent_idx = (current_idx - 1) / 2;
        let parent = heap[parent_idx].clone();
        if current < parent {
            heap[current_idx] = parent.clone();
            swap_callback(current_idx, &parent);
            current_idx = parent_idx;
        } else {
            break;
        }
    }

    heap[current_idx] = current.clone();
    swap_callback(current_idx, &current);
}

pub(crate) fn sift_up<T, C>(heap: &mut Vec<T>, idx: usize, end: usize, mut swap_callback: C)
where
    T: PartialOrd + Clone,
    C: FnMut(usize, &T),
{
    debug_assert!(idx < heap.len());
    debug_assert!(end <= heap.len());

    let mut current_idx = idx;
    let current = heap[current_idx].clone();

    let mut left_child_idx = current_idx.saturating_mul(2).saturating_add(1);
    while left_child_idx < end {
        let right_child_idx = left_child_idx.saturating_add(1);
        let min_child_idx = if right_child_idx >= end || heap[left_child_idx] < heap[right_child_idx] {
            left_child_idx
        } else {
            right_child_idx
        };

        let child = heap[min_child_idx].clone();
        if current <= child {
            break;
        }

        heap[current_idx] = child.clone();
        swap_callback(current_idx, &child);

        current_idx = min_child_idx;
        left_child_idx = current_idx.saturating_mul(2).saturating_add(1);
    }

    heap[current_idx] = current.clone();
    swap_callback(current_idx, &current);
}

pub(crate) fn into_sorted_vec<T>(heap: &Vec<T>) -> Vec<T>
where
    T: PartialOrd + Clone,
{
    let mut heap = (*heap).clone();

    for end in heap.len()..0 {
        heap.swap(0, end - 1);
        sift_up(&mut heap, 0, end, |_, _| {});
    }

    return heap;
}

#[cfg(test)]
mod test {
    use rstest::*;
    use std::iter::zip;

    use super::{into_sorted_vec, sift_down, sift_up};

    #[rstest]
    #[case(
        vec![
                1,
             2,    3,
            4, 5, 6, 0,
        ],
        vec![
                0,
             2,    1,
            4, 5, 6, 3,
        ],
        6,
        vec![6, 2, 0],
    )]
    #[case(
        vec![
                1,
             2,    3,
            0, 5, 6, 7,
        ],
        vec![
                0,
             1,    3,
            2, 5, 6, 7,
        ],
        3,
        vec![3, 1, 0],
    )]
    #[case(
        vec![
                1,
             2,    3,
            4, 5, 2, 7,
        ],
        vec![
                1,
             2,    2,
            4, 5, 3, 7,
        ],
        5,
        vec![5, 2],
    )]
    #[case(
        vec![
                1,
             2,    3,
            4, 1, 6, 7,
        ],
        vec![
                1,
             1,    3,
            4, 2, 6, 7,
        ],
        4,
        vec![4, 1],
    )]
    #[case(
        vec![
                1,
             2,    3,
            4, 5, 6, 7,
        ],
        vec![
                1,
             2,    3,
            4, 5, 6, 7,
        ],
        6,
        vec![6],
    )]
    #[case(
        vec![1],
        vec![1],
        0,
        vec![0],
    )]
    fn test_sift_down(
        #[case] mut input: Vec<i32>,
        #[case] output: Vec<i32>,
        #[case] index: usize,
        #[case] swaps: Vec<usize>,
    ) {
        let mut actual_swaps = Vec::new();
        sift_down(&mut input, index, |idx, _| actual_swaps.push(idx));
        assert_eq!(input, output);
        assert_eq!(actual_swaps, swaps)
    }

    #[rstest]
    #[case(
        vec![
                4,
             2,    3,
            4, 5, 6, 7,
        ],
        vec![
                2,
             4,    3,
            4, 5, 6, 7,
        ],
        0,
        vec![0, 1],
    )]
    #[case(
        vec![
                6,
             2,    3,
            4, 5, 6, 7,
        ],
        vec![
                2,
             4,    3,
            6, 5, 6, 7,
        ],
        0,
        vec![0, 1, 3],
    )]
    #[case(
        vec![
                8,
             3,    2,
            4, 5, 7, 6,
        ],
        vec![
                2,
             3,    6,
            4, 5, 7, 8,
        ],
        0,
        vec![0, 2, 6],
    )]
    #[case(
        vec![1],
        vec![1],
        0,
        vec![0],
    )]
    fn test_sift_up(
        #[case] mut input: Vec<i32>,
        #[case] output: Vec<i32>,
        #[case] index: usize,
        #[case] swaps: Vec<usize>,
    ) {
        let mut actual_swaps = Vec::new();
        let end = input.len();
        sift_up(&mut input, index, end, |idx, _| actual_swaps.push(idx));
        assert_eq!(input, output);
        assert_eq!(actual_swaps, swaps)
    }

    #[rstest]
    #[case(
        vec![
                1,
             2,    3,
            4, 5, 6, 7,
        ],
    )]
    #[case(
        vec![
                1,
             3,    2,
            4, 5, 7,
        ],
    )]
    #[case(
        vec![
             1,
            3, 2,
        ],
    )]
    #[case(
        vec![1],
    )]
    #[case(
        vec![0],
    )]
    #[case(
        vec![],
    )]
    fn test_into_sorted_vec(#[case] input: Vec<i32>) {
        fn is_sorted<T: PartialOrd>(vec: &Vec<T>) -> bool {
            for (cur, nxt) in zip(vec.iter(), vec.iter().nth(1)) {
                if cur > nxt {
                    return false;
                }
            }

            return true;
        }
        let result = into_sorted_vec(&input);
        assert_eq!(result.len(), input.len());
        assert!(is_sorted(&input));
    }
}
