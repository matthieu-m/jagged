//! A simple snapshot publisher example.
//!
//! In this example, there are two threads:
//! -   A Producer thread will intermittently add a new item to the Vector.
//! -   A Consumer thread will intermittently receive a Snapshot of the Vector.
//!
//! When the Consumer thread receives a Snapshot of the Vector, it compares it
//! with the current snapshot it has, if any, and prints the new items that
//! were not present in the snapshot it had.

extern crate crossbeam_utils;
extern crate jagged;

use std::sync::mpsc;
use std::{thread, time};

use jagged::vector::{Vector, VectorSnapshot};

fn main() {
    const NUMBER_ELEMENTS: usize = 10;
    const PACE_TIME: time::Duration = time::Duration::from_millis(100);

    let vec: Vector<_> = Vector::new();

    crossbeam_utils::thread::scope(|scope| {
        let (sender, receiver) = mpsc::channel::<VectorSnapshot<'_, _>>();

        //  Consumer
        scope.spawn(move |_| {
            let mut current: Option<VectorSnapshot<'_, _>> = None;

            while let Ok(new) = receiver.recv() {
                let previous = current.map(|v| v.len()).unwrap_or(0);
                for i in previous..new.len() {
                    println!("Consumer saw new item {}: {}", i, new[i]);
                }
                current = Some(new);
            }

            let current = current
                .expect("Should have received at least one snapshot");

            println!("Consumer final snapshot: {:?}", current);

            assert_eq!(NUMBER_ELEMENTS, current.len());
        });

        //  Producer
        for i in 0..NUMBER_ELEMENTS {
            let value = format!("{}th value", i);
            vec.push(value);

            sender.send(vec.snapshot()).unwrap();

            thread::sleep(PACE_TIME);
        }
    }).unwrap();
}
