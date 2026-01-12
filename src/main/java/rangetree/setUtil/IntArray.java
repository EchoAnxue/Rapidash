package rangetree.setUtil;


import java.util.Arrays;
import java.util.Iterator;
import java.util.NoSuchElementException;

public class IntArray implements Iterable<Integer>, Cloneable {

    private int[] data;
    private int size;

    private static final int DEFAULT_CAPACITY = 8;

    public IntArray() {
        this.data = new int[DEFAULT_CAPACITY];
        this.size = 0;
    }

    public IntArray(int capacity) {
        this.data = new int[Math.max(capacity, DEFAULT_CAPACITY)];
        this.size = 0;
    }

    // ---------- core ops ----------

    public void add(int value) {
        if (size == data.length) {
            grow();
        }
        data[size++] = value;
    }

    public int get(int index) {
        if (index >= size) {
            throw new IndexOutOfBoundsException();
        }
        return data[index];
    }

    public int size() {
        return size;
    }

    public boolean isEmpty() {
        return size == 0;
    }

    public void clear() {
        size = 0; // no need to clear array
    }

    // ---------- internal ----------

    private void grow() {
        int newCap = data.length * 2;
        if (newCap == 0) newCap = 1;
        data = Arrays.copyOf(data, newCap);
    }


    // ---------- clone ----------

    @Override
    public IntArray clone() {
        try {
            IntArray copy = (IntArray) super.clone();
//            保证不压缩size，复制 length
            copy.data = Arrays.copyOf(this.data, this.data.length);
            copy.size = this.size;
            return copy;
        } catch (CloneNotSupportedException e) {
            throw new AssertionError(e);
        }
    }

    // ---------- iteration ----------

    @Override
    public Iterator<Integer> iterator() {
        return new Iterator<Integer>() {
            private int cursor = 0;

            @Override
            public boolean hasNext() {
                return cursor < size;
            }

            @Override
            public Integer next() {
                if (cursor >= size) {
                    throw new NoSuchElementException();
                }
                return data[cursor++]; // auto-box only here
            }
        };
    }
}
