#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

constexpr int kMaxKeys = 48;
constexpr int kMinKeys = kMaxKeys / 2;
constexpr int kNodeCapacity = 13200;
constexpr char kDataFile[] = "bpt_storage.bin";
constexpr char kTempFile[] = "bpt_storage.bin.tmp";

struct Key {
  char index[65]{};
  std::int32_t value = 0;
};

int compare(const Key &a, const Key &b) {
  const int index_result = std::strcmp(a.index, b.index);
  if (index_result != 0) return index_result;
  if (a.value < b.value) return -1;
  if (a.value > b.value) return 1;
  return 0;
}

struct Node {
  std::uint8_t leaf = 1;
  std::uint8_t unused[3]{};
  std::int32_t count = 0;
  std::int32_t next = -1;
  Key keys[kMaxKeys + 1]{};
  std::int32_t children[kMaxKeys + 2]{};
};

struct FileHeader {
  char magic[8]{};
  std::uint32_t version = 1;
  std::uint32_t node_size = sizeof(Node);
  std::int32_t root = 0;
  std::int32_t free_head = -1;
  std::uint64_t node_count = 0;
};

class BPlusTree {
 public:
  BPlusTree() { load(); }
  ~BPlusTree() {
    try {
      save();
    } catch (...) {
    }
  }

  void insert(const Key &key) {
    const int right = insert_recursive(root_, key);
    if (right != -1) {
      const int old_root = root_;
      root_ = allocate(false);
      nodes_[root_].count = 1;
      nodes_[root_].children[0] = old_root;
      nodes_[root_].children[1] = right;
      refresh(root_);
    }
  }

  void erase(const Key &key) {
    erase_recursive(root_, key);
    if (!nodes_[root_].leaf && nodes_[root_].count == 0) {
      const int old_root = root_;
      root_ = nodes_[old_root].children[0];
      release(old_root);
    }
  }

  void find(const std::string &index, std::ostream &out) const {
    Key target = make_key(index, std::numeric_limits<std::int32_t>::min());
    int node_id = root_;
    while (!nodes_[node_id].leaf) {
      const Node &node = nodes_[node_id];
      node_id = node.children[upper_bound(node, target)];
    }

    bool found = false;
    int position = lower_bound(nodes_[node_id], target);
    while (node_id != -1) {
      const Node &node = nodes_[node_id];
      for (; position < node.count; ++position) {
        const int index_result = std::strcmp(node.keys[position].index, index.c_str());
        if (index_result > 0) {
          if (!found) out << "null";
          out << '\n';
          return;
        }
        if (index_result == 0) {
          if (found) out << ' ';
          out << node.keys[position].value;
          found = true;
        }
      }
      node_id = node.next;
      position = 0;
    }
    if (!found) out << "null";
    out << '\n';
  }

  static Key make_key(const std::string &index, std::int32_t value) {
    Key key;
    std::memcpy(key.index, index.data(), index.size());
    key.index[index.size()] = '\0';
    key.value = value;
    return key;
  }

 private:
  std::vector<Node> nodes_;
  int root_ = 0;
  int free_head_ = -1;

  static int lower_bound(const Node &node, const Key &key) {
    int low = 0, high = node.count;
    while (low < high) {
      const int mid = (low + high) / 2;
      if (compare(node.keys[mid], key) < 0)
        low = mid + 1;
      else
        high = mid;
    }
    return low;
  }

  static int upper_bound(const Node &node, const Key &key) {
    int low = 0, high = node.count;
    while (low < high) {
      const int mid = (low + high) / 2;
      if (compare(key, node.keys[mid]) >= 0)
        low = mid + 1;
      else
        high = mid;
    }
    return low;
  }

  int allocate(bool leaf) {
    int id;
    if (free_head_ != -1) {
      id = free_head_;
      free_head_ = nodes_[id].next;
      nodes_[id] = Node{};
    } else {
      id = static_cast<int>(nodes_.size());
      nodes_.push_back(Node{});
    }
    nodes_[id].leaf = leaf;
    nodes_[id].next = -1;
    return id;
  }

  void release(int id) {
    nodes_[id] = Node{};
    nodes_[id].next = free_head_;
    free_head_ = id;
  }

  Key minimum_key(int id) const {
    while (!nodes_[id].leaf) id = nodes_[id].children[0];
    return nodes_[id].keys[0];
  }

  void refresh(int id) {
    Node &node = nodes_[id];
    if (node.leaf) return;
    for (int i = 0; i < node.count; ++i) {
      node.keys[i] = minimum_key(node.children[i + 1]);
    }
  }

  int insert_recursive(int id, const Key &key) {
    Node &node = nodes_[id];
    if (node.leaf) {
      const int position = lower_bound(node, key);
      if (position < node.count && compare(node.keys[position], key) == 0) return -1;
      for (int i = node.count; i > position; --i) node.keys[i] = node.keys[i - 1];
      node.keys[position] = key;
      ++node.count;
      if (node.count <= kMaxKeys) return -1;

      const int right_id = allocate(true);
      Node &left = nodes_[id];
      Node &right = nodes_[right_id];
      const int left_count = left.count / 2;
      right.count = left.count - left_count;
      for (int i = 0; i < right.count; ++i) right.keys[i] = left.keys[left_count + i];
      left.count = left_count;
      right.next = left.next;
      left.next = right_id;
      return right_id;
    }

    const int child_position = upper_bound(node, key);
    const int right_child = insert_recursive(node.children[child_position], key);
    Node &current = nodes_[id];
    if (right_child != -1) {
      for (int i = current.count + 1; i > child_position + 1; --i)
        current.children[i] = current.children[i - 1];
      current.children[child_position + 1] = right_child;
      ++current.count;
    }
    refresh(id);
    if (current.count <= kMaxKeys) return -1;

    const int right_id = allocate(false);
    Node &left = nodes_[id];
    Node &right = nodes_[right_id];
    const int total_children = left.count + 1;
    const int left_children = total_children / 2;
    const int right_children = total_children - left_children;
    for (int i = 0; i < right_children; ++i)
      right.children[i] = left.children[left_children + i];
    left.count = left_children - 1;
    right.count = right_children - 1;
    refresh(id);
    refresh(right_id);
    return right_id;
  }

  bool erase_recursive(int id, const Key &key) {
    Node &node = nodes_[id];
    if (node.leaf) {
      const int position = lower_bound(node, key);
      if (position == node.count || compare(node.keys[position], key) != 0) return false;
      for (int i = position; i + 1 < node.count; ++i) node.keys[i] = node.keys[i + 1];
      --node.count;
      return true;
    }

    const int child_position = upper_bound(node, key);
    if (!erase_recursive(node.children[child_position], key)) return false;
    rebalance_child(id, child_position);
    refresh(id);
    return true;
  }

  void rebalance_child(int parent_id, int position) {
    Node &parent = nodes_[parent_id];
    int child_id = parent.children[position];
    if (nodes_[child_id].count >= kMinKeys) return;

    if (position > 0) {
      const int left_id = parent.children[position - 1];
      if (nodes_[left_id].count > kMinKeys) {
        borrow_from_left(left_id, child_id);
        return;
      }
    }
    if (position < parent.count) {
      const int right_id = parent.children[position + 1];
      if (nodes_[right_id].count > kMinKeys) {
        borrow_from_right(child_id, right_id);
        return;
      }
    }

    if (position > 0) {
      merge_nodes(parent.children[position - 1], child_id);
      remove_child(parent_id, position);
    } else {
      merge_nodes(child_id, parent.children[1]);
      remove_child(parent_id, 1);
    }
  }

  void borrow_from_left(int left_id, int child_id) {
    Node &left = nodes_[left_id];
    Node &child = nodes_[child_id];
    if (child.leaf) {
      for (int i = child.count; i > 0; --i) child.keys[i] = child.keys[i - 1];
      child.keys[0] = left.keys[left.count - 1];
    } else {
      for (int i = child.count + 1; i > 0; --i) child.children[i] = child.children[i - 1];
      child.children[0] = left.children[left.count];
    }
    --left.count;
    ++child.count;
    refresh(left_id);
    refresh(child_id);
  }

  void borrow_from_right(int child_id, int right_id) {
    Node &child = nodes_[child_id];
    Node &right = nodes_[right_id];
    if (child.leaf) {
      child.keys[child.count] = right.keys[0];
      for (int i = 0; i + 1 < right.count; ++i) right.keys[i] = right.keys[i + 1];
    } else {
      child.children[child.count + 1] = right.children[0];
      for (int i = 0; i < right.count; ++i) right.children[i] = right.children[i + 1];
    }
    ++child.count;
    --right.count;
    refresh(child_id);
    refresh(right_id);
  }

  void merge_nodes(int left_id, int right_id) {
    Node &left = nodes_[left_id];
    Node &right = nodes_[right_id];
    if (left.leaf) {
      for (int i = 0; i < right.count; ++i) left.keys[left.count + i] = right.keys[i];
      left.count += right.count;
      left.next = right.next;
    } else {
      const int left_children = left.count + 1;
      for (int i = 0; i <= right.count; ++i)
        left.children[left_children + i] = right.children[i];
      left.count += right.count + 1;
      refresh(left_id);
    }
    release(right_id);
  }

  void remove_child(int parent_id, int position) {
    Node &parent = nodes_[parent_id];
    for (int i = position; i < parent.count; ++i) parent.children[i] = parent.children[i + 1];
    --parent.count;
  }

  void load() {
    nodes_.reserve(kNodeCapacity);
    std::ifstream input(kDataFile, std::ios::binary);
    FileHeader header;
    if (input && input.read(reinterpret_cast<char *>(&header), sizeof(header)) &&
        std::memcmp(header.magic, "BPT016", 7) == 0 && header.version == 1 &&
        header.node_size == sizeof(Node) && header.node_count > 0) {
      nodes_.resize(header.node_count);
      input.read(reinterpret_cast<char *>(nodes_.data()),
                 static_cast<std::streamsize>(nodes_.size() * sizeof(Node)));
      if (!input) throw std::runtime_error("corrupt B+ tree storage");
      root_ = header.root;
      free_head_ = header.free_head;
      return;
    }
    nodes_.push_back(Node{});
  }

  void save() const {
    std::ofstream output(kTempFile, std::ios::binary | std::ios::trunc);
    if (!output) throw std::runtime_error("cannot create B+ tree storage");
    FileHeader header;
    std::memcpy(header.magic, "BPT016", 7);
    header.root = root_;
    header.free_head = free_head_;
    header.node_count = nodes_.size();
    output.write(reinterpret_cast<const char *>(&header), sizeof(header));
    output.write(reinterpret_cast<const char *>(nodes_.data()),
                 static_cast<std::streamsize>(nodes_.size() * sizeof(Node)));
    output.close();
    if (!output || std::rename(kTempFile, kDataFile) != 0)
      throw std::runtime_error("cannot save B+ tree storage");
  }
};

}  // namespace

int main() {
  std::ios::sync_with_stdio(false);
  std::cin.tie(nullptr);

  int command_count;
  if (!(std::cin >> command_count)) return 0;

  BPlusTree tree;
  std::string command, index;
  std::int32_t value;
  for (int i = 0; i < command_count; ++i) {
    std::cin >> command >> index;
    if (command == "find") {
      tree.find(index, std::cout);
    } else {
      std::cin >> value;
      const Key key = BPlusTree::make_key(index, value);
      if (command == "insert")
        tree.insert(key);
      else
        tree.erase(key);
    }
  }
  return 0;
}
