By default, the global generator reads the node configuration from the
`SCRU64_NODE_SPEC` environment variable when a generator method is first called,
and it panics if it fails to do so. The node configuration is encoded in a node
spec string consisting of `node_id` and `node_id_size` integers separated by a
slash (e.g., "42/8", "0xb00/12"; see [`NodeSpec`](crate::generator::NodeSpec)
for details). You can configure the global generator differently by calling
[`GlobalGenerator::initialize`](crate::generator::GlobalGenerator::initialize)
before the default initializer is triggered.
