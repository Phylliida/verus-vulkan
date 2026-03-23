#version 450

layout(push_constant) uniform Quad {
    float x, y, w, h;
    float r, g, b, a;
} quad;

layout(location = 0) out vec4 outColor;

void main() {
    outColor = vec4(quad.r, quad.g, quad.b, quad.a);
}
