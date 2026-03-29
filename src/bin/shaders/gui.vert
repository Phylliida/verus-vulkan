#version 450

layout(push_constant) uniform Quad {
    float x, y, w, h;
    float r, g, b, a;
} quad;

void main() {
    //  6 vertices = 2 triangles forming a quad
    //  Triangle 1: (0,0), (1,0), (0,1)
    //  Triangle 2: (1,0), (1,1), (0,1)
    vec2 offsets[6] = vec2[](
        vec2(0.0, 0.0), vec2(1.0, 0.0), vec2(0.0, 1.0),
        vec2(1.0, 0.0), vec2(1.0, 1.0), vec2(0.0, 1.0)
    );

    vec2 off = offsets[gl_VertexIndex];
    float px = quad.x + off.x * quad.w;
    float py = quad.y + off.y * quad.h;

    gl_Position = vec4(px, py, 0.0, 1.0);
}
