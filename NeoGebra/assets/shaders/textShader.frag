#version 400 core

layout (location = 0) out vec4 colour;

uniform sampler2D u_TextImage;
uniform vec4 u_Colour;
in vec2 pixelPos;

void main()
{
    vec4 col = texture(u_TextImage, pixelPos);
    colour = vec4(u_Colour.xyz, u_Colour.w * col.w);
}