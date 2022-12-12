#version 430 core

out vec4 colour;

in vec2 TexCoords;

uniform vec4 u_Colour;
uniform sampler2D tex;

float kernel[5][5] = 
{
	{ 0.0,  0.25, 1.0,  0.25, 0.0  },
	{ 0.25, 1.0,  1.0,  1.0,  0.25 },
	{ 1.0,  1.0,  1.0,  1.0,  1.0  },
	{ 0.25, 1.0,  1.0,  1.0,  0.25 },
	{ 0.0,  0.25, 1.0,  0.25, 0.0  }
};
	
void main()
{   
	colour = u_Colour * texture(tex, TexCoords).r * kernel[0][0];

    for (int x = 0; x < 5; x++) {
        for (int y = 0; y < 5; y++) {
            vec2 coord = TexCoords + vec2(x, y ) / vec2(textureSize(tex,0));

            colour += u_Colour * texture(tex, coord).r * kernel[x][y];
        }
    }

	//colour = vec4(texture(tex, TexCoords).r, 0.0,0.0,1.0);

}